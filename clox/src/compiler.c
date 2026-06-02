//
//  compiler.c
//  clox
//
//  Created by Matthew Pohlmann on 5/18/18.
//  Copyright © 2018 Matthew Pohlmann. All rights reserved.
//

#include "common.h"
#include "compiler.h"
#include "scanner.h"
#include "debug.h"
#include "object.h"
#include "array.h"

#include <stdio.h>
#include <stdlib.h>



typedef struct Parser
{
	Token current;
	Token previous;

	bool hadError;
	bool panicMode;
} Parser;

typedef enum Precedence
{
	PREC_NONE,
	PREC_ASSIGNMENT,	// =
	PREC_OR,			// or
	PREC_AND,			// and
	PREC_EQUALITY,		// == !=
	PREC_COMPARISON,	// < > <= >=
	PREC_TERM,			// + -
	PREC_FACTOR,		// * /
	PREC_UNARY,			// ! -
	PREC_CALL,			// . ()
	PREC_PRIMARY,
} Precedence;

typedef void (*ParseFn)(bool canAssign);

typedef struct ParseRule
{
	ParseFn prefix;
	ParseFn infix;
	Precedence precedence;
} ParseRule;

typedef struct Local
{
	Token name;
	int depth;
	bool isCaptured;
} Local;

typedef struct Upvalue
{
	uint32_t index;
	bool isLocal;
} Upvalue;

typedef enum FunctionType
{
	TYPE_FUNCTION,
	TYPE_INITIALIZER,
	TYPE_METHOD,
	TYPE_SCRIPT,
} FunctionType;

typedef struct Compiler
{
	struct Compiler * enclosing;
	Scanner * scanner;
	Parser * parser;

	ObjFunction * function;
	FunctionType type;

	// TODO: Optimization. Make lookup faster (currently requires linear search through array)
	// TODO: Enhancement. Add concept of variables that don't allow re-assignment ('let'?)
	Local * locals;
	Upvalue * upvalues;
	int scopeDepth;
} Compiler;

typedef struct ClassCompiler
{
	struct ClassCompiler * enclosing;
	Token name;
	bool hasSuperclass;
} ClassCompiler;

Compiler * current = NULL;
ClassCompiler * currentClass = NULL;


static void advance(void);
static bool check(TokenType type);
static bool match(TokenType type);
static void errorAtCurrent(const char * message);
static void error(const char * message);
static void errorAt(Token * token, const char * message);
static void consume(TokenType type, const char * message);
static void emitByte(uint8_t byte);
static void emitBytes(uint8_t byte1, uint8_t byte2);
static Chunk * currentChunk(void);
static void initCompiler(Compiler * compiler, Scanner * scanner, Parser * parser, FunctionType type);
static ObjFunction * endCompiler(void);
static void destroyCompiler(Compiler * compiler);
static void emitReturn(void);
static void expression(void);
static void statement(void);
static void declaration(void);
static void classDeclaration(void);
static void funDeclaration(void);
static void varDeclaration(void);
static void printStatement(void);
static void returnStatement(void);
static void whileStatement(void);
static void expressionStatement(void);
static void forStatement(void);
static void ifStatement(void);
static void parsePrecedence(Precedence precendece);
static uint32_t identifierConstant(Token * name);
static bool resolveLocal(Compiler * compiler, Token * name, uint32_t * localIndex);
static bool resolveUpvalue(Compiler * compiler, Token * name, uint32_t * upvalueIndex);
static void declareVariable(void);
static uint8_t argumentList(void);
static const ParseRule * getRule(TokenType type);

ObjFunction * compile(const char * source)
{
	Scanner scanner;
	initScanner(&scanner, source);

	Parser parser;
	memset(&parser, 0, sizeof(parser));

	Compiler compiler;
	initCompiler(&compiler, &scanner, &parser, TYPE_SCRIPT);

	advance();

	while (!match(TOKEN_EOF))
	{
		declaration();
	}

	ObjFunction * function = endCompiler();
	destroyCompiler(&compiler);

	return parser.hadError ? NULL : function;
}

static void advance(void)
{
	current->parser->previous = current->parser->current;

	for (;;)
	{
		current->parser->current = scanToken(current->scanner);

		if (current->parser->current.type != TOKEN_ERROR)
			break;

		errorAtCurrent(current->parser->current.start);
	}
}

static void errorAtCurrent(const char * message)
{
	errorAt(&current->parser->current, message);
}

static void error(const char * message)
{
	errorAt(&current->parser->previous, message);
}

static void errorAt(Token * token, const char * message)
{
	if (current->parser->panicMode)
		return;

	current->parser->panicMode = true;

	fprintf(stderr, "[line %d] Error", token->line);

	if (token->type == TOKEN_EOF)
	{
		fprintf(stderr, " at end");
	}
	else if (token->type == TOKEN_ERROR)
	{
		// Nothing.
	}
	else
	{
		fprintf(stderr, " at '%.*s'", token->length, token->start);
	}

	fprintf(stderr, ": %s\n", message);

	current->parser->hadError = true;
}

static void consume(TokenType type, const char * message)
{
	if (current->parser->current.type == type)
	{
		advance();
		return;
	}

	errorAtCurrent(message);
}

static bool check(TokenType type)
{
	return current->parser->current.type == type;
}

static bool match(TokenType type)
{
	if (!check(type)) return false;
	advance();
	return true;
}

static Chunk * currentChunk(void)
{
	return &current->function->chunk;
}

static void synchronize(void)
{
	current->parser->panicMode = false;

	while (current->parser->current.type != TOKEN_EOF)
	{
		if (current->parser->previous.type == TOKEN_SEMICOLON)
			return;

		switch (current->parser->current.type)
		{
		case TOKEN_CLASS:
		case TOKEN_FUN:
		case TOKEN_VAR:
		case TOKEN_FOR:
		case TOKEN_IF:
		case TOKEN_WHILE:
		case TOKEN_PRINT:
		case TOKEN_RETURN:
			return;

		default:
			break;
		}

		advance();
	}
}

static inline void emitByte(uint8_t byte)
{
	writeChunk(currentChunk(), byte, current->parser->previous.line);
}

static inline void emitBytes(uint8_t byte1, uint8_t byte2)
{
	emitByte(byte1);
	emitByte(byte2);
}

static inline void emitU24(uint32_t n)
{
	ASSERT(n <= UINT24_MAX);

	uint8_t b = (n >> (16)) & UINT8_MAX;
	emitByte(b);

	b = (n >> (8)) & UINT8_MAX;
	emitByte(b);

	b = n & UINT8_MAX;
	emitByte(b);
}

static void emitLoop(uint32_t loopStart)
{
	emitByte(OP_LOOP);

	uint32_t offset = ARY_LEN(currentChunk()->aryB) - loopStart + 2;
	if (offset > UINT16_MAX)
	{
		error("Loop body too large.");
	}

	emitByte((offset >> 8) & 0xff);
	emitByte(offset & 0xff);
}

static uint32_t emitJump(uint8_t instruction)
{
	emitByte(instruction);
	emitByte(0xff);
	emitByte(0xff);
	return ARY_LEN(currentChunk()->aryB) - 2;
}

static void emitReturn(void)
{
	if (current->type == TYPE_INITIALIZER)
	{
		emitBytes(OP_GET_LOCAL, 0);
	}
	else
	{
		emitByte(OP_NIL);
	}

	emitByte(OP_RETURN);
}

static uint32_t makeConstant(Value value)
{
	// TODO: De-duplicate equivalent constants added to the chunk

	uint32_t constant = addConstant(currentChunk(), value);

	if (constant > UINT24_MAX)
	{
		error("Too many constants in one chunk.");
		return 0;
	}

	return constant;
}

static void emitConstantHelper(uint32_t constant, OpCode opShort, OpCode opLong)
{
	if (constant <= UINT8_MAX)
	{
		// Use more optimal 1-byte constant op

		emitBytes((uint8_t)opShort, (uint8_t)constant);
	}
	else if (constant <= UINT24_MAX)
	{
		// Use 3-byte constant op

		emitByte((uint8_t)opLong);
		emitU24(constant);
	}
	else
	{
		ASSERT(false);
	}
}

static void emitConstant(Value value)
{
	uint32_t constant = makeConstant(value);
	emitConstantHelper(constant, OP_CONSTANT, OP_CONSTANT_LONG);
}

static void patchJump(uint32_t offset)
{
	// -2 to adjust for the bytecode for the jump offset itself

	uint32_t jump = ARY_LEN(currentChunk()->aryB) - offset - 2;

	if (jump > UINT16_MAX)
	{
		error("Too much code to jump over.");
	}

	currentChunk()->aryB[offset] = (jump >> 8) & 0xff;
	currentChunk()->aryB[offset + 1] = jump & 0xff;
}

static void initCompiler(Compiler * compiler, Scanner * scanner, Parser * parser, FunctionType type)
{
	compiler->enclosing = current;
	compiler->scanner = scanner;
	compiler->parser = parser;
	compiler->type = type;
	compiler->locals = NULL;
	compiler->upvalues = NULL;
	compiler->scopeDepth = 0;
	compiler->function = NULL;
	compiler->function = newFunction();
	current = compiler;

	if (type != TYPE_SCRIPT)
	{
		current->function->name = copyString(current->parser->previous.start, current->parser->previous.length);
	}

	Local local;
	local.depth = 0;
	local.isCaptured = false;

	if (type != TYPE_FUNCTION)
	{
		local.name.start = "this";
		local.name.length = 4;
	}
	else
	{
		local.name.start = "";
		local.name.length = 0;
	}

	ARY_PUSH(current->locals, local);
}

static ObjFunction * endCompiler(void)
{
	emitReturn();
	ObjFunction * function = current->function;

#if DEBUG_PRINT_CODE
	if (!current->parser->hadError)
	{
		disassembleChunk(
			currentChunk(),
			function->name != NULL ? function->name->aChars : "<script>");
	}
#endif

	current = current->enclosing;

	return function;
}

static void destroyCompiler(Compiler * compiler)
{
	ARY_FREE(compiler->locals);
	ARY_FREE(compiler->upvalues);
}

static void beginScope(void)
{
	current->scopeDepth++;
}

static void endScope(void)
{
	current->scopeDepth--;

	unsigned numLocals = 0;

	while (ARY_LEN(current->locals) > 0 &&
		   ARY_TAIL(current->locals)->depth > current->scopeDepth)
	{
		if (ARY_TAIL(current->locals)->isCaptured)
		{
			emitByte(OP_CLOSE_UPVALUE);
		}
		else
		{
			emitByte(OP_POP);
		}

		numLocals++;
		ARY_POP(current->locals);
	}

	// TODO: Get this working again

	//if (numLocals == 0)
	//	return;

	//if (numLocals == 1)
	//{
	//	emitByte(OP_POP);
	//}
	//else
	//{
	//	// Assumption: Only 256 locals possible
	//	// NOTE: POPN stores N - 2

	//	ASSERT(numLocals <= UINT8_COUNT);

	//	uint8_t arg = (uint8_t)(numLocals - 2);

	//	emitBytes(OP_POPN, arg);
	//}
}

static void binary(bool canAssign)
{
	UNUSED(canAssign);

	// Remember the operator

	TokenType operatorType = current->parser->previous.type;

	// Compile the right operand

	const ParseRule * rule = getRule(operatorType);
	parsePrecedence((Precedence)(rule->precedence + 1));

	// Emit the operator instruction

	switch (operatorType)
	{
		case TOKEN_BANG_EQUAL:		emitBytes(OP_EQUAL, OP_NOT); break;
		case TOKEN_EQUAL_EQUAL:		emitByte(OP_EQUAL); break;
		case TOKEN_GREATER:			emitByte(OP_GREATER); break;
		case TOKEN_GREATER_EQUAL:	emitBytes(OP_LESS, OP_NOT); break;
		case TOKEN_LESS:			emitByte(OP_LESS); break;
		case TOKEN_LESS_EQUAL:		emitBytes(OP_GREATER, OP_NOT); break;
		case TOKEN_PLUS:			emitByte(OP_ADD); break;
		case TOKEN_MINUS:			emitByte(OP_SUBTRACT); break;
		case TOKEN_STAR:			emitByte(OP_MULTIPLY); break;
		case TOKEN_SLASH:			emitByte(OP_DIVIDE); break;
		default:
			return; // Unreachable
	}
}

static void call(bool canAssign)
{
	UNUSED(canAssign);

	uint8_t argCount = argumentList();
	emitBytes(OP_CALL, argCount);
}

static void dot(bool canAssign)
{
	consume(TOKEN_IDENTIFIER, "Expect property name after '.'");
	uint32_t name = identifierConstant(&current->parser->previous);

	if (canAssign && match(TOKEN_EQUAL))
	{
		expression();
		emitConstantHelper(name, OP_SET_PROPERTY, OP_SET_PROPERTY_LONG);
	}
	else if (match(TOKEN_LEFT_PAREN))
	{
		uint8_t argCount = argumentList();
		emitConstantHelper(name, OP_INVOKE, OP_INVOKE_LONG);
		emitByte(argCount);
	}
	else
	{
		emitConstantHelper(name, OP_GET_PROPERTY, OP_GET_PROPERTY_LONG);
	}
}

static void literal(bool canAssign)
{
	UNUSED(canAssign);

	switch (current->parser->previous.type)
	{
		case TOKEN_FALSE: emitByte(OP_FALSE); break;
		case TOKEN_NIL: emitByte(OP_NIL); break;
		case TOKEN_TRUE: emitByte(OP_TRUE); break;
		default:
			return; // Unreachable
	}
}

static void grouping(bool canAssign)
{
	UNUSED(canAssign);

	expression();
	consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
}

static void number(bool canAssign)
{
	UNUSED(canAssign);

	double value = strtod(current->parser->previous.start, NULL);
	emitConstant(NUMBER_VAL(value));
}

static void string(bool canAssign)
{
	UNUSED(canAssign);

	emitConstant(OBJ_VAL(copyString(current->parser->previous.start + 1, current->parser->previous.length - 2)));
}

static void and_(bool canAssign)
{
	UNUSED(canAssign);

	uint32_t endJump = emitJump(OP_JUMP_IF_FALSE);

	emitByte(OP_POP);
	parsePrecedence(PREC_AND);

	patchJump(endJump);
}

static void or_(bool canAssign)
{
	// TODO (matthewp) Not as efficient as just having an OP_JUMP_IF_TRUE

	UNUSED(canAssign);

	uint32_t elseJump = emitJump(OP_JUMP_IF_FALSE);
	uint32_t endJump = emitJump(OP_JUMP);

	patchJump(elseJump);
	emitByte(OP_POP);

	parsePrecedence(PREC_OR);
	patchJump(endJump);
}

static void namedVariable(Token name, bool canAssign)
{
	uint8_t getOp, getOpLong, setOp, setOpLong;
	uint32_t arg;

	if (resolveLocal(current, &name, &arg))
	{
		getOp = OP_GET_LOCAL;
		getOpLong = OP_GET_LOCAL_LONG;
		setOp = OP_SET_LOCAL;
		setOpLong = OP_SET_LOCAL_LONG;
	}
	else if (resolveUpvalue(current, &name, &arg))
	{
		getOp = OP_GET_UPVALUE;
		getOpLong = OP_GET_UPVALUE_LONG;
		setOp = OP_SET_UPVALUE;
		setOpLong = OP_SET_UPVALUE_LONG;
	}
	else
	{
		arg = identifierConstant(&name);
		getOp = OP_GET_GLOBAL;
		getOpLong = OP_GET_GLOBAL_LONG;
		setOp = OP_SET_GLOBAL;
		setOpLong = OP_SET_GLOBAL_LONG;
	}

	if (canAssign && match(TOKEN_EQUAL))
	{
		expression();
		emitConstantHelper(arg, setOp, setOpLong);
	}
	else
	{
		emitConstantHelper(arg, getOp, getOpLong);
	}
}

static void variable(bool canAssign)
{
	namedVariable(current->parser->previous, canAssign);
}

static Token syntheticToken(const char* text)
{
	Token token;
	token.type = TOKEN_ERROR;
	token.start = text;
	token.length = (int)strlen(text);
	return token;
}

static void super_(bool canAssign)
{
	UNUSED(canAssign);

	if (currentClass == NULL)
	{
		error("Cannot use 'super' outside of a class.");
	}
	else if (!currentClass->hasSuperclass)
	{
		error("Cannot user 'super' in a class with no superclass.");
	}

	consume(TOKEN_DOT, "Expect '.' after 'super'.");
	consume(TOKEN_IDENTIFIER, "Expect superclass method name.");

	uint32_t name = identifierConstant(&current->parser->previous);

	namedVariable(syntheticToken("this"), false);

	if (match(TOKEN_LEFT_PAREN))
	{
		uint8_t argCount = argumentList();
		namedVariable(syntheticToken("super"), false);
		emitConstantHelper(name, OP_SUPER_INVOKE, OP_SUPER_INVOKE_LONG);
		emitByte(argCount);
	}
	else
	{
		namedVariable(syntheticToken("super"), false);
		emitConstantHelper(name, OP_GET_SUPER, OP_GET_SUPER_LONG);
	}
}

static void unary(bool canAssign)
{
	UNUSED(canAssign);

	TokenType operatorType = current->parser->previous.type;

	// Compile the operand

	parsePrecedence(PREC_UNARY);

	// Emit the operator instruction

	switch (operatorType)
	{
		case TOKEN_BANG: emitByte(OP_NOT); break;
		case TOKEN_MINUS: emitByte(OP_NEGATE); break;
		default:
			return; // Unreachable
	}
}

static void this_(bool canAssign)
{
	UNUSED(canAssign);

	if (currentClass == NULL)
	{
		error("Cannot use 'this' outside of a class.");
		return;
	}

	variable(false);
}

static const ParseRule rules[] =
{
	{ grouping, call,    PREC_CALL },       // TOKEN_LEFT_PAREN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_RIGHT_PAREN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_LEFT_BRACE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_RIGHT_BRACE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_COMMA
	{ NULL,     dot,     PREC_CALL },       // TOKEN_DOT
	{ unary,    binary,  PREC_TERM },       // TOKEN_MINUS
	{ NULL,     binary,  PREC_TERM },       // TOKEN_PLUS
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_SEMICOLON
	{ NULL,     binary,  PREC_FACTOR },     // TOKEN_SLASH
	{ NULL,     binary,  PREC_FACTOR },     // TOKEN_STAR
	{ unary,    NULL,    PREC_NONE },       // TOKEN_BANG
	{ NULL,     binary,  PREC_EQUALITY },   // TOKEN_BANG_EQUAL
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_EQUAL
	{ NULL,     binary,  PREC_EQUALITY },   // TOKEN_EQUAL_EQUAL
	{ NULL,     binary,  PREC_COMPARISON }, // TOKEN_GREATER
	{ NULL,     binary,  PREC_COMPARISON }, // TOKEN_GREATER_EQUAL
	{ NULL,     binary,  PREC_COMPARISON }, // TOKEN_LESS
	{ NULL,     binary,  PREC_COMPARISON }, // TOKEN_LESS_EQUAL
	{ variable, NULL,    PREC_NONE },       // TOKEN_IDENTIFIER
	{ string,   NULL,    PREC_NONE },       // TOKEN_STRING
	{ number,   NULL,    PREC_NONE },       // TOKEN_NUMBER
	{ NULL,     and_,    PREC_AND },        // TOKEN_AND
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_CLASS
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_ELSE
	{ literal,  NULL,    PREC_NONE },       // TOKEN_FALSE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_FOR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_FUN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_IF
	{ literal,  NULL,    PREC_NONE },       // TOKEN_NIL
	{ NULL,     or_,     PREC_OR },         // TOKEN_OR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_PRINT
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_RETURN
	{ super_,   NULL,    PREC_NONE },       // TOKEN_SUPER
	{ this_,    NULL,    PREC_NONE },       // TOKEN_THIS
	{ literal,  NULL,    PREC_NONE },       // TOKEN_TRUE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_VAR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_WHILE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_ERROR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_EOF
};

static void parsePrecedence(Precedence precedence)
{
	advance();

	ParseFn prefixFn = getRule(current->parser->previous.type)->prefix;

	if (prefixFn == NULL)
	{
		error("Expect expression.");
		return;
	}

	bool canAssign = (precedence <= PREC_ASSIGNMENT);
	prefixFn(canAssign);

	while (precedence <= getRule(current->parser->current.type)->precedence)
	{
		advance();
		ParseFn infixFn = getRule(current->parser->previous.type)->infix;
		infixFn(canAssign);
	}

	if (canAssign && match(TOKEN_EQUAL))
	{
		error("Invalid assignment target.");
	}
}

static uint32_t identifierConstant(Token * name)
{
	return makeConstant(OBJ_VAL(copyString(name->start, name->length)));
}

static bool identifiersEqual(Token * a, Token * b)
{
	if (a->length != b->length)
		return false;

	return memcmp(a->start, b->start, a->length) == 0;
}

static bool resolveLocal(Compiler * compiler, Token * name, uint32_t * localIndex)
{
	for (int i = ARY_LEN(compiler->locals) - 1; i >= 0; i--)
	{
		Local * local = &compiler->locals[i];

		if (identifiersEqual(name, &local->name))
		{
			if (local->depth == -1)
			{
				error("Cannot read local variable in its own initializer.");
			}

			*localIndex = i;
			return true;
		}
	}

	return false;
}

static uint32_t addUpvalue(Compiler * compiler, uint32_t index, bool isLocal)
{
	uint32_t upvalueCount = compiler->function->upvalueCount;
	ASSERT(upvalueCount == ARY_LEN(compiler->upvalues));

	for (uint32_t i = 0; i < upvalueCount; ++i)
	{
		Upvalue * upvalue = &compiler->upvalues[i];

		if (upvalue->index == index && upvalue->isLocal == isLocal)
			return i;
	}

	if (upvalueCount >= UINT24_COUNT)
	{
		error("Too many captured variables in closure.");
		return 0;
	}

	Upvalue upvalue;
	upvalue.isLocal = isLocal;
	upvalue.index = index;
	ARY_PUSH(compiler->upvalues, upvalue);
	compiler->function->upvalueCount++;

	return ARY_LEN(compiler->upvalues) - 1;
}

static bool resolveUpvalue(Compiler * compiler, Token* name, uint32_t* upvalueIndex)
{
	if (compiler->enclosing == NULL) return false;

	uint32_t localIndex;
	if (resolveLocal(compiler->enclosing, name, &localIndex))
	{
		ASSERT(localIndex < UINT24_COUNT);
		ASSERT(localIndex < ARY_LEN(compiler->enclosing->locals));

		compiler->enclosing->locals[localIndex].isCaptured = true;
		*upvalueIndex = addUpvalue(compiler, localIndex, true);
		return true;
	}

	uint32_t upvalueIndexEnclosing;
	if (resolveUpvalue(compiler->enclosing, name, &upvalueIndexEnclosing))
	{
		*upvalueIndex = addUpvalue(compiler, upvalueIndexEnclosing, false);
		return true;
	}

	return false;
}

static void addLocal(Token name)
{
	if (ARY_LEN(current->locals) >= UINT24_COUNT)
	{
		error("Too many local variables in function.");
		return;
	}

	Local local;
	local.name = name;
	local.depth = -1;
	local.isCaptured = false;
	ARY_PUSH(current->locals, local);
}

static void declareVariable(void)
{
	// Global variables are implicitly declared

	if (current->scopeDepth == 0)
		return;

	Token * name = &current->parser->previous;

	for (int i = ARY_LEN(current->locals) - 1; i >= 0; i--)
	{
		Local * local = &current->locals[i];

		if (local->depth != -1 && local->depth < current->scopeDepth)
			break;

		if (identifiersEqual(name, &local->name))
		{
			error("Variable with this name already declared in this scope.");
		}
	}

	addLocal(*name);
}

static uint32_t parseVariable(const char * errorMessage)
{
	consume(TOKEN_IDENTIFIER, errorMessage);

	declareVariable();

	if (current->scopeDepth > 0)
		return 0;

	return identifierConstant(&current->parser->previous);
}

static void markInitialized(void)
{
	if (current->scopeDepth == 0)
		return;

	ARY_TAIL(current->locals)->depth = current->scopeDepth;
}

static void defineVariable(uint32_t global)
{
	if (current->scopeDepth > 0)
	{
		markInitialized();
		return;
	}

	if (global >= UINT24_COUNT)
	{
		error("Too many global variables defined.");
		return;
	}

	emitConstantHelper(global, OP_DEFINE_GLOBAL, OP_DEFINE_GLOBAL_LONG);
}

static uint8_t argumentList(void)
{
	uint8_t argCount = 0;

	if (!check(TOKEN_RIGHT_PAREN))
	{
		do
		{
			expression();

			if (argCount == 255)
			{
				error("Cannot have more than 255 arguments.");
			}

			argCount++;
		}
		while (match(TOKEN_COMMA));
	}

	consume(TOKEN_RIGHT_PAREN, "Expect ')' after arguments.");

	return argCount;
}

static const ParseRule * getRule(TokenType type)
{
	return &rules[type];
}

static void expression(void)
{
	parsePrecedence(PREC_ASSIGNMENT);
}

static void block(void)
{
	while (!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF))
	{
		declaration();
	}

	consume(TOKEN_RIGHT_BRACE, "Expect '}' after block.");
}

static void function(FunctionType type)
{
	Compiler compiler;
	initCompiler(&compiler, current->scanner, current->parser, type);
	beginScope();

	// Compile the parameter list

	consume(TOKEN_LEFT_PAREN, "Expect '(' after function name.");

	if (!check(TOKEN_RIGHT_PAREN))
	{
		do
		{
			uint32_t paramConstant = parseVariable("Expect parameter name.");
			defineVariable(paramConstant);

			current->function->arity++;

			if (current->function->arity > 255)
			{
				error("Cannot have more than 255 parameters.");
			}
		}
		while (match(TOKEN_COMMA));
	}

	consume(TOKEN_RIGHT_PAREN, "Expect ')' after parameters.");

	// The body

	consume(TOKEN_LEFT_BRACE, "Expect '{' before function body.");
	block();

	// Create the runtime closure object pointing to the compiled function

	ObjFunction * function = endCompiler();

	uint32_t constant = makeConstant(OBJ_VAL(function));
	emitConstantHelper(constant, OP_CLOSURE, OP_CLOSURE_LONG);

	uint32_t upvalueCount = function->upvalueCount;
	ASSERT(upvalueCount == ARY_LEN(compiler.upvalues));

	for (uint32_t i = 0; i < upvalueCount; ++i)
	{
		uint32_t index = compiler.upvalues[i].index;
		bool longInstruction = (index > UINT8_MAX);

		uint8_t flag = 0;
		if (compiler.upvalues[i].isLocal) flag |= 0x1;
		if (longInstruction) flag |= 0x2;

		emitByte(flag);

		if (longInstruction)
		{
			emitU24(index);
		}
		else
		{
			emitByte((uint8_t)index);
		}
	}

	destroyCompiler(&compiler);
}

static void method(void)
{
	consume(TOKEN_IDENTIFIER, "Expect method name.");

	uint32_t constant = identifierConstant(&current->parser->previous);

	FunctionType type = TYPE_METHOD;

	if (current->parser->previous.length == 4 && memcmp(current->parser->previous.start, "init", 4) == 0)
	{
		type = TYPE_INITIALIZER;
	}

	function(type);

	emitConstantHelper(constant, OP_METHOD, OP_METHOD_LONG);
}

static void declaration(void)
{
	if (match(TOKEN_CLASS))
	{
		classDeclaration();
	}
	else if (match(TOKEN_FUN))
	{
		funDeclaration();
	}
	else if (match(TOKEN_VAR))
	{
		varDeclaration();
	}
	else
	{
		statement();
	}

	if (current->parser->panicMode)
	{
		synchronize();
	}
}

static void classDeclaration(void)
{
	consume(TOKEN_IDENTIFIER, "Expect class name.");
	Token className = current->parser->previous;
	uint32_t nameConstant = identifierConstant(&current->parser->previous);
	declareVariable();

	emitConstantHelper(nameConstant, OP_CLASS, OP_CLASS_LONG);
	defineVariable(nameConstant);

	ClassCompiler classCompiler;
	classCompiler.name = className;
	classCompiler.enclosing = currentClass;
	classCompiler.hasSuperclass = false;
	currentClass = &classCompiler;

	if (match(TOKEN_LESS))
	{
		consume(TOKEN_IDENTIFIER, "Expect superclass name.");
		variable(false);

		if (identifiersEqual(&className, &current->parser->previous))
		{
			error("A class cannot inherit from itself.");
		}

		beginScope();
		addLocal(syntheticToken("super"));
		defineVariable(0);

		namedVariable(className, false);
		emitByte(OP_INHERIT);
		classCompiler.hasSuperclass = true;
	}

	namedVariable(className, false);

	consume(TOKEN_LEFT_BRACE, "Expect '{' before class body.");

	while (!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF))
	{
		method();
	}

	consume(TOKEN_RIGHT_BRACE, "Expect '}' after class body.");

	emitByte(OP_POP);

	if (classCompiler.hasSuperclass)
	{
		endScope();
	}

	currentClass = currentClass->enclosing;
}

static void funDeclaration(void)
{
	uint32_t global = parseVariable("Expect function name.");
	markInitialized();
	function(TYPE_FUNCTION);
	defineVariable(global);
}

static void varDeclaration(void)
{
	uint32_t global = parseVariable("Expect variable name.");

	if (match(TOKEN_EQUAL))
	{
		expression();
	}
	else
	{
		emitByte(OP_NIL);
	}

	consume(TOKEN_SEMICOLON, "Expect ';' after variable declaration.");

	defineVariable(global);
}

static void statement(void)
{
	if (match(TOKEN_PRINT))
	{
		printStatement();
	}
	else if (match(TOKEN_FOR))
	{
		forStatement();
	}
	else if (match(TOKEN_IF))
	{
		ifStatement();
	}
	else if (match(TOKEN_RETURN))
	{
		returnStatement();
	}
	else if (match(TOKEN_WHILE))
	{
		whileStatement();
	}
	else if (match(TOKEN_LEFT_BRACE))
	{
		beginScope();
		block();
		endScope();
	}
	else
	{
		expressionStatement();
	}
}

static void printStatement(void)
{
	expression();
	consume(TOKEN_SEMICOLON, "Expect ';' after value.");
	emitByte(OP_PRINT);
}

static void returnStatement(void)
{
	if (current->type == TYPE_SCRIPT)
	{
		error("Cannot return from top-level code.");
	}

	if (match(TOKEN_SEMICOLON))
	{
		emitReturn();
	}
	else
	{
		if (current->type == TYPE_INITIALIZER)
		{
			error("Cannot return a value from an initializer.");
		}

		expression();
		consume(TOKEN_SEMICOLON, "Expect ';' after return value.");
		emitByte(OP_RETURN);
	}
}

static void whileStatement(void)
{
	// TODO (matthewp) Add support for 'continue' statement

	uint32_t loopStart = ARY_LEN(currentChunk()->aryB);

	consume(TOKEN_LEFT_PAREN, "Expect '(' after 'while'.");
	expression();
	consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

	uint32_t exitJump = emitJump(OP_JUMP_IF_FALSE);

	emitByte(OP_POP);
	statement();

	emitLoop(loopStart);

	patchJump(exitJump);
	emitByte(OP_POP);
}

static void expressionStatement(void)
{
	expression();
	consume(TOKEN_SEMICOLON, "Expect ';' after expression.");
	emitByte(OP_POP);
}

static void forStatement(void)
{
	// TODO (matthewp) Add support for 'continue' statement

	beginScope();

	consume(TOKEN_LEFT_PAREN, "Expect '(' after 'for'.");

	if (match(TOKEN_SEMICOLON))
	{
		// No initializer
	}
	else if (match(TOKEN_VAR))
	{
		varDeclaration();
	}
	else
	{
		expressionStatement();
	}

	uint32_t loopStart = ARY_LEN(currentChunk()->aryB);

	bool hasJump = false;
	uint32_t exitJump = 0;

	if (!match(TOKEN_SEMICOLON))
	{
		expression();
		consume(TOKEN_SEMICOLON, "Expect ';' after loop condition.");

		// Jump out of the loop if the condition is false

		exitJump = emitJump(OP_JUMP_IF_FALSE);
		emitByte(OP_POP); // Condition
		hasJump = true;
	}

	if (!match(TOKEN_RIGHT_PAREN))
	{
		// TODO (matthewp) This is pretty weird an adds additional jumps

		uint32_t bodyJump = emitJump(OP_JUMP);

		uint32_t incrementStart = ARY_LEN(currentChunk()->aryB);
		expression();
		emitByte(OP_POP);
		consume(TOKEN_RIGHT_PAREN, "Expect ')' after for clauses.");

		emitLoop(loopStart);
		loopStart = incrementStart;
		patchJump(bodyJump);
	}

	statement();

	emitLoop(loopStart);

	if (hasJump)
	{
		patchJump(exitJump);
		emitByte(OP_POP); // Condition
	}

	endScope();
}

static void ifStatement(void)
{
	// TODO (matthewp) Support 'switch' statements

	consume(TOKEN_LEFT_PAREN, "Expect '(' after 'if'.");
	expression();
	consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

	uint32_t thenJump = emitJump(OP_JUMP_IF_FALSE);
	emitByte(OP_POP);
	statement();

	uint32_t elseJump = emitJump(OP_JUMP);

	patchJump(thenJump);
	emitByte(OP_POP);

	if (match(TOKEN_ELSE))
	{
		statement();
	}

	patchJump(elseJump);
}

void markCompilerRoots(void)
{
	Compiler* compiler = current;

	while (compiler != NULL)
	{
		markObject((Obj*)compiler->function);
		compiler = compiler->enclosing;
	}
}
