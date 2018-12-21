//
//  compiler.c
//  clox
//
//  Created by Matthew Pohlmann on 5/18/18.
//  Copyright © 2018 Matthew Pohlmann. All rights reserved.
//

#include "compiler.h"
#include "scanner.h"
#include "debug.h"
#include "object.h"

#include <stdio.h>
#include <stdlib.h>


typedef struct
{
	Token current;
	Token previous;

	bool hadError;
	bool panicMode;
} Parser;

typedef enum
{
	PREC_NONE,
	PREC_ASSIGNMENT,	// =
	PREC_OR,			// or
	PREC_AND,			// and
	PREC_EQUALITY,		// == !=
	PREC_COMPARISON,	// < > <= >=
	PREC_TERM,			// + -
	PREC_FACTOR,		// * /
	PREC_UNARY,			// ! - +
	PREC_CALL,			// . () []
	PREC_PRIMARY,
} Precedence;

typedef void (*ParseFn)(void);

typedef struct
{
	ParseFn prefix;
	ParseFn infix;
	Precedence precedence;
} ParseRule;

Parser parser;
Chunk * compilingChunk;


static void advance(void);
static void errorAtCurrent(const char * message);
static void error(const char * message);
static void errorAt(Token * token, const char * message);
static void consume(TokenType type, const char * message);
static void emitByte(uint8_t byte);
static void emitBytes(uint8_t byte1, uint8_t byte2);
static Chunk * currentChunk(void);
static void endCompiler(void);
static void emitReturn(void);
static void expression(void);
static void parsePrecedence(Precedence precendece);
static const ParseRule * getRule(TokenType type);

bool compile(const char * source, Chunk * chunk)
{
	initScanner(source);

	compilingChunk = chunk;

	memset(&parser, 0, sizeof(parser));

	advance();
	expression();
	consume(TOKEN_EOF, "Expect end of expression.");

	endCompiler();

	return !parser.hadError;
}

static void advance(void)
{
	parser.previous = parser.current;

	for (;;)
	{
		parser.current = scanToken();

		if (parser.current.type != TOKEN_ERROR)
			break;

		errorAtCurrent(parser.current.start);
	}
}

static void errorAtCurrent(const char * message)
{
	errorAt(&parser.current, message);
}

static void error(const char * message)
{
	errorAt(&parser.previous, message);
}

static void errorAt(Token * token, const char * message)
{
	if (parser.panicMode)
		return;

	parser.panicMode = true;

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

	parser.hadError = true;
}

static void consume(TokenType type, const char * message)
{
	if (parser.current.type == type)
	{
		advance();
		return;
	}

	errorAtCurrent(message);
}

static Chunk * currentChunk(void)
{
	return compilingChunk;
}

static void emitByte(uint8_t byte)
{
	writeChunk(currentChunk(), byte, parser.previous.line);
}

static void emitBytes(uint8_t byte1, uint8_t byte2)
{
	emitByte(byte1);
	emitByte(byte2);
}

static void emitReturn(void)
{
	emitByte(OP_RETURN);
}

static void emitConstant(Value value)
{
	if (!writeConstant(currentChunk(), value, parser.previous.line))
	{
		error("Too many constants in one chunk");
	}
}

static void endCompiler(void)
{
	emitReturn();

#if DEBUG_PRINT_CODE
	if (!parser.hadError)
	{
		disassembleChunk(currentChunk(), "code");
	}
#endif
}

static void binary()
{
	// Remember the operator

	TokenType operatorType = parser.previous.type;

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

static void literal()
{
	switch (parser.previous.type)
	{
		case TOKEN_FALSE: emitByte(OP_FALSE); break;
		case TOKEN_NIL: emitByte(OP_NIL); break;
		case TOKEN_TRUE: emitByte(OP_TRUE); break;
		default:
			return; // Unreachable
	}
}

static void grouping()
{
	expression();
	consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
}

static void number(void)
{
	double value = strtod(parser.previous.start, NULL);
	emitConstant(NUMBER_VAL(value));
}

static void string(void)
{
	emitConstant(OBJ_VAL(copyString(parser.previous.start + 1, parser.previous.length - 2)));
}

static void unary()
{
	TokenType operatorType = parser.previous.type;

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

static const ParseRule rules[] =
{
	{ grouping, NULL,    PREC_CALL },       // TOKEN_LEFT_PAREN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_RIGHT_PAREN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_LEFT_BRACE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_RIGHT_BRACE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_COMMA
	{ NULL,     NULL,    PREC_CALL },       // TOKEN_DOT
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
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_IDENTIFIER
	{ string,   NULL,    PREC_NONE },       // TOKEN_STRING
	{ number,   NULL,    PREC_NONE },       // TOKEN_NUMBER
	{ NULL,     NULL,    PREC_AND },        // TOKEN_AND
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_CLASS
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_ELSE
	{ literal,  NULL,    PREC_NONE },       // TOKEN_FALSE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_FOR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_FUN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_IF
	{ literal,  NULL,    PREC_NONE },       // TOKEN_NIL
	{ NULL,     NULL,    PREC_OR },         // TOKEN_OR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_PRINT
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_RETURN
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_SUPER
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_THIS
	{ literal,  NULL,    PREC_NONE },       // TOKEN_TRUE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_VAR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_WHILE
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_ERROR
	{ NULL,     NULL,    PREC_NONE },       // TOKEN_EOF
};

static void parsePrecedence(Precedence precedence)
{
	advance();

	ParseFn prefixFn = getRule(parser.previous.type)->prefix;

	if (prefixFn == NULL)
	{
		error("Expect expression.");
		return;
	}

	prefixFn();

	while (precedence <= getRule(parser.current.type)->precedence)
	{
		advance();
		ParseFn infixFn = getRule(parser.previous.type)->infix;
		infixFn();
	}
}

static const ParseRule * getRule(TokenType type)
{
	return &rules[type];
}

static void expression(void)
{
	parsePrecedence(PREC_ASSIGNMENT);
}