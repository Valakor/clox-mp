//
//  debug.c
//  clox
//
//  Created by Matthew Pohlmann on 2/19/18.
//  Copyright © 2018 Matthew Pohlmann. All rights reserved.
//

#include "common.h"
#include "debug.h"

#include <stdio.h>

#include "object.h"
#include "value.h"
#include "array.h"

void disassembleChunk(Chunk * chunk, const char * name)
{
	printf("== %s ==\n", name);

	for (unsigned i = 0; i < ARY_LEN(chunk->aryB);)
	{
		i = disassembleInstruction(chunk, i);
	}
}

static inline uint32_t readU24(Chunk * chunk, unsigned offset)
{
	uint32_t constant = chunk->aryB[offset];
	constant = constant << 8;
	constant |= chunk->aryB[offset + 1];
	constant = constant << 8;
	constant |= chunk->aryB[offset + 2];
	return constant;
}

static unsigned getConstant(Chunk * chunk, bool isLong, unsigned * offsetOut)
{
	unsigned constant;
	unsigned constantBytes;

	unsigned offset = *offsetOut;

	if (isLong)
	{
		constantBytes = 3;

		ASSERT(offset + constantBytes <= ARY_LEN(chunk->aryB));

		constant = readU24(chunk, offset);
	}
	else
	{
		constantBytes = 1;

		ASSERT(offset + constantBytes <= ARY_LEN(chunk->aryB));

		constant = chunk->aryB[offset];
	}

	ASSERT(constant < ARY_LEN(chunk->aryValConstants));

	*offsetOut += constantBytes;

	return constant;
}

static unsigned constantInstruction(const char * name, Chunk * chunk, unsigned offset, bool isLong)
{
	offset += 1;

	unsigned constant = getConstant(chunk, isLong, &offset);

	printf("%-16s %4u '", name, constant);
	printValue(chunk->aryValConstants[constant]);
	printf("'\n");

	return offset;
}

static unsigned invokeInstruction(const char * name, Chunk * chunk, unsigned offset, bool isLong)
{
	offset += 1;

	unsigned constant = getConstant(chunk, isLong, &offset);
	uint8_t argCount = chunk->aryB[offset++];

	printf("%-16s %4d '", name, constant);
	printValue(chunk->aryValConstants[constant]);
	printf("' (%d args)\n", argCount);

	return offset;
}

static unsigned closureInstruction(const char * name, Chunk * chunk, unsigned offset, bool isLong)
{
	offset += 1;

	unsigned constant = getConstant(chunk, isLong, &offset);

	printf("%-16s %4u '", name, constant);
	printValue(chunk->aryValConstants[constant]);
	printf("'\n");

	ObjFunction * function = AS_FUNCTION(chunk->aryValConstants[constant]);

	for (int j = 0; j < function->upvalueCount; ++j)
	{
		int isLocal = chunk->aryB[offset++];
		int index = chunk->aryB[offset++];
		printf("%04d      |                     %s %d\n", offset - 2, isLocal ? "local" : "upvalue", index);
	}

	return offset;
}

static unsigned simpleInstruction(const char * name, unsigned offset)
{
	printf("%s\n", name);
	return offset + 1;
}

static unsigned immediateInstruction(const char * name, Chunk * chunk, unsigned offset, bool isLong)
{
	offset += 1;
	uint32_t slot = (isLong) ? readU24(chunk, offset) : chunk->aryB[offset];
	printf("%-16s %4d\n", name, slot);
	return offset + ((isLong) ? 3 : 1);
}

static unsigned jumpInstruction(const char * name, int sign, Chunk * chunk, int offset)
{
	uint16_t jump = (uint16_t)(chunk->aryB[offset + 1] << 8);
	jump |= chunk->aryB[offset + 2];
	printf("%-16s %4d -> %d\n", name, offset, offset + 3 + sign * jump);
	return offset + 3;
}

unsigned disassembleInstruction(Chunk * chunk, unsigned offset)
{
	ASSERT(offset < ARY_LEN(chunk->aryB));

	printf("%04d ", offset);

	unsigned line = getLine(chunk, offset);

	if (offset > 0 && line == getLine(chunk, offset - 1))
	{
		printf("   | ");
	}
	else
	{
		printf("%4d ", line);
	}

	uint8_t instruction = chunk->aryB[offset];
	switch (instruction)
	{
		case OP_CONSTANT:
			return constantInstruction("OP_CONSTANT", chunk, offset, false);
		case OP_CONSTANT_LONG:
			return constantInstruction("OP_CONSTANT_LONG", chunk, offset, true);
		case OP_NIL:
			return simpleInstruction("OP_NIL", offset);
		case OP_TRUE:
			return simpleInstruction("OP_TRUE", offset);
		case OP_FALSE:
			return simpleInstruction("OP_FALSE", offset);
		case OP_POP:
			return simpleInstruction("OP_POP", offset);
		case OP_POPN:
			return immediateInstruction("OP_POPN", chunk, offset, false);
		case OP_GET_LOCAL:
			return immediateInstruction("OP_GET_LOCAL", chunk, offset, false);
		case OP_GET_LOCAL_LONG:
			return immediateInstruction("OP_GET_LOCAL_LONG", chunk, offset, true);
		case OP_SET_LOCAL:
			return immediateInstruction("OP_SET_LOCAL", chunk, offset, false);
		case OP_SET_LOCAL_LONG:
			return immediateInstruction("OP_SET_LOCAL_LONG", chunk, offset, true);
		case OP_GET_GLOBAL:
			return constantInstruction("OP_GET_GLOBAL", chunk, offset, false);
		case OP_GET_GLOBAL_LONG:
			return constantInstruction("OP_GET_GLOBAL_LONG", chunk, offset, true);
		case OP_DEFINE_GLOBAL:
			return constantInstruction("OP_DEFINE_GLOBAL", chunk, offset, false);
		case OP_DEFINE_GLOBAL_LONG:
			return constantInstruction("OP_DEFINE_GLOBAL_LONG", chunk, offset, true);
		case OP_SET_GLOBAL:
			return constantInstruction("OP_SET_GLOBAL", chunk, offset, false);
		case OP_SET_GLOBAL_LONG:
			return constantInstruction("OP_SET_GLOBAL_LONG", chunk, offset, true);
		case OP_GET_UPVALUE:
			return immediateInstruction("OP_GET_UPVALUE", chunk, offset, false);
		case OP_GET_UPVALUE_LONG:
			return immediateInstruction("OP_GET_UPVALUE_LONG", chunk, offset, true);
		case OP_SET_UPVALUE:
			return immediateInstruction("OP_SET_UPVALUE", chunk, offset, false);
		case OP_SET_UPVALUE_LONG:
			return immediateInstruction("OP_SET_UPVALUE_LONG", chunk, offset, true);
		case OP_GET_PROPERTY:
			return constantInstruction("OP_GET_PROPERTY", chunk, offset, false);
		case OP_GET_PROPERTY_LONG:
			return constantInstruction("OP_GET_PROPERTY_LONG", chunk, offset, true);
		case OP_SET_PROPERTY:
			return constantInstruction("OP_SET_PROPERTY", chunk, offset, false);
		case OP_SET_PROPERTY_LONG:
			return constantInstruction("OP_SET_PROPERTY_LONG", chunk, offset, true);
		case OP_GET_SUPER:
			return constantInstruction("OP_GET_SUPER", chunk, offset, false);
		case OP_GET_SUPER_LONG:
			return constantInstruction("OP_GET_SUPER_LONG", chunk, offset, true);
		case OP_EQUAL:
			return simpleInstruction("OP_EQUAL", offset);
		case OP_GREATER:
			return simpleInstruction("OP_GREATER", offset);
		case OP_LESS:
			return simpleInstruction("OP_LESS", offset);
		case OP_NEGATE:
			return simpleInstruction("OP_NEGATE", offset);
		case OP_ADD:
			return simpleInstruction("OP_ADD", offset);
		case OP_SUBTRACT:
			return simpleInstruction("OP_SUBTRACT", offset);
		case OP_MULTIPLY:
			return simpleInstruction("OP_MULTIPLY", offset);
		case OP_DIVIDE:
			return simpleInstruction("OP_DIVIDE", offset);
		case OP_NOT:
			return simpleInstruction("OP_NOT", offset);
		case OP_PRINT:
			return simpleInstruction("OP_PRINT", offset);
		case OP_JUMP:
			return jumpInstruction("OP_JUMP", 1, chunk, offset);
		case OP_JUMP_IF_FALSE:
			return jumpInstruction("OP_JUMP_IF_FALSE", 1, chunk, offset);
		case OP_LOOP:
			return jumpInstruction("OP_LOOP", -1, chunk, offset);
		case OP_CALL:
			return immediateInstruction("OP_CALL", chunk, offset, false);
		case OP_INVOKE:
			return invokeInstruction("OP_INVOKE", chunk, offset, false);
		case OP_INVOKE_LONG:
			return invokeInstruction("OP_INVOKE_LONG", chunk, offset, true);
		case OP_SUPER_INVOKE:
			return invokeInstruction("OP_SUPER_INVOKE", chunk, offset, false);
		case OP_SUPER_INVOKE_LONG:
			return invokeInstruction("OP_SUPER_INVOKE_LONG", chunk, offset, true);
		case OP_CLOSURE:
			return closureInstruction("OP_CLOSURE", chunk, offset, false);
		case OP_CLOSURE_LONG:
			return closureInstruction("OP_CLOSURE_LONG", chunk, offset, true);
		case OP_CLOSE_UPVALUE:
			return simpleInstruction("OP_CLOSE_UPVALUE", offset);
		case OP_RETURN:
			return simpleInstruction("OP_RETURN", offset);
		case OP_CLASS:
			return constantInstruction("OP_CLASS", chunk, offset, false);
		case OP_CLASS_LONG:
			return constantInstruction("OP_CLASS_LONG", chunk, offset, true);
		case OP_INHERIT:
			return simpleInstruction("OP_INHERIT", offset);
		case OP_METHOD:
			return constantInstruction("OP_METHOD", chunk, offset, false);
		case OP_METHOD_LONG:
			return constantInstruction("OP_METHOD_LONG", chunk, offset, true);
		default:
			printf("Unknown opcode %d\n", instruction);
			return offset + 1;
	}
}
