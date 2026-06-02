//
//  vm.c
//  clox
//
//  Created by Matthew Pohlmann on 4/6/18.
//  Copyright © 2018 Matthew Pohlmann. All rights reserved.
//

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>

#include "vm.h"

#include "debug.h"
#include "compiler.h"
#include "object.h"
#include "memory.h"



VM vm; // TODO (matthewp) Make this not a global!

static void resetStack(void);
static bool callValue(Value callee, int argCount);
static void defineNative(const char * name, NativeFn function);

static bool clockNative(int argCount, Value * args);
static bool errNative(int argCount, Value * args);
static bool getNative(int argCount, Value * args);
static bool deleteNative(int argCount, Value * args);
static bool isNative(int argCount, Value * args);

void initVM(void)
{
	resetStack();
	vm.objects = NULL;
	initTable(&vm.globals);
	initTable(&vm.strings);
	vm.openUpvalues = NULL;
	vm.grayStack = NULL;
	vm.bytesAllocated = 0;
	vm.bytesAllocatedMax = 0;
	vm.nextGC = 64 * 1024;
	vm.runningGC = false;
	vm.initString = copyString("init", 4);

	defineNative("clock", clockNative);
	defineNative("error", errNative);
	defineNative("get", getNative);
	defineNative("delete", deleteNative);
	defineNative("is", isNative);
}

void freeVM(void)
{
	freeTable(&vm.globals);
	freeTable(&vm.strings);
	vm.initString = NULL;
	freeObjects();

	// BB (matthewp) Use array/memory helpers here

	free(vm.grayStack);

	ASSERTMSG(vm.bytesAllocated == 0, "Memory leak detected! (vm.bytesAllocated=%zu)", vm.bytesAllocated);

#if DEBUG_ALLOC
	ASSERTMSG(s_cAlloc == 0, "Memory leak detected! (s_cAlloc=%llu)", s_cAlloc);
	printf("[Memory] Max allocated bytes: %zu\n", vm.bytesAllocatedMax);
#endif // #if DEBUG_ALLOC
}

void push(Value value)
{
	ASSERT((int64_t)(vm.stackTop - vm.stack) < STACK_MAX);

	*vm.stackTop = value;
	vm.stackTop++;
}

Value pop(void)
{
	ASSERT((int64_t)(vm.stackTop - vm.stack) > 0);

	vm.stackTop--;
	return *vm.stackTop;
}

static Value peek(int distance)
{
	ASSERT(vm.stackTop - 1 - distance >= vm.stack);

	return vm.stackTop[-1 - distance];
}

static bool isFalsey(Value value)
{
	return IS_NIL(value) || (IS_BOOL(value) && !AS_BOOL(value));
}

static void concatenate(void)
{
	ObjString * b = AS_STRING(peek(0));
	ObjString * a = AS_STRING(peek(1));

	ObjString * result = concatStrings(a, b);

	pop();
	pop();
	push(OBJ_VAL(result));
}

static InterpretResult run(void);

InterpretResult interpret(const char * source)
{
	ObjFunction * function = compile(source);

	if (function == NULL)
		return INTERPRET_COMPILE_ERROR;

	return interpretFunction(function);
}

InterpretResult interpretFunction(ObjFunction * function)
{
	// A null name indicates the root "function" (the script itself)

	ASSERT(function);
	ASSERT(function->name == NULL);

	push(OBJ_VAL(function));
	ObjClosure * closure = newClosure(function);
	pop();
	push(OBJ_VAL(closure));
	callValue(OBJ_VAL(closure), 0);

	return run();
}

static void resetStack(void)
{
	vm.stackTop = vm.stack;
	vm.frameCount = 0;
}

static bool clockNative(int argCount, Value * args)
{
	UNUSED(argCount);
	args[-1] = NUMBER_VAL((double)clock() / CLOCKS_PER_SEC);
	return true;
}

static bool errNative(int argCount, Value * args)
{
	if (argCount > 0 && IS_STRING(args[0]))
	{
		args[-1] = args[0];
	}
	else
	{
		args[-1] = OBJ_VAL(copyString("Runtime Error", 13));
	}

	return false;
}

static bool getNative(int argCount, Value * args)
{
	if ((argCount == 2 || argCount == 3) && IS_INSTANCE(args[0]) && IS_STRING(args[1]))
	{
		ObjInstance* instance = AS_INSTANCE(args[0]);
		ObjString* name = AS_STRING(args[1]);
		Value value;
		if (!tableGet(&instance->fields, name, &value)) value = (argCount == 2) ? NIL_VAL : args[2];
		args[-1] = value;
		return true;
	}

	args[-1] = OBJ_VAL(copyString("Invalid arguments to get", 24));
	return false;
}

static bool deleteNative(int argCount, Value * args)
{
	if (argCount == 2 && IS_INSTANCE(args[0]) && IS_STRING(args[1]))
	{
		ObjInstance* instance = AS_INSTANCE(args[0]);
		ObjString* name = AS_STRING(args[1]);
		args[-1] = BOOL_VAL(tableDelete(&instance->fields, name));
		return true;
	}

	args[-1] = OBJ_VAL(copyString("Invalid arguments to delete", 27));
	return false;
}

static bool isNative(int argCount, Value * args)
{
	if (argCount == 2 && IS_INSTANCE(args[0]) && IS_CLASS(args[1]))
	{
		ObjInstance* instance = AS_INSTANCE(args[0]);
		ObjClass* klass = AS_CLASS(args[1]);
		args[-1] = BOOL_VAL(instance->klass == klass);
		return true;
	}

	args[-1] = OBJ_VAL(copyString("Invalid arguments to is", 23));
	return false;
}

static void runtimeError(const char * format, ...)
{
	fputs("ERROR: ", stderr);

	va_list args;
	va_start(args, format);
	vfprintf(stderr, format, args);
	va_end(args);

	fputs("\n", stderr);

	for (int i = vm.frameCount - 1; i >= 0; i--)
	{
		CallFrame * frame = &vm.frames[i];
		ObjFunction * function = frame->closure->function;

		unsigned instruction = (unsigned)(frame->ip - function->chunk.aryB - 1);
		unsigned line = getLine(&function->chunk, instruction);

		fprintf(stderr, "[line %u] in ", line);

		if (function->name == NULL)
		{
			fprintf(stderr, "script\n");
		}
		else
		{
			fprintf(stderr, "%s()\n", function->name->aChars);
		}
	}

	resetStack();
}

static void defineNative(const char * name, NativeFn function)
{
	push(OBJ_VAL(copyString(name, (int)strlen(name))));
	push(OBJ_VAL(newNative(function)));
	tableSet(&vm.globals, AS_STRING(peek(1)), peek(0));
	pop();
	pop();
}

static bool call(ObjClosure * closure, int argCount)
{
	if (argCount != closure->function->arity)
	{
		runtimeError("Expected %d arguments but got %d.", closure->function->arity, argCount);
		return false;
	}

	if (vm.frameCount == FRAMES_MAX)
	{
		runtimeError("Stack overflow.");
		return false;
	}

	CallFrame * frame = &vm.frames[vm.frameCount++];
	frame->closure = closure;
	frame->ip = closure->function->chunk.aryB;
	frame->slots = vm.stackTop - argCount - 1;

	return true;
}

static bool callValue(Value callee, int argCount)
{
	if (IS_OBJ(callee))
	{
		switch (OBJ_TYPE(callee))
		{
			case OBJ_CLOSURE:
				return call(AS_CLOSURE(callee), argCount);

			case OBJ_BOUND_METHOD:
			{
				ObjBoundMethod* bound = AS_BOUND_METHOD(callee);
				vm.stackTop[-argCount - 1] = bound->receiver;
				return call(bound->method, argCount);
			}

			case OBJ_NATIVE:
			{
				NativeFn native = AS_NATIVE(callee);

				if (LIKELY(native(argCount, vm.stackTop - argCount)))
				{
					vm.stackTop -= argCount;
					return true;
				}
				else
				{
					// BB (matthewp) Relax this restriction
					ASSERT(IS_STRING(vm.stackTop[-argCount - 1]));
					runtimeError(AS_CSTRING(vm.stackTop[-argCount - 1]));
					return false;
				}
			}

			case OBJ_CLASS:
			{
				ObjClass* klass = AS_CLASS(callee);
				vm.stackTop[-argCount - 1] = OBJ_VAL(newInstance(klass));
				if (klass->init)
				{
					return call(klass->init, argCount);
				}
				else if (argCount != 0)
				{
					runtimeError("Expected 0 arguments but got %d.", argCount);
					return false;
				}
				return true;
			}

			default:
				// Non-callable object type;
				break;
		}
	}

	runtimeError("Can only call functions and classes.");
	return false;
}

static bool invokeFromClass(ObjClass* klass, ObjString* name, int argCount)
{
	Value method;
	if (!tableGet(&klass->methods, name, &method))
	{
		runtimeError("Undefined property '%s'.", name->aChars);
		return false;
	}

	return call(AS_CLOSURE(method), argCount);
}

static bool invoke(ObjString* name, int argCount)
{
	Value receiver = peek(argCount);

	if (!IS_INSTANCE(receiver))
	{
		runtimeError("Only instances have methods.");
		return false;
	}

	ObjInstance* instance = AS_INSTANCE(receiver);

	Value value;
	if (tableGet(&instance->fields, name, &value))
	{
		vm.stackTop[-argCount - 1] = value;
		return callValue(value, argCount);
	}

	return invokeFromClass(instance->klass, name, argCount);
}

static bool bindMethod(ObjClass* klass, ObjString* name)
{
	Value method;
	if (!tableGet(&klass->methods, name, &method))
		return false;

	ObjBoundMethod* bound = newBoundMethod(peek(0), AS_CLOSURE(method));
	pop();
	push(OBJ_VAL(bound));
	return true;
}

static ObjUpvalue * captureUpvalue(Value * local)
{
	ObjUpvalue * prevUpvalue = NULL;
	ObjUpvalue * upvalue = vm.openUpvalues;

	while (upvalue != NULL && upvalue->location > local)
	{
		prevUpvalue = upvalue;
		upvalue = upvalue->next;
	}

	if (upvalue != NULL && upvalue->location == local) return upvalue;

	ObjUpvalue * createdUpvalue = newUpvalue(local);
	createdUpvalue->next = upvalue;

	if (prevUpvalue == NULL)
	{
		vm.openUpvalues = createdUpvalue;
	}
	else
	{
		prevUpvalue->next = createdUpvalue;
	}

	return createdUpvalue;
}

static void closeUpvalues(Value * last)
{
	while (vm.openUpvalues != NULL && vm.openUpvalues->location >= last)
	{
		ObjUpvalue * upvalue = vm.openUpvalues;
		upvalue->closed = *upvalue->location;
		upvalue->location = &upvalue->closed;
		vm.openUpvalues = upvalue->next;
	}
}

static void defineMethod(ObjString* name)
{
	Value method = peek(0);
	ObjClass* klass = AS_CLASS(peek(1));
	tableSet(&klass->methods, name, method);
	if (name == vm.initString)
	{
		klass->init = AS_CLOSURE(method);
	}
	pop();
}

static InterpretResult run(void)
{
	// NOTE (matthewp) frame->ip MUST be restored whenever leaving this function in case outside code wants to
	//  access the frame's current instruction pointer. The benefits here (>10% performance in simple tests) seem
	//  worth the extra complexity

	CallFrame * frame = &vm.frames[vm.frameCount - 1];
	register uint8_t * ip = frame->ip;

	// BB (matthewp) Avoid extra push-pop operations by modifying the top of the stack in-place
	//  Example: In unary negation, instead of: push(negate(pop())), do negate(peek())

#define RETURN_RUNTIME_ERR(fmt, ...) \
	do { \
		frame->ip = ip; \
		runtimeError(fmt, ##__VA_ARGS__); \
		return INTERPRET_RUNTIME_ERROR; \
	} while (false)

#define READ_BYTE() (*ip++)
#define READ_SHORT() (ip += 2, (uint16_t)((ip[-2] << 8) | ip[-1]))
#define READ_U24() (ip += 3, (uint32_t)((ip[-3] << 16) | (ip[-2] << 8) | ip[-1]))
#define READ_CONSTANT(short) frame->closure->function->chunk.aryValConstants[(short) ? READ_BYTE() : READ_U24()]
#define READ_STRING(short) AS_STRING(READ_CONSTANT(short))
#define BINARY_OP(valueType, op) \
	do { \
		if (!IS_NUMBER(peek(0)) || !IS_NUMBER(peek(1))) { \
			RETURN_RUNTIME_ERR("Operands must be numbers."); \
		} \
		double b = AS_NUMBER(pop()); \
		double a = AS_NUMBER(pop()); \
		push(valueType(a op b)); \
	} while(false)

	for (;;)
	{
#if DEBUG_TRACE_EXECUTION
		printf("          ");
		for (Value* slot = vm.stack; slot < vm.stackTop; slot++)
		{
			printf("[ ");
			printValue(*slot);
			printf(" ]");
		}
		printf("\n");
		disassembleInstruction(&frame->closure->function->chunk, (unsigned)(ip - frame->closure->function->chunk.aryB));
#endif
		uint8_t op;
		switch (op = READ_BYTE())
		{
			case OP_CONSTANT:
			case OP_CONSTANT_LONG:
				push(READ_CONSTANT(op == OP_CONSTANT));
				break;

			case OP_NIL: push(NIL_VAL); break;
			case OP_TRUE: push(BOOL_VAL(true)); break;
			case OP_FALSE: push(BOOL_VAL(false)); break;
			case OP_POP: pop(); break;

			case OP_POPN:
			{
				uint32_t num = READ_BYTE() + 2;
				while (num--) pop();
				break;
			}

			case OP_GET_LOCAL:
			{
				uint8_t slot = READ_BYTE();
				push(frame->slots[slot]);
				break;
			}

			case OP_GET_LOCAL_LONG:
			{
				uint32_t slot = READ_U24();
				push(frame->slots[slot]);
				break;
			}

			case OP_SET_LOCAL:
			{
				uint8_t slot = READ_BYTE();
				frame->slots[slot] = peek(0);
				break;
			}

			case OP_SET_LOCAL_LONG:
			{
				uint32_t slot = READ_U24();
				frame->slots[slot] = peek(0);
				break;
			}

			// TODO: Improve global lookup by avoiding hash-table. Consider assigning every
			//  global a unique (linear) ID during compilation and writing that to the bytecode
			//  stream. Lookup becomes just an index into an array (need an extra bool to make
			//  sure it's actually been defined already?).

			case OP_GET_GLOBAL:
			case OP_GET_GLOBAL_LONG:
			{
				ObjString * name = READ_STRING(op == OP_GET_GLOBAL);
				Value value;
				if (!tableGet(&vm.globals, name, &value))
				{
					RETURN_RUNTIME_ERR("Undefined variable '%s'.", name->aChars);
				}
				push(value);
				break;
			}

			case OP_DEFINE_GLOBAL:
			case OP_DEFINE_GLOBAL_LONG:
			{
				ObjString * name = READ_STRING(op == OP_DEFINE_GLOBAL);
				if (!tableSetIfNew(&vm.globals, name, peek(0)))
				{
					RETURN_RUNTIME_ERR("Global named '%s' already exists.", name->aChars);
				}
				pop();
				break;
			}

			case OP_SET_GLOBAL:
			case OP_SET_GLOBAL_LONG:
			{
				ObjString * name = READ_STRING(op == OP_SET_GLOBAL);
				if (tableSet(&vm.globals, name, peek(0)))
				{
					tableDelete(&vm.globals, name);
					RETURN_RUNTIME_ERR("Undefined variable '%s'.", name->aChars);
				}
				break;
			}

			case OP_GET_UPVALUE:
			{
				uint8_t slot = READ_BYTE();
				push(*frame->closure->upvalues[slot]->location);
				break;
			}

			case OP_GET_UPVALUE_LONG:
			{
				uint32_t slot = READ_U24();
				push(*frame->closure->upvalues[slot]->location);
				break;
			}

			case OP_SET_UPVALUE:
			{
				uint8_t slot = READ_BYTE();
				*frame->closure->upvalues[slot]->location = peek(0);
				break;
			}

			case OP_SET_UPVALUE_LONG:
			{
				uint32_t slot = READ_U24();
				*frame->closure->upvalues[slot]->location = peek(0);
				break;
			}

			case OP_GET_PROPERTY:
			case OP_GET_PROPERTY_LONG:
			{
				Value p = peek(0);

				if (!IS_INSTANCE(p))
				{
					RETURN_RUNTIME_ERR("Trying to access a property on a non-instance object.");
				}

				ObjInstance* instance = AS_INSTANCE(p);
				ObjString* name = READ_STRING(op == OP_GET_PROPERTY);

				Value value;
				if (tableGet(&instance->fields, name, &value))
				{
					pop();
					push(value);
					break;
				}

				if (!bindMethod(instance->klass, name))
				{
					RETURN_RUNTIME_ERR("Undefined property '%s'.", name->aChars);
				}

				break;
			}

			case OP_SET_PROPERTY:
			case OP_SET_PROPERTY_LONG:
			{
				Value p = peek(1);

				if (!IS_INSTANCE(p))
				{
					RETURN_RUNTIME_ERR("Trying to set a property on a non-instance object.");
				}

				ObjInstance* instance = AS_INSTANCE(p);
				ObjString* name = READ_STRING(op == OP_SET_PROPERTY);

				tableSet(&instance->fields, name, peek(0));

				Value value = pop();
				pop();
				push(value);
				break;
			}

			case OP_GET_SUPER:
			case OP_GET_SUPER_LONG:
			{
				ObjString* name = READ_STRING(op == OP_GET_SUPER);
				ObjClass* superclass = AS_CLASS(pop());
				if (!bindMethod(superclass, name))
				{
					RETURN_RUNTIME_ERR("Undefined method on '%s' superclass.", name->aChars);
				}
				break;
			}

			case OP_EQUAL:
			{
				Value b = pop();
				Value a = pop();
				push(BOOL_VAL(valuesEqual(a, b)));
				break;
			}

			case OP_GREATER: BINARY_OP(BOOL_VAL, >); break;
			case OP_LESS: BINARY_OP(BOOL_VAL, <); break;

			case OP_NEGATE:
				if (!IS_NUMBER(peek(0)))
				{
					RETURN_RUNTIME_ERR("Operand must be a number.");
				}

				push(NUMBER_VAL(-AS_NUMBER(pop())));
				break;

			case OP_ADD:
			{
				if (IS_STRING(peek(0)) && IS_STRING(peek(1)))
				{
					concatenate();
				}
				else if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1)))
				{
					double b = AS_NUMBER(pop());
					double a = AS_NUMBER(pop());
					push(NUMBER_VAL(a + b));
				}
				else
				{
					RETURN_RUNTIME_ERR("Operands must be two numbers or two strings");
				}
				break;
			}
			case OP_SUBTRACT: BINARY_OP(NUMBER_VAL, -); break;
			case OP_MULTIPLY: BINARY_OP(NUMBER_VAL, *); break;
			case OP_DIVIDE: BINARY_OP(NUMBER_VAL, /); break;

			case OP_NOT: push(BOOL_VAL(isFalsey(pop()))); break;

			case OP_PRINT:
			{
				printValue(pop());
				printf("\n");
				break;
			}

			case OP_JUMP:
			{
				uint16_t offset = READ_SHORT();
				ip += offset;
				break;
			}

			case OP_JUMP_IF_FALSE:
			{
				uint16_t offset = READ_SHORT();
				if (isFalsey(peek(0))) ip += offset;
				break;
			}

			case OP_LOOP:
			{
				uint16_t offset = READ_SHORT();
				ip -= offset;
				break;
			}

			case OP_CALL:
			{
				int argCount = READ_BYTE();
				frame->ip = ip;

				if (!callValue(peek(argCount), argCount))
					return INTERPRET_RUNTIME_ERROR;

				frame = &vm.frames[vm.frameCount - 1];
				ip = frame->ip;
				break;
			}

			case OP_INVOKE:
			case OP_INVOKE_LONG:
			{
				ObjString * method = READ_STRING(op == OP_INVOKE);
				int argCount = READ_BYTE();
				frame->ip = ip;

				if (!invoke(method, argCount))
					return INTERPRET_RUNTIME_ERROR;

				frame = &vm.frames[vm.frameCount - 1];
				ip = frame->ip;

				break;
			}

			case OP_SUPER_INVOKE:
			case OP_SUPER_INVOKE_LONG:
			{
				ObjString* method = READ_STRING(op == OP_SUPER_INVOKE);
				int argCount = READ_BYTE();
				ObjClass * superclass = AS_CLASS(pop());
				frame->ip = ip;

				if (!invokeFromClass(superclass, method, argCount))
					return INTERPRET_RUNTIME_ERROR;

				frame = &vm.frames[vm.frameCount - 1];
				ip = frame->ip;

				break;
			}

			case OP_CLOSURE:
			case OP_CLOSURE_LONG:
			{
				ObjFunction * function = AS_FUNCTION(READ_CONSTANT(op == OP_CLOSURE));
				ObjClosure * closure = newClosure(function);
				push(OBJ_VAL(closure));

				for (int i = 0; i < closure->upvalueCount; ++i)
				{
					uint8_t flag = READ_BYTE();
					bool isLocal = flag & 0x1;
					bool isLong = flag & 0x2;
					uint32_t index = (isLong) ? READ_U24() : READ_BYTE();

					if (isLocal)
					{
						closure->upvalues[i] = captureUpvalue(frame->slots + index);
					}
					else
					{
						closure->upvalues[i] = frame->closure->upvalues[index];
					}
				}
				break;
			}

			case OP_CLOSE_UPVALUE:
			{
				closeUpvalues(vm.stackTop - 1);
				pop();
				break;
			}

			case OP_RETURN:
			{
				Value result = pop();

				closeUpvalues(frame->slots);

				vm.frameCount--;
				if (vm.frameCount == 0)
				{
					pop();
					return INTERPRET_OK;
				}

				vm.stackTop = frame->slots;
				push(result);

				frame = &vm.frames[vm.frameCount - 1];
				ip = frame->ip;
				break;
			}

			case OP_CLASS:
			case OP_CLASS_LONG:
				push(OBJ_VAL(newClass(READ_STRING(op == OP_CLASS))));
				break;

			case OP_INHERIT:
			{
				Value superclass = peek(1);
				if (!IS_CLASS(superclass))
				{
					RETURN_RUNTIME_ERR("Superclass must be a class.");
				}

				ObjClass* subclass = AS_CLASS(peek(0));
				tableAddAll(&AS_CLASS(superclass)->methods, &subclass->methods);
				pop();
				break;
			}

			case OP_METHOD:
			case OP_METHOD_LONG:
				defineMethod(READ_STRING(op == OP_METHOD));
				break;
		}
	}

#undef RETURN_RUNTIME_ERR
#undef READ_BYTE
#undef READ_SHORT
#undef READ_U24
#undef READ_CONSTANT
#undef READ_STRING
#undef BINARY_OP
}
