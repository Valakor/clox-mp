//
//  common.h
//  clox
//
//  Created by Matthew Pohlmann on 2/19/18.
//  Copyright © 2018 Matthew Pohlmann. All rights reserved.
//

#pragma once

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>



#ifdef _MSC_VER
#define PRINTF_LIKE(...)
#define LIKELY(f) (f)
#define UNLIKELY(f) (f)
#define FUNCTION_PRETTY __FUNCSIG__
#define TARGET_WINDOWS 1
#define TARGET_MAC 0
#else
#define PRINTF_LIKE(iFormat, iArgs) __attribute__((format(printf, iFormat, iArgs)))
#define LIKELY(f) __builtin_expect(!!(f), 1)
#define UNLIKELY(f) __builtin_expect(!!(f), 0)
#define FUNCTION_PRETTY __PRETTY_FUNCTION__
#define TARGET_WINDOWS 0
#define TARGET_MAC 1
#endif

#if DEBUG || _DEBUG
#if TARGET_WINDOWS
	#define DEBUG_BREAK() __debugbreak()
#else
	#define DEBUG_BREAK() __builtin_debugtrap()
#endif

	void DoAssert(const char * file, int line, const char * function, const char * format, ...) PRINTF_LIKE(4, 5);

	#define ASSERT_MACRO(f, format, ...) \
		(void)(LIKELY(!!(f)) || (DoAssert(__FILE__, __LINE__, FUNCTION_PRETTY, format, ##__VA_ARGS__), DEBUG_BREAK(), 0))

	#define ASSERT(f) ASSERT_MACRO(f, #f)
	#define ASSERTMSG(f, format, ...) ASSERT_MACRO(f, format, ##__VA_ARGS__)
#else
	#define DEBUG_BREAK() (void)0

	#define ASSERT(...) (void)0
	#define ASSERTMSG(...) (void)0
#endif

#ifndef DEBUG_TRACE_EXECUTION
#define DEBUG_TRACE_EXECUTION 0
#endif

#ifndef DEBUG_PRINT_CODE
#define DEBUG_PRINT_CODE 0
#endif

#ifndef DEBUG_STRESS_GC
#define DEBUG_STRESS_GC 0
#endif

#ifndef DEBUG_LOG_GC
#define DEBUG_LOG_GC 0
#endif

#ifndef DEBUG_ALLOC
#define DEBUG_ALLOC (DEBUG || _DEBUG)
#endif

#define CASSERT(f) static_assert(f, #f)
#define CASSERTMSG(f, msg) static_assert(f, msg)
#define UNUSED(x) (void)(x)

#define MIN(a, b) ((a) <= (b) ? (a) : (b))
#define MAX(a, b) ((a) >= (b) ? (a) : (b))

#define UINT8_COUNT (UINT8_MAX + 1U)

#define UINT24_MAX 16777215U
#define UINT24_COUNT (UINT24_MAX + 1U)

#define IS_POW2(n) ((n) && (((n) & ((n) - 1)) == 0))
