/* Arena allocator for Civet's chibicc-based parser.
   Replaces individual calloc() calls with bulk arena allocation.
   All memory is freed at once via arena_reset() after the Swift side
   has copied the AST data.  */

#pragma once
#include <stddef.h>

void *arena_alloc(size_t size);
void  arena_reset(void);
void  arena_destroy(void);
