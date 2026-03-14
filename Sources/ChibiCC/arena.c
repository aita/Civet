/* Arena (bump) allocator for Civet.
   All allocations are zero-initialized to match calloc() semantics.
   arena_reset() frees all blocks except the first, ready for reuse.  */

#include "arena.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BLOCK_SIZE (64 * 1024)  /* 64 KiB per block */
#define ALIGN     16            /* allocation alignment */

typedef struct Block {
    struct Block *next;
    size_t capacity;
    size_t used;
    char data[];
} Block;

static Block *head = NULL;
static Block *current = NULL;

static Block *new_block(size_t min_size) {
    size_t cap = min_size > BLOCK_SIZE ? min_size : BLOCK_SIZE;
    Block *b = malloc(sizeof(Block) + cap);
    if (!b) {
        fprintf(stderr, "arena: out of memory\n");
        exit(1);
    }
    b->next = NULL;
    b->capacity = cap;
    b->used = 0;
    return b;
}

void *arena_alloc(size_t size) {
    /* Round up to alignment boundary */
    size = (size + ALIGN - 1) & ~(ALIGN - 1);

    if (!current) {
        head = current = new_block(size);
    }

    if (current->used + size > current->capacity) {
        Block *b = new_block(size);
        current->next = b;
        current = b;
    }

    void *ptr = current->data + current->used;
    current->used += size;
    memset(ptr, 0, size);
    return ptr;
}

void arena_reset(void) {
    if (!head) return;

    /* Free all blocks except the first (reuse head) */
    Block *b = head->next;
    while (b) {
        Block *next = b->next;
        free(b);
        b = next;
    }
    head->next = NULL;
    head->used = 0;
    current = head;
}

void arena_destroy(void) {
    Block *b = head;
    while (b) {
        Block *next = b->next;
        free(b);
        b = next;
    }
    head = current = NULL;
}
