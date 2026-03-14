/* Originally from chibicc by Rui Ueyama
   https://github.com/rui314/chibicc

   Copyright (c) 2019 Rui Ueyama

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.

   Modified for Civet: arena allocation, global state reset.  */

#include "chibicc.h"
#include "arena.h"

void strarray_push(StringArray *arr, char *s) {
  if (!arr->data) {
    arr->data = arena_alloc(8 * sizeof(char *));
    arr->capacity = 8;
  }

  if (arr->capacity == arr->len) {
    int new_cap = arr->capacity * 2;
    char **new_data = arena_alloc(new_cap * sizeof(char *));
    memcpy(new_data, arr->data, arr->capacity * sizeof(char *));
    arr->data = new_data;
    arr->capacity = new_cap;
  }

  arr->data[arr->len++] = s;
}

// Takes a printf-style format string and returns a formatted string.
char *format(char *fmt, ...) {
  // First pass: determine required length.
  va_list ap;
  va_start(ap, fmt);
  int len = vsnprintf(NULL, 0, fmt, ap);
  va_end(ap);

  // Allocate in arena and format directly into it.
  char *arena_buf = arena_alloc(len + 1);
  va_start(ap, fmt);
  vsnprintf(arena_buf, len + 1, fmt, ap);
  va_end(ap);
  return arena_buf;
}

char *arena_strndup(const char *s, size_t n) {
  char *p = arena_alloc(n + 1);
  memcpy(p, s, n);
  p[n] = '\0';
  return p;
}

char *arena_strdup(const char *s) {
  return arena_strndup(s, strlen(s));
}
