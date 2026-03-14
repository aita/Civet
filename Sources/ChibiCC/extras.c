// Stubs for symbols defined in main.c and codegen.c which we don't compile.
#include "chibicc.h"
#include "arena.h"

// From codegen.c
int align_to(int n, int align) {
  return (n + align - 1) / align * align;
}

// From main.c
bool file_exists(char *path) {
  struct stat st;
  return !stat(path, &st);
}

// Global variables from main.c
StringArray include_paths = {};
bool opt_fpic;
bool opt_fcommon = true;
char *base_file;

void civet_add_include_path(const char *path) {
  strarray_push(&include_paths, (char *)path);
}

void civet_clear_include_paths(void) {
  include_paths.len = 0;
}

void civet_set_base_file(const char *path) {
  base_file = arena_strdup(path);
}

// Reset functions defined in each source file
extern void parse_reset(void);
extern void tokenize_reset(void);
extern void preprocess_reset(void);

void chibicc_reset(void) {
  parse_reset();
  tokenize_reset();
  preprocess_reset();
  // Free strdup'd include path strings before zeroing
  for (int i = 0; i < include_paths.len; i++)
    free(include_paths.data[i]);
  include_paths = (StringArray){};
  base_file = NULL;
  arena_reset();
}
