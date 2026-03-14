#ifndef CIVET_CHIBICC_PUBLIC_H
#define CIVET_CHIBICC_PUBLIC_H
#include "../chibicc.h"
void civet_add_include_path(const char *path);
void civet_clear_include_paths(void);
void civet_set_base_file(const char *path);
void chibicc_reset(void);
#endif
