#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

void error(char const*) __attribute__((noreturn));
inline void error(char const* msg) {
  printf("Error: %s\n",msg);
  exit(1);
}
