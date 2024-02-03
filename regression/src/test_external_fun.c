#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "test_external_fun.h"

uint64_t external_fun(uint64_t n) {
  return n+1;
}


int main(int argc, char **argv) {
  assert (uses_external_fun(42) == 44);
  
  return 0;
}
