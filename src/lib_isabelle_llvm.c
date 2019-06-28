#include <stdlib.h>
#include <stdio.h>

void isabelle_llvm_abort() {
  printf("%s\n","Isabelle-LLVM (abort): Dynamic check failed.");
  abort();
}

void isabelle_llvm_abort_msg(char *msg) {
  printf("Isabelle-LLVM (abort): %s\n",msg);
  abort();
}

char* isabelle_llvm_calloc(size_t n, size_t m) {
  // printf("calloc(%ld,%ld)",n,m);
  char *res = calloc(n,m);
  if (!res) isabelle_llvm_abort_msg("Out of memory");
  return res;
}

void isabelle_llvm_free(char *p) {
  free(p);
}

