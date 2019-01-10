#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>


int64_t cr_big_al(int64_t);


int32_t euclid2(int32_t a, int32_t b) {
  while (a!=b) {
    if (a<=b) b=b-a; else a=a-b;
  }
  return a;
}


int main (int argc, char** argv) {
  
  if (argc != 2) {printf("Expecting one argument\n"); exit(1);}
  
  int64_t n = strtoul (argv[1],NULL,10);
  
  printf ("sum %ld = %ld\n", n, cr_big_al(n));
}



