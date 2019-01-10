#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>


int32_t euclid(int32_t, int32_t);


int32_t euclid2(int32_t a, int32_t b) {
  while (a!=b) {
    if (a<=b) b=b-a; else a=a-b;
  }
  return a;
}


int main (int argc, char** argv) {
  
  if (argc != 3) {printf("Expecting two arguments\n"); exit(1);}
  
  int32_t a = strtoul (argv[1],NULL,10);
  int32_t b = strtoul (argv[2],NULL,10);
  
  printf ("gcd(%d,%d) = %d\n", a, b, euclid(a,b));
}



