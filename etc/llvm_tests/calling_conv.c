#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>


typedef struct {
  char a;
  char b;
  char c;
} s1;

typedef struct {
  uint64_t a;
  uint64_t b;
} s2;

typedef struct {
  uint64_t a;
  uint64_t b;
  uint64_t c;
} s3;

char f1(s1 x) {
    return x.b;
}

uint64_t f2(s2 x) {
    return x.b;
}

uint64_t f3(s3 x) {
    return x.b;
}

int main(int argc, char **argv) {


  return 0;
}


