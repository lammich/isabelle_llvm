#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


void arraycpy(char *dst, char *src, int64_t n);

void arraycp2(char *dst, char *src, int64_t n) {
  int64_t i=0;
  
  while (i<n) {
    dst[i] = src[i];
    ++i;
  }
}


int main (int argc, char** argv) {
  
  int64_t size = 1000 * 1024*1024;
  
  char *x = calloc(1, size);
  char *y = calloc(1, size);
  
  memset(y,27,size);
  arraycpy(x,y,size);
  
  int j=0;
  for (int i=0;i<size;++i) j+=x[i];
  
  return j;
}



