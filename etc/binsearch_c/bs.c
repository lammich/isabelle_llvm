#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

typedef uint64_t elem_t;

typedef struct {
  int64_t len;
  elem_t *data;
} larray_t;

int64_t bin_search (larray_t xs, elem_t x) {
  int64_t l = 0;
  int64_t h = xs.len;
  
  while (l<h) {
    int64_t m = l + (h-l) / 2;
    if (xs.data[m] < x) l=m+1;
    else h=m;
  }
  
  return l;
}


int main(int argc, char **argv) {

  if (argc != 2) {printf("usage: bs <size>\n"); exit(1);}
  
  int64_t len = strtol(argv[1],NULL,10);

  elem_t* ptr = (elem_t*)calloc(len,sizeof(elem_t));
  
  for (int64_t i=0;i<len;++i) ptr[i] = ((elem_t)i) * 5;
  
  larray_t arr = { len, ptr };
  
  clock_t time = clock();
  
  int64_t i = 0;
  
  for (elem_t x=0;x<5*len;x+=2)
    i += bin_search(arr,x);
  
  time = clock() - time;  
    
  printf("Time: %fs, (idx checksum: %ld)\n",((double)time)/CLOCKS_PER_SEC,i);
  
  uint64_t time_ms = ((double)time)/CLOCKS_PER_SEC * 1000;
  printf("@ %ld %ld\n",len,time_ms);
  
}
