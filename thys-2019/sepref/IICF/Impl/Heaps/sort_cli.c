#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>


typedef struct {
  int64_t l;
  int64_t c;
  int64_t *data;
} array_list;

extern array_list sort(array_list);
extern array_list arl_new();
extern array_list arl_push_back(array_list,int64_t);


int main(int argc, char **argv) {
  array_list a;
  a.l=0;
  a.c=0;
  a.data=0;
  
  a = arl_new();
  
  printf("%ld, %ld\n",a.l,a.c);
  
  arl_push_back(a,42);
  
  // for (int i=0;i<5;i++) a=arl_push_back(a,i);
  
  return 0;
}

