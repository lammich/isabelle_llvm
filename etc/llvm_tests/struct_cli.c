#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>


typedef struct {
  int64_t l;
  int64_t c;
  int64_t d;
  //int64_t *data;
} test;


test create_test(void);

int64_t read_test(test a) {
  return a.c;
}


test create_test2() {
  test a;
  a.l=0;
  a.c=0;
  a.d=0;
  return a;
}


int main(int argc, char **argv) {
  test a;
  
  a.l=-1;
  a.c=-1;
  a.d=-1;
//  a.data=(void*)0xFEFEFEFEFEFEFEFE;

  printf("%ld,%ld,%ld\n",a.l,a.c,a.d);
  
  
  a = create_test();

  printf("%ld,%ld,%ld\n",a.l,a.c,a.d);
  

  return 0;
}
