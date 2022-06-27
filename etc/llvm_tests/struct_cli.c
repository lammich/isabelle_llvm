#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>


typedef union {
    double f0;
    struct {
      char f0;
      int32_t f1;
      int32_t f2;
    }f1;
  } test ;


typedef struct {
  char a;
  struct {
    char b;
    int64_t c;
  };
} test1;

typedef struct {
  char a;
  char b;
  int64_t c;
} test2;


size_t s1 = sizeof(struct{char a;});
size_t s2 = sizeof(test);
test t2;


typedef union {
  struct {
    int32_t a1;
    int32_t a2;
    int32_t a3;
  };
  struct {
    int64_t b;
  };
} testXX;

test create_test(void);

// int64_t read_test(test a) {
//   return a.c;
// }


// test create_test2() {
//   test a;
//   a.l=0;
//   a.c=0;
//   a.d=0;
//   return a;
// }

void foo(testXX *t) {
  testXX tt;

  tt.a1=-1;
  tt.b=42;

  *t=tt;
}


int main(int argc, char **argv) {
//   test a;
  testXX aXX;

  aXX.a1=-1;
  aXX.b=42;

//   a.l=-1;
//   a.c=-1;
//   a.d=-1;
// //  a.data=(void*)0xFEFEFEFEFEFEFEFE;

//   printf("%ld,%ld,%ld\n",a.l,a.c,a.d);
  
  
//   a = create_test();

//   printf("%ld,%ld,%ld\n",a.l,a.c,a.d);
  

  return 0;
}
