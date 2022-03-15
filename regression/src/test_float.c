#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>
#include "test_float.h"

#include "double_lib.c"

float c_test_float(float a, float b) {
  return fmodf(sqrtf(a*a + b*b) - a/b, a+b) + .5;
}

void test(float a, float b) {

  assert(isnan(a) || i2f(f2i(a)) == a);

  float rv = c_test_float(a,b);
  float v = test_float(a,b);

//  printf("%a,%a -> %a | %a\n",a,b,rv,v);


  assert(f2i(v) == f2i(rv));

  assert(isnan(v) && isnan(rv) || v==rv );
}

int main(int argc, char **argv) {

  test(42,15);

  srand(42);

//   for (size_t i=0;i<100; ++i) {
//     uint64_t x = ru64();
//     printf("%lx %.10e\n",x,i2d(x));
//   }

  for (size_t i=0;i<1000000; ++i)
    test(rd1(),rd1());
}

