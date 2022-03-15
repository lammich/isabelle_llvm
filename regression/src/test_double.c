#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>
#include "test_double.h"

#include "double_lib.c"

double c_test_double(double a, double b) {
  return fmod (sqrt(a*a + b*b) - a/b, a+b) + .5;
}

void test(double a, double b) {

  assert(isnan(a) || i2d(d2i(a)) == a);

  double rv = c_test_double(a,b);
  double v = test_double(a,b);

//   printf("%e,%e\n",a,b);


  assert(d2i(v) == d2i(rv));

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

