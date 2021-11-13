#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>
#include <immintrin.h>
#include <avx512fintrin.h>
#include "test_avx512f.h"

#include "double_lib.c"


double fmadd_sd(double a, double b, double c) {
  return _mm_cvtsd_f64(_mm_fmadd_sd(_mm_set_sd(a), _mm_set_sd(b), _mm_set_sd(c)));
}

double c_test_avx_fp(double a, double b) {
  return (sqrt(a*a + b*b) - a/b) + a;
}

double c_test_avx(double a, double b) {
  return (sqrt(fmadd_sd(b,b,a*a)) - a/b) + a;
}


void test_avx(double a, double b) {

//   printf("%.20f, %.20f\n",a,b);

  double rv_n = c_test_avx(a,b);
  double rv_fp = c_test_avx_fp(a,b);
  double t_n = test_avx512f_to_nearest(a,b);
  double t_up = test_avx512f_to_pinf(a,b);
  double t_down = test_avx512f_to_ninf(a,b);
  double t_z = test_avx512f_to_zero(a,b);

//   printf("t_n  = %.20e\nrv_n = %.20e\n",t_n,rv_n);

  assert (d2i(t_n) == d2i(rv_n));

  assert (nd(t_n) == nd(rv_n));

  // fix bounds, should they be nan
  if (isnan(t_down)) t_down=-INFINITY;
  if (isnan(t_up)) t_up=INFINITY;

  assert (isnan(rv_n) || t_down <= rv_n && rv_n <= t_up);
  assert (isnan(t_n) || t_down <= t_n && t_n <= t_up);
  assert (isnan(t_z) || t_down <= t_z && t_z <= t_up);
  assert (isnan(rv_fp) || t_down <= rv_fp && rv_fp <= t_up);

//   printf("%.30f\n%.30f\n%.30f\n%.30f\n%.30f\n",rv_n,t_n,t_up,t_down,t_z);

//   if (t_n != t_down && t_n != t_up) printf("d < n < u\n");
//   if (t_z != t_down && t_z != t_up) printf("d < z < u\n");
//   if (rv_n != rv_fp) printf("rv_n != rv_fp\n");


//   assert (t_z == t_up || t_z == t_down);
//   assert (t_n == t_up || t_n == t_down);

}



int main(int argc, char **argv) {

  test_avx( 20.34012319629086462669, 16.35112350729811936390 );

  test_avx(1,-167126871);
  test_avx(0.00001,-15.7347);

  srand(42);
  for (size_t i=0;i<1000000;++i) test_avx(rd1(),rd1());

}

