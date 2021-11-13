#error obsolete, replaced by sorting.cpp

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include "sorting.h"


llstring str(const char *s) {
  llstring res;
  str_init(&res);

  for (;*s;++s) str_append(&res,*s);

  return res;
}

char strleq(llstring a, llstring b) {
  return ! (llstrcmp(&b,&a));
}

void test_int() {
  const size_t n = 30;
  uint64_t init[n] = {32,45,12,97,4534,248,457,2145,57623,12,32,45,12,97,4534,248,457,2145,57623,12,32,45,12,97,4534,248,457,2145,57623,12};

  uint64_t a[n];

  for (size_t i=0;i<n;++i) a[i] = init[i];
  introsort(a,0,n);
  for (size_t i=1;i<n;++i) assert(a[i-1]<=a[i]);

  for (size_t i=0;i<n;++i) a[i] = init[i];
  pdqsort(a,0,n);
  for (size_t i=1;i<n;++i) assert(a[i-1]<=a[i]);

}

void test_str() {
  const size_t n = 30;
  llstring init[n] = {
    str("dfga"),str("e89yf9"),str("45f"),str(""),str("pdft214"),str(".abxd"),str("-1923"),str("8hdjgsha"),str("122nnsd"),str("1908bud"),
    str("dfsa"),str("jklj984"),str("kfj48"),str(";';k;76"),str("894hvvjb"),str("dj289"),str("asrgt4"),str("djc0943"),str("bhc3byu"),str("3215413-45"),
    str("jkghjk"),str("vv"),str("b"),str("0-5296"),str("1,nm23"),str("18n77"),str("90mav"),str("2890"),str("nv94"),str("mc n3789")
  };

  llstring a[n];

  for (size_t i=0;i<n;++i) a[i] = init[i];
  str_introsort(a,0,n);
  for (size_t i=1;i<n;++i) assert(strleq(a[i-1],a[i]));

  for (size_t i=0;i<n;++i) a[i] = init[i];
  str_pdqsort(a,0,n);
  for (size_t i=1;i<n;++i) assert(strleq(a[i-1],a[i]));

  for (size_t i=0;i<n;++i) str_free(&(init[i]));

}


int main(int argc, char **argv) {
  test_int();
  test_str();
}

