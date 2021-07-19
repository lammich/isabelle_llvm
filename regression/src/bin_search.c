#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include "bin_search.h"

void bin_search_test(larray_t arr, elem_t e) {
  int64_t j = bin_search(&arr,e);

  int64_t n = arr.len;
  elem_t *a = arr.data;

  if (j<n) {
    assert(e<=a[j]);
    assert(j==0 || !(e<=a[j-1]));
  } else {
    assert(j==n);
    assert(!(e<=a[j-1]));
  }
}

int main(int argc, char **argv) {

  const size_t n=1000;
  elem_t elems[n];

  for (size_t i=0;i<n;++i) elems[i]=i*2;

  larray_t arr = {n,(elem_t*)elems};

  bin_search_test(arr,n*3);

  for (size_t i=0;i<n;++i) {
    bin_search_test(arr,i);
  }

}

