#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include "open_list.h"

int main(int argc, char **argv) {
  os_list l = os_empty();
  
  for (uint64_t x=0;x<100;++x)
    l = os_prepend(x,l);

  l = os_reverse(l);

  l = os_rem (42,l);

  assert (!os_is_empty(l));

  for (uint64_t x = 0; x<100; ++x ) {
    if (x!=42) {
      pop_result res;
      os_pop(l,&res);
      l=res.list;

      assert (res.data == x);
    }
  }

  assert (os_is_empty(l));

}

