#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include "kmp.h"


string str(const char *s) {
  string res = {strlen(s),(char *)s};
  return res;
}

void test_kmp(string a, string b) {

//   int64_t la=a.len;
//   int64_t lb=b.len;

  char *da = a.str;
  char *db = b.str;

  int64_t i = kmp(&b,&a);

  char *testres = strstr(da,db);

  if (testres) {
    // printf("%ld vs. %ld\n",i,testres - da);
    assert(i == testres - da);
  } else {
    assert(i==-1);
  }

}

int main(int argc, char **argv) {

  string master=str("0123456789ABCDEABCDEBANANAS");

  test_kmp(master,str("456"));
  test_kmp(master,str("ANA"));
  test_kmp(master,str("ANAS"));
  test_kmp(master,str(""));
  test_kmp(master,str("ABCE"));
  test_kmp(str(""),str("4"));
  test_kmp(str(""),str(""));


}

