#include <cstdlib>
#include <cstdint>
#include <cassert>
#include <chrono>
#include <iostream>
#include <algorithm>
#include <vector>
#include <cmath>

extern "C" {
  #include "sorting.h"
}


size_t const N = 1000000;
size_t const STRLEN = 50;
size_t const NSTR = 500000;

using namespace std;




template <class D,class T> void check_sorted(vector<T> data, D comp) {
  assert (is_sorted(data.begin(), data.end(),comp));
}

template<typename A> void time_op(std::string name, A op) {
  auto start = std::chrono::system_clock::now();
  op();
  auto finish = std::chrono::system_clock::now();

  std::chrono::duration<double> duration = finish - start;

  std::cout<<"  "<<name<<"."<<"time: "<<round(duration.count()*1000)<<std::endl;
}

template<class IA, class compare, class Op>
void sort_test(string name, std::vector<IA> &A, compare comp, Op op, bool verify=true) {
  time_op(name, [&]{op(A);});

//   for (auto i : A) clog<<i<<" ";
//   clog<<endl;

  if (verify) check_sorted(A,comp);
}

void isa_introsort_uint(vector<uint64_t> &xs) {
  introsort(xs.data(),0,xs.size());
}

void isa_pdqsort_uint(vector<uint64_t> &xs) {
  pdqsort(xs.data(),0,xs.size());
}

void isa_parqsort_uint(vector<uint64_t> &xs) {
  par_sort(xs.data(),xs.size());
}

void isa_introsort_llstring(vector<llstring> &xs) {
  str_introsort(xs.data(),0,xs.size());
}

void isa_pdqsort_llstring(vector<llstring> &xs) {
  str_pdqsort(xs.data(),0,xs.size());
}

void isa_parqsort_llstring(vector<llstring> &xs) {
  str_par_sort(xs.data(),xs.size());
}



template <class Op> void sort_test_uint64(string name, Op op) {
  srand(1);

  vector<uint64_t> xs;
  for (size_t i=0;i<N;++i) xs.push_back(rand());
  sort_test(name, xs, less<uint64_t>(),op);
}


char rand_char() {
  size_t low=' ';
  size_t high='z';
  return low + (char)(rand() % (high-low));
}

llstring randstr() {
  size_t n = rand() % STRLEN;

  llstring res;
  str_init(&res);

  for (size_t i=0;i<n;++i) str_append(&res,rand_char());

  return res;
}

namespace std {
template<>
struct less<llstring>
{
   inline bool operator()(const llstring& k1, const llstring& k2) const
   {
//       return less<string>()(bcnv_str(k1), bcnv_str(k2));
     return llstrcmp((llstring*)&k1,(llstring*)&k2);
   }
};
}

template <class Op> void sort_test_llstring(string name, Op op) {
  srand(1);

  vector<llstring> xs;
  for (size_t i=0;i<NSTR;++i) xs.push_back(randstr());
  sort_test(name, xs, less<llstring>(),op);

  // Clean up
  for (auto i : xs) str_free(&i);
}






int main (int argc, char**argv) {

  sort_test_uint64("introsort-uint64",isa_introsort_uint);
  sort_test_uint64("pdqsort-uint64",isa_pdqsort_uint);
  sort_test_uint64("parqsort-uint64",isa_parqsort_uint);


  sort_test_llstring("introsort-llstring",isa_introsort_llstring);
  sort_test_llstring("pdqsort-llstring",isa_pdqsort_llstring);
  sort_test_llstring("parqsort-llstring",isa_parqsort_llstring);

  return 0;
}


