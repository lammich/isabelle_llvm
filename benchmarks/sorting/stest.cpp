#include <algorithm>

#include <iostream>
#include <vector>

#include <boost/sort/common/time_measure.hpp>

uint64_t llcnt_partitionings=0;
uint64_t llcnt_partitions=0;


extern "C" {
  #include "introsort.h"
}


size_t NELEM = 100;

namespace bsc = boost::sort::common;

using bsc::time_point;
using bsc::now;
using bsc::subtract_time;


template <typename A> void print_range(A begin, A end) {

  uint64_t last=0;
  bool dots=false;
  for (auto i=begin;i<end;++i) {
      bool print = i==begin || last+1 != *i;

      if (!print && !dots) {std::cout<<"..."; dots=true; }

      if (print && dots) {std::cout<<last; dots=false; }

      if (print && i!=begin) std::cout<<" ";
      if (print) {std::cout<<*i; dots=false; }

      last=*i;
  }

  if (dots) {std::cout<<last; dots=false; }

  std::cout<<std::endl;
}

/*
template <typename A> void print_range(A begin, A end) {
  for (auto i=begin;i<end;++i) std::cout<<*i<<" ";
  std::cout<<std::endl;
}
*/

extern "C" {
  void incr_partitionings() {++llcnt_partitionings;}
  void incr_partitions() {++llcnt_partitions;}

  void print_partition(uint64_t *a, int64_t l, int64_t h) {
    print_range(a+l,a+h);
  }


}




namespace annot {


  uint64_t cnt_dlimit=0;
  uint64_t cnt_intro_loops=0;
  uint64_t cnt_partitionings=0;
  uint64_t cnt_partitions=0;


  void print_stats() {
    std::cout<<"**** STL ***"<<std::endl;
    std::cout<<"hit depth limit: "<<cnt_dlimit<<std::endl;
    std::cout<<"intro loops: "<<cnt_intro_loops<<std::endl;
    std::cout<<"partitionings: "<<cnt_partitionings<<std::endl;
    std::cout<<"partitions: "<<cnt_partitions<<std::endl;
    std::cout<<std::endl;
    std::cout<<"**** Isabelle-LLVM ***"<<std::endl;
    std::cout<<"partitionings: "<<llcnt_partitionings<<std::endl;
    std::cout<<"partitions: "<<llcnt_partitions<<std::endl;

  }



  /// This is a helper function for the sort routine.
  template<typename _RandomAccessIterator, typename _Size, typename _Compare>
    void
    __introsort_loop(_RandomAccessIterator __first,
		     _RandomAccessIterator __last,
		     _Size __depth_limit, _Compare __comp)
    {
      while (__last - __first > int(std::_S_threshold))
	{
          ++cnt_intro_loops;
	  if (__depth_limit == 0)
	    {
              ++cnt_dlimit;
	      std::__partial_sort(__first, __last, __last, __comp);
	      return;
	    }
	  --__depth_limit;
          print_range(__first,__last);
	  _RandomAccessIterator __cut =
	    std::__unguarded_partition_pivot(__first, __last, __comp);
          print_range(__first,__last);
          ++cnt_partitionings;
	  annot::__introsort_loop(__cut, __last, __depth_limit, __comp);
	  __last = __cut;
	}

      ++cnt_partitions;
    }

  // sort

  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    __sort(_RandomAccessIterator __first, _RandomAccessIterator __last,
	   _Compare __comp)
    {
      if (__first != __last)
	{
	  annot::__introsort_loop(__first, __last,
				std::__lg(__last - __first) * 2,
				__comp);
	  std::__final_insertion_sort(__first, __last, __comp);
	}
    }




  template<typename _RandomAccessIterator>
    inline void
    sort(_RandomAccessIterator __first, _RandomAccessIterator __last)
    {
      // concept requirements
      __glibcxx_function_requires(_Mutable_RandomAccessIteratorConcept<
	    _RandomAccessIterator>)
      __glibcxx_function_requires(_LessThanComparableConcept<
	    typename iterator_traits<_RandomAccessIterator>::value_type>)
      __glibcxx_requires_valid_range(__first, __last);
      __glibcxx_requires_irreflexive(__first, __last);

      annot::__sort(__first, __last, __gnu_cxx::__ops::__iter_less_iter());
    }




}

















template<typename A> void time_op(std::string name, A op) {
  auto start = now ();
  op();
  auto finish = now ();
  auto duration = subtract_time (finish, start);

  std::cout<<name<<": "<<duration<<std::endl;
}

int main (int argc, char *argv[])
{


  std::vector<uint64_t> A,B;

  A.reserve (NELEM);
  A.clear ();
  for (size_t i = 0; i < NELEM; ++i)
      A.push_back (i);


  B=A;
  time_op("std::sort", [&B]{annot::sort(B.begin(),B.end());});

  B=A;
  time_op("isabelle-llvm::introsort", [&B]{introsort(B.data(),0,NELEM);});

  annot::print_stats();

/*
  B=A;
  time_op("std::heapsort", [&B]{std::make_heap(B.begin(),B.end()); std::sort_heap(B.begin(),B.end()); });*/

}
