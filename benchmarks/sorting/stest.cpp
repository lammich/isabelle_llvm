#include <algorithm>

#include <iostream>
#include <vector>

#include <boost/sort/common/time_measure.hpp>

uint64_t llcnt_partitionings=0;
uint64_t llcnt_partitions=0;


extern "C" {
  #include "introsort.h"
}


size_t NELEM = 32;

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

void prn(int x) {
  if (x<10) std::cout<<" "; std::cout<<x;
}

template <typename A> void print_range2(A l0, A begin, A end) {

  size_t n = end-begin;
  size_t base = begin-l0;

  for (size_t i=0;i<n;++i) {prn(base+i); std::cout<<" ";}
  std::cout<<std::endl;
  for (size_t i=0;i<n;++i) {prn(*(begin+i)); std::cout<<" ";}
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


template<typename RandomAccessIterator>
  inline void
  std_heapsort(RandomAccessIterator first, RandomAccessIterator last)
  {
    std::make_heap(first,last);
    std::sort_heap(first,last);
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



namespace test2 {


  std::vector<uint64_t>::iterator l0;

  /// This is a helper function...
  template<typename _RandomAccessIterator, typename _Compare>
    _RandomAccessIterator
    __unguarded_partition(_RandomAccessIterator __first,
			  _RandomAccessIterator __last,
			  _RandomAccessIterator __pivot, _Compare __comp)
    {
      while (true)
	{
	  while (__first!=__last && __comp(__first, __pivot))
	    ++__first;
	  --__last;
	  while (__first!=__last && __comp(__pivot, __last))
	    --__last;
	  if (!(__first < __last))
	    return __first;
	  std::iter_swap(__first, __last);
	  ++__first;
	}
    }

  /// This is a helper function...
  template<typename _RandomAccessIterator, typename _Compare>
    inline _RandomAccessIterator
    __unguarded_partition_pivot(_RandomAccessIterator __first,
				_RandomAccessIterator __last, _Compare __comp)
    {
      _RandomAccessIterator __mid = __first + (__last - __first) / 2;

      std::cout<<"mid = "<<__mid-l0<<std::endl;

      std::__move_median_to_first(__first, __first + 1, __mid, __last - 1,
				  __comp);
      return test2::__unguarded_partition(__first + 1, __last, __first, __comp);
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
          std::cout<<"Sorting ["<<(__first-l0)<<"..."<<(__last-l0)<<"]"<<std::endl;

	  if (__depth_limit == 0)
	    {
              std::cout<<"HIT DEPTH LIMIT"<<std::endl;
	      std::__partial_sort(__first, __last, __last, __comp);
	      return;
	    }
	  --__depth_limit;
	  _RandomAccessIterator __cut =
	    test2::__unguarded_partition_pivot(__first, __last, __comp);

          std::cout<<"cut at "<<(__cut-l0)<<std::endl;
          print_range2(l0,__first,__last);


	  test2::__introsort_loop(__cut, __last, __depth_limit, __comp);
	  __last = __cut;
	}
    }


  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    __sort(_RandomAccessIterator __first, _RandomAccessIterator __last,
	   _Compare __comp)
    {
      if (__first != __last)
	{
	  test2::__introsort_loop(__first, __last,
				std::__lg(__last - __first) * 2,
				__comp);

          std::cout<<"partially sorted array"<<std::endl;
          print_range2(l0,__first,__last);

	  std::__final_insertion_sort(__first, __last, __comp);

          std::cout<<"RESULT"<<std::endl;
          print_range2(l0,__first,__last);

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

      test2::__sort(__first, __last, __gnu_cxx::__ops::__iter_less_iter());
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

  std::cout<<sizeof(llstring)<<std::endl;
  std::cout<<sizeof(std::vector<char>)<<std::endl;
  std::cout<<sizeof(std::string)<<std::endl;

  return 1;


  std::vector<uint64_t> A,B;

  A.reserve (NELEM);
  A.clear ();
  for (size_t i = 0; i < NELEM; ++i)
      A.push_back (i);

  A[0]=9;
  A[15]=10;

  B=A;

  test2::l0=B.begin();

  time_op("test2::sort", [&B]{test2::sort(B.begin(),B.end());});

//   B=A;
//   time_op("std::sort", [&B]{std::sort(B.begin(),B.end());});



//   B=A;
//   time_op("std::heapsort", [&B]{std_heapsort(B.begin(),B.end());});
//
//   B=A;
//   time_op("isabelle-llvm::heapsort", [&B]{heapsort(B.data(),0,NELEM);});

//   annot::print_stats();

/*
  B=A;
  time_op("std::heapsort", [&B]{std::make_heap(B.begin(),B.end()); std::sort_heap(B.begin(),B.end()); });*/

//   xxx, ctd here: try to confirm influence of insertion-sort (measure time with omitted final-sort)
//   try to tune threshold factor?






}
