//----------------------------------------------------------------------------
/// @file benchmark_numbers.cpp
/// @brief Benchmark of several sort methods with integer objects
///
/// @author Copyright (c) 2017 Francisco José Tapia (fjtapia@gmail.com )\n
///         Distributed under the Boost Software License, Version 1.0.\n
///         ( See accompanying file LICENSE_1_0.txt or copy at
///           http://www.boost.org/LICENSE_1_0.txt )
///
///         This program use for comparison purposes, the Threading Building
///         Blocks which license is the GNU General Public License, version 2
///         as  published  by  the  Free Software Foundation.
///
/// @version 0.1
///
/// @remarks
//-----------------------------------------------------------------------------
#include <algorithm>

#include <iostream>
#include <iomanip>
#include <random>
#include <stdlib.h>
#include <vector>


#include <boost/sort/common/time_measure.hpp>
#include <boost/sort/common/file_vector.hpp>
#include <boost/sort/common/int_array.hpp>

#include <boost/sort/sort.hpp>

#include "BlockQuicksort/blocked_double_pivot_check_mosqrt.h++"



extern "C" {
  #include "introsort.h"
}

#define NELEM 10000000
#define NITER 10

using namespace std;
namespace bsort = boost::sort;
namespace bsc = boost::sort::common;

using bsc::time_point;
using bsc::now;
using bsc::subtract_time;
using bsc::fill_vector_uint64;
using bsc::write_file_uint64;

using bsort::spinsort;
using bsort::flat_stable_sort;
using bsort::spreadsort::spreadsort;
using bsort::pdqsort;
using bsort::pdqsort_branchless;


template<typename A> double time_op(A op) {
  auto start = now ();
  op();
  auto finish = now ();
  return subtract_time (finish, start);
}


template<typename A> void time_op(std::string name, A op) {
  auto start = now ();
  op();
  auto finish = now ();
  auto duration = subtract_time (finish, start);

  std::cout<<"  "<<name<<"."<<"time: "<<duration<<std::endl;
}



namespace annot {


  template<class Iter, class Compare>
  inline void pdqsort(Iter first, Iter last, Compare comp) {
      if (first == last) return;
      boost::sort::pdqsort_detail::pdqsort_loop<Iter, Compare,
          false
          >(
          first, last, comp, boost::sort::pdqsort_detail::log2(last - first));
  }




  double insort_duration=0;

  void ll_introsort(uint64_t *a, int64_t l, int64_t h) {
    introsort_aux(a,l,h,std::__lg(h-l) * 2+100);
    insort_duration+=time_op([&]{insertion_sort(a,l,h);});
  }


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
  }




  /// This is a helper function for the sort routine.
  template<typename _RandomAccessIterator, typename _Compare>
    void
    __guarded_linear_insert(_RandomAccessIterator __first, _RandomAccessIterator __last,
			      _Compare __comp)
    {
      typename iterator_traits<_RandomAccessIterator>::value_type
	__val = _GLIBCXX_MOVE(*__last);
      _RandomAccessIterator __i = __last;
      while (__i != __first && __comp(__val, __i-1))
	{
	  *__i = _GLIBCXX_MOVE(*(__i-1));
	  --__i;
	}
      *__i = _GLIBCXX_MOVE(__val);
    }

  /// This is a helper function for the sort routine.
  template<typename _RandomAccessIterator, typename _Compare>
    void
    __insertion_sort(_RandomAccessIterator __first,
		     _RandomAccessIterator __last, _Compare __comp)
    {
      if (__first == __last) return;

      for (_RandomAccessIterator __i = __first + 1; __i != __last; ++__i)
	{
// 	  if (__comp(__i, __first))
// 	    {
// 	      typename iterator_traits<_RandomAccessIterator>::value_type
// 		__val = _GLIBCXX_MOVE(*__i);
// 	      _GLIBCXX_MOVE_BACKWARD3(__first, __i, __i + 1);
// 	      *__first = _GLIBCXX_MOVE(__val);
// 	    }
// 	  else
	    annot::__guarded_linear_insert(__first, __i,
				__gnu_cxx::__ops::__val_comp_iter(__comp));
	}
    }


  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    insort(_RandomAccessIterator __first, _RandomAccessIterator __last,
	   _Compare __comp)
    {
      __glibcxx_function_requires(_Mutable_RandomAccessIteratorConcept<
	    _RandomAccessIterator>)
      __glibcxx_requires_valid_range(__first, __last);
      __glibcxx_requires_irreflexive_pred(__first, __last, __comp);

      typedef __decltype(__comp) _Cmp;
      __gnu_cxx::__ops::_Iter_comp_iter<_Cmp> __cmp(_GLIBCXX_MOVE(__comp));

      if (__first != __last)
	{
	  annot::__insertion_sort(__first, __last, __cmp);
	}
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
//           print_range(__first,__last);
	  _RandomAccessIterator __cut =
	    std::__unguarded_partition_pivot(__first, __last, __comp);
//           print_range(__first,__last);
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
	  std::__introsort_loop(__first, __last,
				std::__lg(__last - __first) * 2,
				__comp);
	  insort_duration+=time_op([&]{std::__final_insertion_sort(__first, __last, __comp);});
	}
    }

  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    __sort2(_RandomAccessIterator __first, _RandomAccessIterator __last,
	   _Compare __comp)
    {
      if (__first != __last)
	{
	  std::__introsort_loop(__first, __last,
				std::__lg(__last - __first) * 2,
				__comp);
// 	  insort_duration+=time_op([&]{std::__final_insertion_sort(__first, __last, __comp);});
	  insort_duration+=time_op([&]{annot::__insertion_sort(__first, __last, __comp);});
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

  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    sort(_RandomAccessIterator __first, _RandomAccessIterator __last,
	 _Compare __comp)
    {
      // concept requirements
      __glibcxx_function_requires(_Mutable_RandomAccessIteratorConcept<
	    _RandomAccessIterator>)
      __glibcxx_function_requires(_BinaryPredicateConcept<_Compare,
	    typename iterator_traits<_RandomAccessIterator>::value_type,
	    typename iterator_traits<_RandomAccessIterator>::value_type>)
      __glibcxx_requires_valid_range(__first, __last);
      __glibcxx_requires_irreflexive_pred(__first, __last, __comp);

      annot::__sort(__first, __last, __gnu_cxx::__ops::__iter_comp_iter(__comp));
    }

  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    sort2(_RandomAccessIterator __first, _RandomAccessIterator __last,
	 _Compare __comp)
    {
      // concept requirements
      __glibcxx_function_requires(_Mutable_RandomAccessIteratorConcept<
	    _RandomAccessIterator>)
      __glibcxx_function_requires(_BinaryPredicateConcept<_Compare,
	    typename iterator_traits<_RandomAccessIterator>::value_type,
	    typename iterator_traits<_RandomAccessIterator>::value_type>)
      __glibcxx_requires_valid_range(__first, __last);
      __glibcxx_requires_irreflexive_pred(__first, __last, __comp);

      annot::__sort2(__first, __last, __gnu_cxx::__ops::__iter_comp_iter(__comp));
    }


}




template<typename RandomAccessIterator, typename Compare>
  inline void
  std_heapsort(RandomAccessIterator first, RandomAccessIterator last,
        Compare comp)
  {
    std::make_heap(first,last,comp);
    std::sort_heap(first,last,comp);

  }



namespace testbp {


  vector<uint64_t>::iterator l0;

  /// This is a helper function...
  template<typename _RandomAccessIterator, typename _Compare>
    _RandomAccessIterator
    __unguarded_partition2(_RandomAccessIterator __first,
			  _RandomAccessIterator __last,
			  _RandomAccessIterator __pivot, _Compare __comp)
    {
      while (__comp(__first, __pivot))
        ++__first;
      --__last;
      while (__comp(__pivot, __last))
        --__last;

      while ((__first < __last))
	{
	  std::iter_swap(__first, __last);
	  ++__first;

	  while (__comp(__first, __pivot))
	    ++__first;
	  --__last;
	  while (__comp(__pivot, __last))
	    --__last;
	}

      return __first;
    }


  template<typename _RandomAccessIterator, typename _Compare>
    _RandomAccessIterator
    __unguarded_partition(_RandomAccessIterator __first,
			  _RandomAccessIterator __last,
			  _RandomAccessIterator __pivot, _Compare __comp)
    {
      while (true)
	{
	  while (__comp(__first, __pivot))
	    ++__first;
	  --__last;
	  while (__comp(__pivot, __last))
	    --__last;
	  if (!(__first < __last))
	    return __first;
	  std::iter_swap(__first, __last);
	  ++__first;
	}
    }

  template<typename _RandomAccessIterator, typename _Compare>
    _RandomAccessIterator
    __unguarded_partition3(_RandomAccessIterator __first,
			  _RandomAccessIterator __last,
			  _RandomAccessIterator __pivot, _Compare __comp)
    {
      bool brk=false;
      while (!brk)
	{
	  while (__comp(__first, __pivot))
	    ++__first;
	  --__last;
	  while (__comp(__pivot, __last))
	    --__last;
	  if (!(__first < __last))
	    brk=true;
          else {
            std::iter_swap(__first, __last);
            ++__first;
          }
	}

      return __first;
    }

  /// This is a helper function...
  template<typename _RandomAccessIterator, typename _Compare>
    inline _RandomAccessIterator
    __unguarded_partition_pivot(_RandomAccessIterator __first,
				_RandomAccessIterator __last, _Compare __comp)
    {
      _RandomAccessIterator __mid = __first + (__last - __first) / 2;
      std::__move_median_to_first(__first, __first + 1, __mid, __last - 1,
				  __comp);
       return testbp::__unguarded_partition3(__first + 1, __last, __first, __comp);
    }

  /// This is a helper function for the sort routine.
  template<typename _RandomAccessIterator, typename _Size, typename _Compare>
    void
    __introsort_loop(_RandomAccessIterator __first,
		     _RandomAccessIterator __last,
		     _Size __depth_limit, _Compare __comp)
    {
      while (__last - __first > int(_S_threshold))
	{
	  if (__depth_limit == 0)
	    {
	      std::__partial_sort(__first, __last, __last, __comp);
	      return;
	    }
	  --__depth_limit;
	  _RandomAccessIterator __cut =
	  testbp::__unguarded_partition_pivot(__first, __last, __comp);
	  testbp::__introsort_loop(__cut, __last, __depth_limit, __comp);
	  __last = __cut;
	}
    }

  template<typename I, typename S, typename C> void introsort_alt(I l, I h, S d, C comp) {
    if (h-l > (int)(_S_threshold)) {
      if (d==0) {
        std::__partial_sort(l,h,h,comp);
      } else {
        --d;

        I m = testbp::__unguarded_partition_pivot(l,h,comp);

//         std::iter_swap(l,m-1);


        introsort_alt(l,m,d,comp);
        introsort_alt(m,h,d,comp);
      }
    }
  }


  // sort


  template<typename _RandomAccessIterator, typename _Compare>
    void
    __unguarded_linear_insert(_RandomAccessIterator __last,
			      _Compare __comp)
    {
      typename iterator_traits<_RandomAccessIterator>::value_type
	__val = _GLIBCXX_MOVE(*__last);
      _RandomAccessIterator __next = __last;
      --__next;
      while (__comp(__val, __next))
	{
	  *__last = _GLIBCXX_MOVE(*__next);
	  __last = __next;
	  --__next;
	}
      *__last = _GLIBCXX_MOVE(__val);
    }

  template<typename I, typename C> void lin_insert(I l, I h, C comp) {
    auto tmp=*h;
    while (l<h && comp(tmp,h-1)) {
      *h=*(h-1);
      --h;
    }
    *h=tmp;
  }


  /// This is a helper function for the sort routine.
  template<typename _RandomAccessIterator, typename _Compare>
    void
    __insertion_sort(_RandomAccessIterator __first,
		     _RandomAccessIterator __last, _Compare __comp)
    {
      if (__first == __last) return;

      for (_RandomAccessIterator __i = __first + 1; __i != __last; ++__i)
	{

          testbp::lin_insert(__first,__i,__gnu_cxx::__ops::__val_comp_iter(__comp));

/*
	  if (__comp(__i, __first))
	    {
	      typename iterator_traits<_RandomAccessIterator>::value_type
		__val = _GLIBCXX_MOVE(*__i);
	      _GLIBCXX_MOVE_BACKWARD3(__first, __i, __i + 1);
	      *__first = _GLIBCXX_MOVE(__val);
	    }
	  else
	    testbp::__unguarded_linear_insert(__i,
				__gnu_cxx::__ops::__val_comp_iter(__comp));*/

	}
    }



  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    __sort(_RandomAccessIterator __first, _RandomAccessIterator __last,
	   _Compare __comp)
    {
      if (__first != __last)
	{
// 	  testbp::__introsort_loop(__first, __last,
// 				std::__lg(__last - __first) * 2,
// 				__comp);
	  testbp::introsort_alt(__first, __last,
				std::__lg(__last - __first) * 2,
				__comp);

	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
// 	  testbp::__insertion_sort(__first, __last, __comp);
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

      testbp::__sort(__first, __last, __gnu_cxx::__ops::__iter_less_iter());
    }









}




namespace test_no_final_sort {




  template<typename _RandomAccessIterator, typename _Compare>
    inline void
    __sort(_RandomAccessIterator __first, _RandomAccessIterator __last,
	   _Compare __comp)
    {
      if (__first != __last)
	{
	  std::__introsort_loop(__first, __last,
				std::__lg(__last - __first) * 2,
				__comp);
// 	  std::__final_insertion_sort(__first, __last, __comp);
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

      test_no_final_sort::__sort(__first, __last, __gnu_cxx::__ops::__iter_less_iter());
    }


  void ll_introsort(uint64_t *a, int64_t l, int64_t h) {
    introsort_aux(a,l,h,std::__lg(h-l) * 2+100);
//     insertion_sort(a,l,h);
  }


}








void Generator_random (void);
void Generator_random_dup (void);
void Generator_sorted (void);
void Generator_almost_sorted (size_t nperm);
void Generator_alleq ();
void Generator_sorted_end (size_t n_last);
void Generator_sorted_middle (size_t n_last);
void Generator_reverse_sorted (void);
void Generator_reverse_sorted_end (size_t n_last);
void Generator_reverse_sorted_middle (size_t n_last);

template<class IA, class compare>
int Test (std::vector<IA> &B, compare comp = compare ());

int main (int argc, char *argv[])
{

    Generator_random ();
    Generator_random_dup ();

    Generator_alleq ();
    Generator_almost_sorted (NELEM / 1000);
    Generator_almost_sorted (NELEM / 100);
    Generator_almost_sorted (NELEM / 10);
    Generator_almost_sorted (NELEM);

    Generator_sorted ();
    Generator_sorted_end (NELEM / 1000);
    Generator_sorted_end (NELEM / 100);
    Generator_sorted_end (NELEM / 10);
    Generator_sorted_middle (NELEM / 1000);
    Generator_sorted_middle (NELEM / 100);
    Generator_sorted_middle (NELEM / 10);
    Generator_reverse_sorted ();
    Generator_reverse_sorted_end (NELEM / 1000);
    Generator_reverse_sorted_end (NELEM / 100);
    Generator_reverse_sorted_end (NELEM / 10);
    Generator_reverse_sorted_middle (NELEM / 1000);
    Generator_reverse_sorted_middle (NELEM / 100);
    Generator_reverse_sorted_middle (NELEM / 10);

//     annot::print_stats();

    return 0;
}
void
Generator_random (void)
{
    std::cout<<std::endl<<std::endl<<"random"<<std::endl;
    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    Test<uint64_t, std::less<uint64_t>> (A);
}
;

void
Generator_random_dup (void)
{
    std::cout<<std::endl<<std::endl<<"random with lots of dups"<<std::endl;
    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };

    for (size_t i=0;i<A.size();++i) A[i]%=(2048);


    Test<uint64_t, std::less<uint64_t>> (A);
}
;



void
Generator_sorted (void)
{
    std::cout<<std::endl<<std::endl<<"sorted"<<std::endl;
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();
    for (size_t i = 0; i < NELEM; ++i)
        A.push_back (i);
    Test<uint64_t, std::less<uint64_t>> (A);

}


void
Generator_almost_sorted (size_t nperm)
{
    std::cout<<std::endl<<std::endl<<"almost sorted ("<< (float)nperm/NELEM * 100<<"perm)"<<std::endl;
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();
    for (size_t i = 0; i < NELEM; ++i)
        A.push_back (i);

    vector<size_t> P;

    if (fill_vector_uint64 ("input.bin", P, nperm) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };

    for (size_t i=0;i<P.size();++i) P[i]%=NELEM;

    for (size_t i=0;i+1<P.size();i+=2) {
      std::swap(A[P[i]],A[P[i+1]]);
    }



    Test<uint64_t, std::less<uint64_t>> (A);

}

void
Generator_alleq ()
{
    std::cout<<std::endl<<std::endl<<"all equal"<<std::endl;
    vector<uint64_t> A(NELEM,42);

    Test<uint64_t, std::less<uint64_t>> (A);

}

void Generator_sorted_end (size_t n_last)
{
    std::cout<<std::endl<<std::endl<<"sorted + "<<(float)n_last/NELEM * 100<<"% end"<<std::endl;

    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    std::sort (A.begin (), A.begin () + NELEM);

    Test<uint64_t, std::less<uint64_t>> (A);

}
;
void Generator_sorted_middle (size_t n_last)
{
    std::cout<<std::endl<<std::endl<<"sorted + "<<(float)n_last/NELEM * 100<<"% mid"<<std::endl;

    vector<uint64_t> A, B, C;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    for (size_t i = NELEM; i < A.size (); ++i)
        B.push_back (std::move (A[i]));
    A.resize ( NELEM);
    for (size_t i = 0; i < (NELEM >> 1); ++i)
        std::swap (A[i], A[NELEM - 1 - i]);

    std::sort (A.begin (), A.end ());
    size_t step = NELEM / n_last + 1;
    size_t pos = 0;

    for (size_t i = 0; i < B.size (); ++i, pos += step)
    {
        C.push_back (B[i]);
        for (size_t k = 0; k < step; ++k)
            C.push_back (A[pos + k]);
    };
    while (pos < A.size ())
        C.push_back (A[pos++]);
    A = C;
    Test<uint64_t, std::less<uint64_t>> (A);
}
;
void Generator_reverse_sorted (void)
{
    std::cout<<std::endl<<std::endl<<"rev sorted"<<std::endl;
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();
    for (size_t i = NELEM; i > 0; --i)
        A.push_back (i);
    Test<uint64_t, std::less<uint64_t>> (A);
}
void Generator_reverse_sorted_end (size_t n_last)
{
    std::cout<<std::endl<<std::endl<<"rev sorted + "<<(float)n_last/NELEM * 100<<"% end"<<std::endl;

    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    std::sort (A.begin (), A.begin () + NELEM);
    for (size_t i = 0; i < (NELEM >> 1); ++i)
        std::swap (A[i], A[NELEM - 1 - i]);

    Test<uint64_t, std::less<uint64_t>> (A);
}
void Generator_reverse_sorted_middle (size_t n_last)
{
    std::cout<<std::endl<<std::endl<<"rev sorted + "<<(float)n_last/NELEM * 100<<"% mid"<<std::endl;

    vector<uint64_t> A, B, C;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    for (size_t i = NELEM; i < A.size (); ++i)
        B.push_back (std::move (A[i]));
    A.resize ( NELEM);
    for (size_t i = 0; i < (NELEM >> 1); ++i)
        std::swap (A[i], A[NELEM - 1 - i]);

    std::sort (A.begin (), A.end ());
    size_t step = NELEM / n_last + 1;
    size_t pos = 0;

    for (size_t i = 0; i < B.size (); ++i, pos += step)
    {
        C.push_back (B[i]);
        for (size_t k = 0; k < step; ++k)
            C.push_back (A[pos + k]);
    };
    while (pos < A.size ())
        C.push_back (A[pos++]);
    A = C;
    Test<uint64_t, std::less<uint64_t>> (A);
};

template<class IA, class compare>
void test_sorted(string name, std::vector<IA> &A, compare comp)
{
  if (!std::is_sorted(A.begin (), A.end (), comp)) {

    std::cout<<"*** NOT SORTED *** "<<name<<std::endl;
//     for (auto i=B.begin(); i<B.end();++i) std::cout<<*i<<" ";
//     std::cout<<std::endl;
//     for (auto i=A.begin(); i<A.end();++i) std::cout<<*i<<" ";
//     std::cout<<std::endl;


  }
}


template<class IA, class compare, class Op>
void sort_test(std::vector<IA> &A, std::vector<IA> &B, compare comp, string name, Op op, bool verify=true) {
//   std::cout<<name<<std::endl;

  vector<double> durations;
  annot::insort_duration=0;

  for (int i=0;i<NITER;++i) {
    A=B;

    durations.push_back(time_op(op) * 1000.0);
    if (verify) test_sorted(name,A,comp);
  }

  std::sort(durations.begin(),durations.end());

  auto N=durations.size();
  auto l=durations.begin()+N/10;
  auto h=durations.end()-N/10;

  N=h-l;

  double duration=std::accumulate(l,h,0.0) / (double)N;
  double min=*std::min_element(l,h);
  double max=*std::max_element(l,h);
//   double dev=max-min;

  std::cout<<"  "<<name<<"."<<"time x "<<N<<": "<<std::setw(2)<<duration<<" ["<<min<<" .. "<<max<<"]";

  if (annot::insort_duration != 0) {
    std::cout<<" ("<<std::setw(2)<<annot::insort_duration<<")";
  }


  std::cout<<std::endl;

}

extern "C" {
int cmpfunc (const void * ap, const void * bp) {
  uint64_t a=*(uint64_t*)ap;
  uint64_t b=*(uint64_t*)bp;
  if (a<b) return -1;
  else if (a==b) return 0;
  else return 1;
}
}

void qsort(std::vector<uint64_t> &A) {
  std::qsort(A.data(),A.size(),sizeof(uint64_t),cmpfunc);
}



template<class IA, class compare>
int Test (std::vector<IA> &B,  compare comp)
{
  std::vector<IA> A (B);

   sort_test(A,B,comp,"isa::introsort",[&]{ introsort(A.data (), 0, A.size()); });
//    sort_test(A,B,comp,"isa::introsortUGI",[&]{ introsortUGI(A.data (), 0, A.size()); });
//    sort_test(A,B,comp,"nfs-isa::introsort",[&]{ test_no_final_sort::ll_introsort(A.data (), 0, A.size()); }, false);
//   sort_test(A,B,comp,"isa::introsort*",[&]{ annot::ll_introsort(A.data (), 0, A.size()); });
//    sort_test(A,B,comp,"testbp::sort",[&]{ testbp::sort(A.begin (), A.end ()); });
   sort_test(A,B,comp,"std::sort",[&]{ std::sort(A.begin (), A.end (), comp);});
//   sort_test(A,B,comp,"no_final::sort",[&]{ test_no_final_sort::sort(A.begin (), A.end ()); }, false);


//   sort_test(A,B,comp,"std::qsort",[&]{ qsort(A); });
//  sort_test(A,B,comp,"bdpcmosqrt::sort",[&]{ blocked_double_pivot_check_mosqrt::sort(A.begin (), A.end (), comp); });




//   sort_test(A,B,comp,"pdqsort_bl",[&]{ pdqsort_branchless(A.begin (), A.end (), comp); });
//   sort_test(A,B,comp,"pdqsort",[&]{ annot::pdqsort(A.begin (), A.end (), comp); });
//   sort_test(A,B,comp,"std::sort*",[&]{ annot::sort(A.begin (), A.end (), comp); });
//   sort_test(A,B,comp,"std::sort2",[&]{ annot::sort2(A.begin (), A.end (), comp); });


//   std::vector<IA> A (B);
//
//   A = B;
//   time_op("std::sort",[&]{ annot::sort(A.begin (), A.end (), comp); });
//   test_sorted("std::sort",A,comp);
//
//   A = B;
//   time_op("isa::introsort*",[&]{ annot::ll_introsort(A.data (), 0, A.size()); });
//   test_sorted("isa::introsort*",A,comp);
//
//   A = B;
//   time_op("isa::introsort",[&]{ introsort(A.data (), 0, A.size()); });
//   test_sorted("isa::introsort",A,comp);
//

// //     A = B;
// //     start = now ();
// //     insertion_sort (A.data() , 0, A.size());


//     //---------------------------- begin --------------------------------
//     double duration;
//     time_point start, finish;
//     std::vector<IA> A (B);
//     std::vector<double> V;
//
//     //--------------------------------------------------------------------
//     A = B;
//     start = now ();
// //    std::sort (A.begin (), A.end (), comp);
//     annot::sort (A.begin (), A.end ()/*, comp*/);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//     test_sorted("std::sort",A,comp);
//
// //     A = B;
// //     start = now ();
// //     annot::insort (A.begin (), A.end (), comp);
// // //     annot::sort (A.begin (), A.end ()/*, comp*/);
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("std::insort",A,B,comp);
// //
// //     A = B;
// //     start = now ();
// //     insertion_sort (A.data() , 0, A.size());
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("isabelle-llvm::insort",A,B,comp);
// //
// //
// //     A = B;
// //     start = now ();
// //     introsort (A.data() , 0, A.size());
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("isabelle-llvm::introsort",A,B,comp);
// //
//
// //     A = B;
// //     start = now ();
// //     std_heapsort (A.begin (), A.end (), comp);
// // //     annot::sort (A.begin (), A.end ()/*, comp*/);
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("heapsort",A,B,comp);
// //
// //
// //     A = B;
// //     start = now ();
// //     heapsort (A.data() , 0, A.size());
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("isabelle-llvm::heapsort",A,B,comp);
//
//
// //     A = B;
// //     start = now ();
// //     pdqsort (A.begin (), A.end (), comp);
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("pdqsort",A,B,comp);
// //
// //     A = B;
// //     start = now ();
// //     std::stable_sort (A.begin (), A.end (), comp);
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("std::stable_sort",A,B,comp);
// //
// //     A = B;
// //     start = now ();
// //     spinsort(A.begin (), A.end (), comp);
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("spinsort",A,B,comp);
// //
// //     A = B;
// //     start = now ();
// //     flat_stable_sort (A.begin (), A.end (), comp);
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("flat_stable_sort",A,B,comp);
// //
// //
// //     A = B;
// //     start = now ();
// //     spreadsort (A.begin (), A.end ());
// //     finish = now ();
// //     duration = subtract_time (finish, start);
// //     V.push_back (duration);
// //     test_sorted("spreadsort",A,B,comp);
//
//     //-----------------------------------------------------------------------
//     // printing the vector
//     //-----------------------------------------------------------------------
//     std::cout<<std::setprecision(2)<<std::fixed;
//     for ( uint32_t i =0 ; i < V.size() ; ++i)
//     {   std::cout<<std::right<<std::setw(5)<<V[i]<<" |";
//     };
//     std::cout<<std::endl;
    return 0;
};

