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


extern "C" {
  #include "introsort.h"
}

#define NELEM 1000000
#define NITER 100

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
	  insort_duration+=time_op([&]{std::__insertion_sort(__first, __last, __comp);});
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
	  std::__insertion_sort(__first, __last, __cmp);
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

















void Generator_random (void);
void Generator_sorted (void);
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
void sort_test(std::vector<IA> &A, std::vector<IA> &B, compare comp, string name, Op op) {
//   std::cout<<name<<std::endl;

  vector<double> durations;
  annot::insort_duration=0;

  for (int i=0;i<NITER;++i) {
    A=B;

    durations.push_back(time_op(op) * 1000.0);
    test_sorted(name,A,comp);
  }

  std::sort(durations.begin(),durations.end());

  auto N=durations.size();
  auto l=durations.begin()+N/10;
  auto h=durations.end()-N/10;

  N=h-l;

  double duration=std::accumulate(l,h,0.0) / (double)N;
  double min=*std::min_element(l,h);
  double max=*std::max_element(l,h);
  double dev=max-min;

  std::cout<<"  "<<name<<"."<<"time x "<<N<<": "<<std::setw(2)<<duration<<" ["<<dev<<"]";

  if (annot::insort_duration != 0) {
    std::cout<<" ("<<std::setw(2)<<annot::insort_duration<<")";
  }


  std::cout<<std::endl;

}


template<class IA, class compare>
int Test (std::vector<IA> &B,  compare comp)
{
  std::vector<IA> A (B);

  sort_test(A,B,comp,"isa::introsort",[&]{ introsort(A.data (), 0, A.size()); });
  sort_test(A,B,comp,"isa::introsort*",[&]{ annot::ll_introsort(A.data (), 0, A.size()); });
  sort_test(A,B,comp,"std::sort",[&]{ std::sort(A.begin (), A.end (), comp); });
  sort_test(A,B,comp,"std::sort*",[&]{ annot::sort(A.begin (), A.end (), comp); });
  sort_test(A,B,comp,"std::sort2",[&]{ annot::sort(A.begin (), A.end (), comp); });


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

