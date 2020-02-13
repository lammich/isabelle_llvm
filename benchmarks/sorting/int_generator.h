#ifndef _INT_GENERATOR_H
#define _INT_GENERATOR_H

#include <algorithm>
#include <iostream>
#include <iomanip>
#include <random>
#include <stdlib.h>
#include <vector>

#include <boost/sort/common/time_measure.hpp>
#include <boost/sort/common/file_vector.hpp>
#include "boost/sort/common/int_array.hpp"

#include <boost/sort/sort.hpp>

using namespace std;
namespace bsort = boost::sort;
namespace bsc = boost::sort::common;

using bsc::time_point;
using bsc::now;
using bsc::subtract_time;
using bsc::fill_vector_uint64;
using bsc::write_file_uint64;

class Int_Generator {

public:

  static vector<uint64_t> random(size_t NELEM) {
    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
    };
    return A;
  }

  static vector<uint64_t> random_dup (size_t NELEM, size_t nvals)
  {
    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
    };

    for (size_t i=0;i<A.size();++i) A[i]%=nvals;

    return A;
  }




  static vector<uint64_t> sorted (size_t NELEM)
  {
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();
    for (size_t i = 0; i < NELEM; ++i)
        A.push_back (i);

    return A;
  }

  static vector<uint64_t> organ_pipe (size_t NELEM)
  {
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();

    size_t n = NELEM/2;
    uint64_t v=0;

    for (size_t i=0;i<n;++i) A.push_back(v++);
    for (size_t i=n;i<2*n;++i) A.push_back(--v);
    return A;
  }


  static vector<uint64_t> almost_sorted (size_t NELEM, size_t nperm)
  {
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();
    for (size_t i = 0; i < NELEM; ++i)
        A.push_back (i);

    vector<size_t> P;

    if (fill_vector_uint64 ("input.bin", P, 2*nperm) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
    };

    for (size_t i=0;i<P.size();++i) P[i]%=NELEM;

    for (size_t i=0;i+1<P.size();i+=2) {
      std::swap(A[P[i]],A[P[i+1]]);
    }

    return A;
  }

  static vector<uint64_t> alleq (size_t NELEM)
  {
    vector<uint64_t> A(NELEM,42);
    return A;
  }

  static vector<uint64_t> sorted_end (size_t NELEM,size_t n_last)
  {
    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
    };
    std::sort (A.begin (), A.begin () + NELEM);

    return A;
  }

  static vector<uint64_t> sorted_middle (size_t NELEM, size_t n_last)
  {
    vector<uint64_t> A, B, C;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
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
    return A;
  }

  static vector<uint64_t> reverse_sorted (size_t NELEM)
  {
    vector<uint64_t> A;

    A.reserve (NELEM);
    A.clear ();
    for (size_t i = NELEM; i > 0; --i)
        A.push_back (i);

    return A;
  }


  static vector<uint64_t> reverse_sorted_end (size_t NELEM, size_t n_last)
  {
    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
    };
    std::sort (A.begin (), A.begin () + NELEM);
    for (size_t i = 0; i < (NELEM >> 1); ++i)
        std::swap (A[i], A[NELEM - 1 - i]);

    return A;
  }


  static vector<uint64_t> reverse_sorted_middle (size_t NELEM, size_t n_last)
  {
    vector<uint64_t> A, B, C;
    A.reserve (NELEM);
    A.clear ();
    if (fill_vector_uint64 ("input.bin", A, NELEM + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
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
    return A;
  };


  static void stats(vector<uint64_t> &A) {
    auto B=A;

    // Count different values, min,max,avg length of strings
    std::sort(B.begin(),B.end());
    auto i = std::unique(B.begin(),B.end());
    size_t n = i-B.begin();

    cout<<"# "<<A.size()<<" numbers "<<n<<" different"<<endl;
  }


public:
  static vector<uint64_t> generate_aux(size_t NELEM, string name) {
    if (name=="random") return random(NELEM);
    else if (name=="random-dup-10") return random_dup(NELEM,NELEM/10);
    else if (name=="random-boolean") return random_dup(NELEM,2);
    else if (name=="organ-pipe") return organ_pipe(NELEM);
    else if (name=="sorted") return sorted(NELEM);
    else if (name=="equal") return alleq(NELEM);
    else if (name=="almost-sorted-.1") return almost_sorted(NELEM,NELEM/1000);
    else if (name=="almost-sorted-1") return almost_sorted(NELEM,NELEM/100);
    else if (name=="almost-sorted-10") return almost_sorted(NELEM,NELEM/10);
    else if (name=="almost-sorted-50") return almost_sorted(NELEM,NELEM/2);
    else if (name=="sorted-end-.1") return sorted_end(NELEM,NELEM/1000);
    else if (name=="sorted-end-1") return sorted_end(NELEM,NELEM/100);
    else if (name=="sorted-end-10") return sorted_end(NELEM,NELEM/10);
    else if (name=="sorted-middle-.1") return sorted_middle(NELEM,NELEM/1000);
    else if (name=="sorted-middle-1") return sorted_middle(NELEM,NELEM/100);
    else if (name=="sorted-middle-10") return sorted_middle(NELEM,NELEM/10);
    else if (name=="rev-sorted") return reverse_sorted(NELEM);
    else if (name=="rev-sorted-end-.1") return reverse_sorted_end(NELEM,NELEM/1000);
    else if (name=="rev-sorted-end-1") return reverse_sorted_end(NELEM,NELEM/100);
    else if (name=="rev-sorted-end-10") return reverse_sorted_end(NELEM,NELEM/10);
    else if (name=="rev-sorted-middle-.1") return reverse_sorted_middle(NELEM,NELEM/1000);
    else if (name=="rev-sorted-middle-1") return reverse_sorted_middle(NELEM,NELEM/100);
    else if (name=="rev-sorted-middle-10") return reverse_sorted_middle(NELEM,NELEM/10);

    else {
      cout<<"No such integer generator "<<name<<endl;
      exit(1);
    }
  }

  static vector<uint64_t> generate(size_t NELEM, string name) {
    auto A = generate_aux(NELEM,name);
    stats(A);
    return A;
  }

};


#endif
