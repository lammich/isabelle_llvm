// Re-used parts from BOOST sorting benchmark suite

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

#ifndef NO_LLVM
extern "C" {
  #include "introsort.h"
}
#endif

using namespace std;
namespace bsort = boost::sort;
namespace bsc = boost::sort::common;

using bsc::time_point;
using bsc::now;
using bsc::subtract_time;
using bsc::fill_vector_uint64;
using bsc::write_file_uint64;


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

template<class IA, class compare>
void test_sorted(std::vector<IA> &A, compare comp)
{
  if (!std::is_sorted(A.begin (), A.end (), comp)) {
    std::cout<<"*** NOT SORTED *** "<<std::endl;
  }
}

template<class IA, class compare, class Op>
void sort_test(std::vector<IA> &A, std::vector<IA> &B, size_t NITER, compare comp, Op op, bool verify=true) {
//   std::cout<<name<<std::endl;

  vector<double> durations;

  for (size_t i=0;i<NITER;++i) {
    A=B;

    durations.push_back(time_op(op) * 1000.0);
    if (verify) test_sorted(A,comp);
  }

  std::sort(durations.begin(),durations.end());

  auto N=durations.size();
//   auto l=durations.begin()+N/10;
//   auto h=durations.end()-N/10;
  auto l=durations.begin();
  auto h=durations.end();

  N=h-l;

  double duration=std::accumulate(l,h,0.0) / (double)N;
  double min=*std::min_element(l,h);
  double max=*std::max_element(l,h);
//   double dev=max-min;

  std::cout<<": "<<std::setw(2)<<duration<<" ["<<min<<" .. "<<max<<"] ";

  for (auto i=l;i!=h;++i)
      std::cout<<std::setw(2)<<*i<<" ";

  std::cout<<std::endl;
}


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


#ifndef NO_LLVM

llstring cnv_str(string s) {
  llstring res;
  str_init(&res);

  for (auto c = s.begin(); c!=s.end();++c) { str_append(&res,*c); }
  return res;
}


std::vector<llstring> cnv_strvec(std::vector<string> v) {
  std::vector<llstring> res;
  res.reserve(v.size());

  for (auto i = v.begin();i!=v.end();++i) res.push_back(cnv_str(*i));

  return res;
}

string bcnv_str(const llstring &s) {
  string res="";

  for (size_t i=0;i<s.size;++i) { res = res + ((s.data[i])); }
  return res;
}


std::vector<string> bcnv_strvec(std::vector<llstring> v) {
  std::vector<string> res;
  res.reserve(v.size());

  for (auto i = v.begin();i!=v.end();++i) res.push_back(bcnv_str(*i));

  return res;
}



class String_Generator {

  static vector<string> random(size_t NELEM)
  {
    std::vector<std::string> A;
    A.reserve(NELEM);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NELEM) != 0)
    {
      std::cout << "Error in the input file\n";
      exit(1);
    };
    return A;

  }

  static vector<string> sorted(size_t NELEM)
  {
    std::vector<std::string> A;
    A.reserve(NELEM);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NELEM) != 0)
    {
      std::cout << "Error in the input file\n";
      exit(1);
    };
    std::sort( A.begin() , A.end() );
    return A;
  };

  static vector<string> almost_sorted (size_t NELEM, size_t nperm)
  {
    vector<string> A = sorted(NELEM);
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


  static vector<string> organ_pipe(size_t NELEM)
  {
    std::vector<std::string> A = sorted(NELEM);
    auto i = std::unique( A.begin() , A.end() );
    A.resize(i-A.begin());

    if (A.size()<NELEM/2) {
      std::cout << "Too many equal strings for organ-pipe distribution\n";
      exit(1);
    }
    A.resize(NELEM/2);
    A.insert(A.end(),A.begin(),A.end());
    std::reverse(A.begin()+NELEM/2,A.end());

    return A;
  };

  static vector<string> random_dup(size_t NELEM, size_t nval)
  {
    std::vector<std::string> D = sorted(nval);
    std::vector<size_t> S = Int_Generator::random_dup(NELEM,nval);

    std::vector<std::string> A;
    A.reserve(NELEM);
    A.clear();
    for (size_t i=0;i<NELEM;++i) {
      A.push_back(D[S[i]]);
    }

    return A;
  };


  static vector<string> alleq(size_t NELEM)
  {
    std::vector<std::string> D = sorted(1);

    std::vector<std::string> A;
    A.reserve(NELEM);
    A.clear();
    for (size_t i=0;i<NELEM;++i) {
      A.push_back(D[0]);
    }

    return A;
  };

  static vector<string> sorted_end(size_t NELEM, size_t n_last)
  {
    std::vector<std::string> A;
    A.reserve(NELEM);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NELEM+ n_last) != 0)
    {
      std::cout << "Error in the input file\n";
      exit(1);
    };
    std::sort (A.begin() , A.begin() + NELEM );
    return A;
  };

  static vector<string> sorted_middle(size_t NELEM,size_t n_last)
  {
    std::vector<std::string> A,B,C;
    A.reserve(NELEM);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NELEM + n_last) != 0)
    {
      std::cout << "Error in the input file\n";
      exit(1);
    };
    for ( size_t i = NELEM; i < A.size() ; ++i)
      B.push_back ( std::move ( A[i]));
    A.resize ( NELEM);
    std::sort (A.begin() , A.end() );
    size_t step = NELEM/n_last +1 ;
    size_t pos = 0 ;

    for ( size_t i =0 ; i < B.size() ; ++i, pos += step)
    {   C.push_back ( B[i]);
      for ( size_t k = 0 ; k < step ; ++k )
        C.push_back ( A[pos + k] );
    };
    while ( pos < A.size() ) C.push_back ( A[pos++]);
    A = C ;

    return A;
  };

  static vector<string> reverse_sorted(size_t NELEM)
  {

    std::vector<std::string> A;
    A.reserve(NELEM);
    {
      std::vector<std::string> B;
      B.reserve(NELEM);
      if (bsc::fill_vector_string("input.bin", B, NELEM) != 0)
      {
        std::cout << "Error in the input file\n";
        exit(1);
      };
      std::sort(B.begin(), B.end());
      A.clear();
      for (size_t i = 0; i < NELEM; ++i)
        A.push_back(B[NELEM - 1 - i]);
    };
    return A;
  };

  static vector<string> reverse_sorted_end(size_t NELEM,size_t n_last)
  {
    std::vector<std::string> A;
    A.reserve(NELEM);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NELEM+ n_last) != 0)
    {
      std::cout << "Error in the input file\n";
      exit(1);
    };
    std::sort (A.begin() , A.begin() + NELEM );
    for ( size_t i =0 ; i< (NELEM >>1); ++i)
      std::swap ( A[i], A[NELEM - 1 - i]);

    return A;

  };

  static vector<string> reverse_sorted_middle(size_t NELEM,size_t n_last)
  {
    std::vector<std::string> A,B,C;
    A.reserve(NELEM);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NELEM + n_last) != 0)
    {
      std::cout << "Error in the input file\n";
      exit(1);
    };
    for ( size_t i = NELEM ; i < A.size() ; ++i)
      B.push_back ( std::move ( A[i]));
    A.resize ( NELEM);

    std::sort (A.begin() , A.end() );
    for ( size_t i =0 ; i< (NELEM >>1); ++i)
      std::swap ( A[i], A[NELEM - 1 - i]);

    size_t step = NELEM /n_last +1 ;
    size_t pos = 0 ;

    for ( size_t i =0 ; i < B.size() ; ++i, pos += step)
    {   C.push_back ( B[i]);
      for ( size_t k = 0 ; k < step ; ++k )
        C.push_back ( A[pos + k] );
    };
    while ( pos < A.size() )
      C.push_back ( A[pos++]);
    A = C ;

    return A;
  };

public:


  static void stats(vector<string> &A) {
    auto B=A;

    // Sum up all string length
    size_t suml=0;
    for (auto i=B.begin();i<B.end();++i) suml+=i->size();

    // Count different values, min,max,avg length of strings
    std::sort(B.begin(),B.end());
    auto i = std::unique(B.begin(),B.end());
    B.resize(i-B.begin());

    size_t minl = B[0].size(),maxl = B[0].size();

    for (auto i=B.begin()+1;i!=B.end();++i) {
      minl=min(minl,i->size());
      maxl=max(maxl,i->size());
    }

    cout<<"# "<<A.size()<<" strings "<<B.size()<<" different. Lengths ["<<minl<<".."<<maxl<<"] avg: "<<suml/A.size()<<endl;
  }


  static vector<string> generate_aux(size_t NELEM, string name) {
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
      cout<<"No such string generator "<<name<<endl;
      exit(1);
    }
  }

  static vector<llstring> generate(size_t NELEM, string name) {
    auto A = generate_aux(NELEM,name);
    stats(A);
    return cnv_strvec(A);
  }

};


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

#endif

void test_uint(string name, size_t NITER, vector<uint64_t> B) {
  std::vector<uint64_t> A (B);

  auto comp = std::less<uint64_t>();
#ifndef NO_LLVM
  if (name=="isabelle::sort") sort_test(A,B,NITER,comp,[&]{ introsort(A.data (), 0, A.size());});
  else
#endif
  if (name=="std::sort") sort_test(A,B,NITER,comp,[&]{ std::sort(A.begin (), A.end (), comp);});
  else {
    cout<<"No such sorting algorithm "<<name<<endl;
    exit(1);
  }
}

#ifndef NO_LLVM
void test_llstring(string name, size_t NITER, vector<llstring> &B) {
  std::vector<llstring> A (B);

  auto comp = std::less<llstring>();

  if (name=="isabelle::sort") sort_test(A,B,NITER,comp,[&]{ str_introsort(A.data (), 0, A.size());});
  else if (name=="std::sort") sort_test(A,B,NITER,comp,[&]{ std::sort(A.begin (), A.end (), comp);});
  else {
    cout<<"No such sorting algorithm "<<name<<endl;
    exit(1);
  }
}
#endif

int main(int argc, char** argv) {

  if (argc != 6) {
    cout<<"Usage: do_benchmark type algo-name data-name NELEM NITER"<<endl;
    exit(1);
  }

  string type_name=argv[1];
  string algo_name=argv[2];
  string data_name=argv[3];
  size_t NELEM=stoul(argv[4]);
  size_t NITER=stoul(argv[5]);


  if (type_name == "uint64") {
    auto A = Int_Generator::generate(NELEM,data_name);
#ifdef NO_LLVM
    cout<<"NO_LLVM ";
#endif
    cout<<type_name<<" "<<algo_name<<" "<<data_name<<" "<<NELEM<<"x"<<NITER<<std::flush;
    test_uint(algo_name,NITER,A);
#ifndef NO_LLVM
  } else if (type_name == "llstring") {
    auto A = String_Generator::generate(NELEM,data_name);
    cout<<type_name<<" "<<algo_name<<" "<<data_name<<" "<<NELEM<<"x"<<NITER<<std::flush;
    test_llstring(algo_name,NITER,A);
#endif
  } else {
    cout<<"No such data type "<<type_name<<endl;
    exit(1);
  }



  return 0;
}












