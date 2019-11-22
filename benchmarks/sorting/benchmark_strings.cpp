//----------------------------------------------------------------------------
/// @file benchmark_strings.cpp
/// @brief Benchmark of several sort methods with strings
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
#include "boost/sort/common/int_array.hpp"

#include <boost/sort/sort.hpp>

extern "C" {
  #include "introsort.h"
}


#define NMAXSTRING 1000000

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

void Generator_random (void);
void Generator_sorted(void);
void Generator_sorted_end(size_t n_last);
void Generator_sorted_middle (size_t n_last);
void Generator_reverse_sorted(void);
void Generator_reverse_sorted_end(size_t n_last);
void Generator_reverse_sorted_middle(size_t n_last);

template <class IA, class compare>
int Test(std::vector<IA> &B, compare comp = compare());

static int compare (const unsigned char* p, const unsigned char* q, size_t n) {
  while (n--) {if (*p != *q) return (*p < *q)?-1:1; ++p; ++q;}
  return 0;
}

static inline int compare2 (const unsigned char* p, const unsigned char* q, size_t n) {
  size_t i=0;
  int r = 0;

  while (i<n && r==0) {
    if (p[i]==q[i]) ++i;
    else if (p[i]<q[i]) {++i; r=-1;}
    else {++i; r=1;}
  }

  return r;
}


inline bool cvec_cmp(const vector<unsigned char> &a, const vector<unsigned char> &b) {
  size_t n;
  if (a.size() < b.size()) n=a.size(); else n=b.size();
//   auto n = min(a.size(),b.size());

  auto r = compare2(a.data(),b.data(),n);

  if (r==-1) return true;
  else if (r==0) return (a.size() < b.size());
  else return false;

}


// bool llstrcmp2(llstring &a,llstring &b) {
//   auto n = min(a.size,b.size);
//
//   auto r = compare2(a.data,b.data,n);
//
//   if (r==-1) return true;
//   else if (r==0) return (a.size() < b.size());
//   else return false;
// }
//





vector<vector<unsigned char>> strvec2cvec(vector<string> v) {
  vector<vector<unsigned char>> r;
  r.reserve(v.size());
  for (auto i=v.begin();i!=v.end();++i) {
    vector<unsigned char> x(i->begin(),i->end());
    r.push_back(x);
  }

  return r;
}


vector<string> cvec2strvec(vector<vector<unsigned char>> v) {
  vector<string> r;
  r.reserve(v.size());
  for (auto i=v.begin();i!=v.end();++i) {
    string x(i->begin(),i->end());
    r.push_back(x);
  }

  return r;
}




int main(int argc, char *argv[])
{
    cout << "\n\n";
    cout << "************************************************************\n";
    cout << "**                                                        **\n";
    cout << "**               B O O S T      S O R T                   **\n";
    cout << "**              S I N G L E    T H R E A D                **\n";
    cout << "**            S T R I N G S   B E N C H M A R K           **\n";
    cout << "**                                                        **\n";
    cout << "**       S O R T   O F  10 000 000   S T R I N G S        **\n";
    cout << "**                                                        **\n";
    cout << "************************************************************\n";
    cout << std::endl;

    cout<<"[ 1 ] std::sort   [ 2 ] pdqsort          [ 3 ] std::stable_sort \n";
    cout<<"[ 4 ] spinsort    [ 5 ] flat_stable_sort [ 6 ] spreadsort\n\n";
    cout<<"                    |      |      |      |      |      |      |\n";
    cout<<"                    | [ 1 ]| [ 2 ]| [ 3 ]| [ 4 ]| [ 5 ]| [ 6 ]|\n";
    cout<<"--------------------+------+------+------+------+------+------+\n";
    std::string empty_line =
           "                    |      |      |      |      |      |      |\n";



    cout<<"random              |";
    Generator_random ();

    cout<<empty_line;
    cout<<"sorted              |";
    Generator_sorted();

    cout<<"sorted + 0.1% end   |";
    Generator_sorted_end(NMAXSTRING / 1000);

    cout<<"sorted +   1% end   |";
    Generator_sorted_end(NMAXSTRING / 100);

    cout<<"sorted +  10% end   |";
    Generator_sorted_end(NMAXSTRING / 10);

    cout<<empty_line;
    cout<<"sorted + 0.1% mid   |";
    Generator_sorted_middle (NMAXSTRING / 1000);

    cout<<"sorted +   1% mid   |";
    Generator_sorted_middle (NMAXSTRING / 100);

    cout<<"sorted +  10% mid   |";
    Generator_sorted_middle (NMAXSTRING / 10 );

    cout<<empty_line;
    cout<<"reverse sorted      |";
    Generator_reverse_sorted();

    cout<<"rv sorted + 0.1% end|";
    Generator_reverse_sorted_end(NMAXSTRING / 1000);

    cout<<"rv sorted +   1% end|";
    Generator_reverse_sorted_end(NMAXSTRING / 100);

    cout<<"rv sorted +  10% end|";
    Generator_reverse_sorted_end(NMAXSTRING / 10);

    cout<<empty_line;
    cout<<"rv sorted + 0.1% mid|";
    Generator_reverse_sorted_middle(NMAXSTRING / 1000);

    cout<<"rv sorted +   1% mid|";
    Generator_reverse_sorted_middle(NMAXSTRING / 100);

    cout<<"rv sorted +  10% mid|";
    Generator_reverse_sorted_middle(NMAXSTRING / 10);

    cout<<"--------------------+------+------+------+------+------+------+\n";
    cout<<endl<<endl ;
    return 0;
}

void Generator_random(void)
{
    std::vector<std::string> A;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    Test<std::string, std::less<std::string>>(A);

};
void Generator_sorted(void)
{
    std::vector<std::string> A;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    std::sort( A.begin() , A.end() );
    Test<std::string, std::less<std::string>>(A);
};

void Generator_sorted_end(size_t n_last)
{
    std::vector<std::string> A;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING+ n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    std::sort (A.begin() , A.begin() + NMAXSTRING );
    Test<std::string, std::less<std::string>>(A);
};
void Generator_sorted_middle(size_t n_last)
{
    std::vector<std::string> A,B,C;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    for ( size_t i = NMAXSTRING ; i < A.size() ; ++i)
        B.push_back ( std::move ( A[i]));
    A.resize ( NMAXSTRING);
    std::sort (A.begin() , A.end() );
    size_t step = NMAXSTRING /n_last +1 ;
    size_t pos = 0 ;

    for ( size_t i =0 ; i < B.size() ; ++i, pos += step)
    {   C.push_back ( B[i]);
        for ( size_t k = 0 ; k < step ; ++k )
            C.push_back ( A[pos + k] );
    };
    while ( pos < A.size() ) C.push_back ( A[pos++]);
    A = C ;

    Test<std::string, std::less<std::string>>(A);
};

void Generator_reverse_sorted(void)
{

    std::vector<std::string> A;
    A.reserve(NMAXSTRING);
    {
        std::vector<std::string> B;
        B.reserve(NMAXSTRING);
        if (bsc::fill_vector_string("input.bin", B, NMAXSTRING) != 0)
        {
            std::cout << "Error in the input file\n";
            return;
        };
        std::sort(B.begin(), B.end());
        A.clear();
        for (size_t i = 0; i < NMAXSTRING; ++i)
            A.push_back(B[NMAXSTRING - 1 - i]);
    };
    Test<std::string, std::less<std::string>>(A);

/*
    std::vector<std::string> A;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    std::sort( A.begin() , A.end());
    size_t nmid = (A.size() >>1), nlast = A.size() -1 ;
    for (size_t i = 0 ; i < nmid ;++i)
        std::swap ( A[i], A [nlast -i]);

    Test<std::string, std::less<std::string>>(A);
*/
};
void Generator_reverse_sorted_end(size_t n_last)
{
    std::vector<std::string> A;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING+ n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    std::sort (A.begin() , A.begin() + NMAXSTRING );
    for ( size_t i =0 ; i< (NMAXSTRING >>1); ++i)
        std::swap ( A[i], A[NMAXSTRING - 1 - i]);

    Test<std::string, std::less<std::string>>(A);

};
void Generator_reverse_sorted_middle(size_t n_last)
{
    std::vector<std::string> A,B,C;
    A.reserve(NMAXSTRING);
    A.clear();
    if (bsc::fill_vector_string("input.bin", A, NMAXSTRING + n_last) != 0)
    {
        std::cout << "Error in the input file\n";
        return;
    };
    for ( size_t i = NMAXSTRING ; i < A.size() ; ++i)
        B.push_back ( std::move ( A[i]));
    A.resize ( NMAXSTRING);

    std::sort (A.begin() , A.end() );
    for ( size_t i =0 ; i< (NMAXSTRING >>1); ++i)
        std::swap ( A[i], A[NMAXSTRING - 1 - i]);

    size_t step = NMAXSTRING /n_last +1 ;
    size_t pos = 0 ;

    for ( size_t i =0 ; i < B.size() ; ++i, pos += step)
    {   C.push_back ( B[i]);
        for ( size_t k = 0 ; k < step ; ++k )
            C.push_back ( A[pos + k] );
    };
    while ( pos < A.size() )
        C.push_back ( A[pos++]);
    A = C ;

    Test<std::string, std::less<std::string>>(A);
};

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

string bcnv_str(llstring s) {
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

template<class T> void output_firsts(vector<T> &x) {
  cout<<endl;
  for (size_t i = 0; i < std::min((size_t)5,x.size()); ++i) cout<<x[i]<<",";
  cout<<endl;
}

template<class IA, class compare>
int Test (std::vector<IA> &B,  compare comp)
{   //---------------------------- begin -----------------------------
    double duration;
    time_point start, finish;
    std::vector<IA> A (B);
    std::vector<double> V;


//     A = B;
//     start = now ();
//     std::sort (A.begin (), A.end (), comp);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//

    std::vector<llstring> AA = cnv_strvec(B);
    start = now ();
    std::sort (AA.begin (), AA.end (), [](llstring &a,llstring &b){return llstrcmp(&a,&b);});
    finish = now ();
    duration = subtract_time (finish, start);
    V.push_back (duration);
    A = bcnv_strvec(AA);
    test_sorted("std::sort",A,comp);


    AA = cnv_strvec(B);
    start = now ();
    str_introsort (AA.data (), 0, AA.size ());
    finish = now ();
    duration = subtract_time (finish, start);
    V.push_back (duration);
    A = bcnv_strvec(AA);
    test_sorted("ll_introsort",A,comp);

//     vector<vector<unsigned char>> AX = strvec2cvec(B);
//     start = now ();
//     std::sort (AX.begin (), AX.end (), cvec_cmp);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//
//     A = cvec2strvec(AX);
//     test_sorted("std::sort<vector<char>>",A,comp);
//

//     xxx: why is C++ vecrtor comparison faster? Is LLVM missing optimization on our impl?
//
//     xxx, compare c-strings


//     A = B;
//     start = now ();
//     pdqsort (A.begin (), A.end (), comp);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//
//     A = B;
//     start = now ();
//     std::stable_sort (A.begin (), A.end (), comp);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//
//     A = B;
//     start = now ();
//     spinsort (A.begin (), A.end (), comp);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//
//     A = B;
//     start = now ();
//     flat_stable_sort (A.begin (), A.end (), comp);
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);
//
//     A = B;
//     start = now ();
//     spreadsort (A.begin (), A.end ());
//     finish = now ();
//     duration = subtract_time (finish, start);
//     V.push_back (duration);

    //-----------------------------------------------------------------------
    // printing the vector
    //-----------------------------------------------------------------------
    std::cout<<std::setprecision(2)<<std::fixed;
    for ( uint32_t i =0 ; i < V.size() ; ++i)
    {   std::cout<<std::right<<std::setw(5)<<V[i]<<" |";
    };
    std::cout<<std::endl;
    return 0;
};

