// Re-used parts from BOOST sorting benchmark suite

#include <execution>

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

// #include <parallel/algo.h>

#include <tbb/tbb.h>

#include "pcg_rand/pcg_random.hpp"

#ifndef NO_LLVM
extern "C" {
  #include "introsort.h"
}
#endif



using namespace std;
namespace bsort = boost::sort;
namespace bsc = boost::sort::common;


// Disable branch-prediction optimization for all iterators, to make it comparable with our impl!
template<class Iter, class Compare>
inline void boost_pdqsort(Iter first, Iter last, Compare comp) {
    if (first == last) return;
    boost::sort::pdqsort_detail::pdqsort_loop<Iter, Compare, false >( first, last, comp, boost::sort::pdqsort_detail::log2(last - first));
}

template<class Iter>
inline void boost_pdqsort(Iter first, Iter last) {
    typedef typename std::iterator_traits<Iter>::value_type T;
    boost_pdqsort(first, last, std::less<T>());
}





//////////////////////////////////
// Parallel experiments
//////////////////////////////////

std::atomic<size_t> bad_partitions (0);
std::atomic<size_t> threads_spawned (0);
std::atomic<size_t> depth_limit (0);
std::atomic<size_t> big_partitions (0);
std::atomic<size_t> small_partitions (0);


template<typename I, typename Compare> I find_pivot(I first, I last, Compare comp) {
  size_t size = last-first;

  size_t num_samples = std::min ((size_t)std::__lg(size) * 4, (size_t)64);

  size_t samples[num_samples];

  size_t incr = (size-1) / num_samples;
  size_t extra = (size-1) % num_samples;
  size_t idx = 0;

  for (size_t i=0;i<num_samples;++i) {
    samples[i]=idx;
    idx += incr;
    if (extra) {++idx; --extra;}
  }




//   clog<<"Samples out of "<<size<<": ";
//   for (size_t i=0;i<num_samples;++i) clog<<samples[i]<<" ";
//   clog<<endl;
//
//   clog<<"Values: ";
//   for (size_t i=0;i<num_samples;++i) clog<< *(first+samples[i]) <<" ";
//   clog<<endl;


  std::sort(samples, samples+num_samples, [&](size_t i,size_t j){return comp(first+i,first+j);});
  size_t midx=samples[num_samples/2];


//   clog<<"Sorted samples: ";
//   for (size_t i=0;i<num_samples;++i) clog<<samples[i]<<" ";
//   clog<<endl;
//
//   clog<<"Values: ";
//   for (size_t i=0;i<num_samples;++i) clog<< *(first+samples[i]) <<" ";
//   clog<<endl;
//
//   clog<<"Median index: "<<midx<<endl;
//   clog<<"Median value: "<< *(first+midx) <<endl;


  return (first + midx);
}

template<typename I, typename Compare> void pivot_to_first(I first, I last, Compare comp) {
  I pvt = find_pivot(first,last,comp);
  std::iter_swap(first,pvt);
}


template<typename I, typename Compare> I my_partition2(I first, I last, I pivot, Compare comp) {
  assert (last-first > 4);
  I first0 = first;
  auto e0 = *first0; *first0=*pivot; ++first;
  --last;
  auto eN = *last; *last = *pivot;

  /*
   *  Now we have PVT ........... PVT
   *                  ^           ^
   *                  first       last
   */
  I mid = __unguarded_partition(first,last,first0,comp);

  // Move saved elements back in
  *first0 = e0;
  *last = eN;

  if (comp(pivot,first0)) {
    --mid;
    iter_swap(first0,mid);
  }

  if (comp(last,pivot)) {
    iter_swap(mid,last);
    ++mid;
  }

  return mid;
}


template<typename I, typename _Predicate>
  I
  my_partition(I __first, I __last,
              _Predicate __pred)
  {
    if (__first == __last)
      return __first;

    while (__pred(__first))
      if (++__first == __last)
        return __first;

    I __next = __first;

    while (++__next != __last)
      if (__pred(__next))
        {
          std::iter_swap(__first, __next);
          ++__first;
        }

    return __first;
  }


struct intv {
  size_t l;
  size_t h;

  intv(size_t __l, size_t __h) :l(__l), h(__h) {
    assert(l<=h);
  };

  bool is_empty() {return l==h;}

  bool contains(size_t i) {return l<=i && i<h; }

  size_t size() {return h-l;}
};

struct swap_t {
  size_t si;
  size_t di;
  size_t len;
};


template<typename F1, typename F2, typename R1, typename R2> pair<R1,R2> par(F1 f1, F2 f2) {
  // TODO: do proper initialization, most likely move function results to uninit result.

  R1 r1;
  R2 r2;

  auto f1r = [&]() { r1=f1(); };
  auto f2r = [&]() { r2=f2(); };

  tbb::parallel_invoke(f1r,f2r);

  return {r1,r2};
}


template<typename Result, typename I, typename Compute> vector<Result> simple_par_map(Compute f, I first, I last) {
  if (first==last) return vector<Result>();

  vector<future<Result>> vfuture;

  for (auto i = first; i<last; ++i) {vfuture.push_back(std::async(std::launch::async, f, *i)); ++threads_spawned; }

  vector<Result> res;

  for (auto &i : vfuture) res.push_back(i.get());

  return res;
}

template<typename I, typename Compute> void simple_par_it(Compute f, I first, I last) {
  vector<future<void>> vfuture;

  for (auto i = first; i<last; ++i) {vfuture.push_back(std::async(std::launch::async, f, *i)); ++threads_spawned; }

  for (auto &i : vfuture) i.get();
}

size_t get_num_blocks(size_t total_size, size_t chunk_size) {
  size_t d = total_size / chunk_size;
  if (d==0 || total_size % chunk_size > chunk_size/2) d++;

  assert(d>0);

  return d;
}


vector<vector<swap_t>> rebalance_swaps(vector<swap_t> & swaps) {
  // Compute total size
  size_t tlen = 0; for (auto &s : swaps) tlen+=s.len;
  size_t chunk_size=1000000;

  vector<vector<swap_t>> res;
  auto c = swaps.begin();
  auto end = swaps.end();

  vector<swap_t> tc;
  while (c!=end) {
    tc.clear();

    size_t cs=chunk_size;

    while (c!=end && cs) {
      if (c->len <= cs) { // Take swap if it still fits in size-limit
        tc.push_back(*c);
        cs-=c->len;
        ++c; // We've taken the whole swap
        continue;
      }

      if (c->len <= cs + chunk_size/4) { // Allow slack of 1/4 chunk_size, to avoid splitting the swap
        tc.push_back(*c);
        cs=0;
        ++c; // We've taken the whole swap
        continue;
      }

      // Otherwise, split the swap
      assert(c->len > cs);

      tc.push_back(swap_t{c->si, c->di, cs});
      c->len-=cs;
      c->si+=cs;
      c->di+=cs;

      cs=0;
    }

    assert(tc.size());
    res.push_back(tc);
  }

  return res;
}

template<typename I> void do_swap(I it, swap_t s) {
  assert(s.si + s.len <= s.di || s.di + s.len <= s.si ); // Assert non-overlapping
  swap_ranges(it + s.si, it + s.si + s.len, it + s.di);
};

template<typename I> void do_swaps(I it, vector<swap_t> &ss) {
  for (auto s : ss) do_swap(it,s);
};


template<typename I, typename Compare> I par_partition(I first, I last, I pivot, Compare comp) {

  // auto comp_pivot = [&](I &b){ return comp(b,pivot); };

  size_t chunk_size=1000000;

  vector<intv> lows;
  vector<intv> highs;

  size_t n = last - first;

//   clog<<"par_partition with size "<<n<<endl;

  { // Determine number of chunks
    size_t d = n / chunk_size;
    if (d==0 || n % chunk_size > chunk_size/2) d++;

    assert(d>0);

    // (Parallel) partition the chunks
    size_t r = n % d;
    size_t c = n / d;

    {
      size_t i = 0;

//       auto do_partition = [&](std::pair<I,I> lh) { return my_partition2(lh.first,lh.second,comp_pivot); };
      auto do_partition = [&](std::pair<I,I> lh) { return my_partition2(lh.first,lh.second,pivot,comp); };

      vector<std::pair<I,I>> partition_jobs;

      while (i<n) {
        size_t l = i;
        i=i+c;
        if (r) {
          --r;
          ++i;
        }

        size_t h=i;

        {
          I li = first + l;
          I hi = first + h;

          partition_jobs.push_back({li,hi});

//           I mi = my_partition(li,hi,comp_pivot);
//
//           size_t m = mi - first;
//
//           lows.push_back(intv(l,m));
//           highs.push_back(intv(m,h));
        }
      }
      assert (i==n);

      // Execute partition jobs
//       vector<I> partition_results;
//       for (auto job : partition_jobs) partition_results.push_back(do_partition(job));

      vector<I> partition_results = simple_par_map<I>(do_partition, partition_jobs.begin(),partition_jobs.end());


      // Gather results
      for (size_t i=0;i<partition_results.size();++i) {
        size_t l = partition_jobs[i].first - first;
        size_t h = partition_jobs[i].second - first;
        size_t m = partition_results[i] - first;

        lows.push_back(intv(l,m));
        highs.push_back(intv(m,h));
      }


    }
  }

  // Determine middle position
  size_t m=0; for (auto i : lows) m+=i.size();


  { // Sanity check
    size_t mm=0; for (auto i : highs) mm+=i.size();

    assert (m+mm == n);
  }

  // Determine out-of-order intervals
  vector<intv> lows2;
  vector<intv> highs2;

  // Filter non-empty lows above mid-line. split first one if necessary
  for (auto i : lows) {
    if (i.is_empty()) continue;
    if (i.h <= m) continue;

    if (i.contains(m)) lows2.push_back(intv(m,i.h));
    else lows2.push_back(i);
  }

  // Filter highs below mid-line, split last if necessary
  for (auto i : highs) {
    if (i.is_empty()) continue;
    if (i.l >= m) continue;

    if (i.contains(m)) highs2.push_back(intv(i.l,m));
    else highs2.push_back(i);
  }

  // Compute swaps
  auto cl = lows2.begin();
  auto ch = highs2.begin();

  vector<swap_t> swaps;

  size_t total_swap_len = 0;

  while (cl != lows2.end()) {
    assert (ch != highs2.end());

    size_t len = min(cl->size(),ch->size());
    assert(len);

    swaps.push_back({cl->l,ch->l,len});

    total_swap_len+=len;

    cl->l+=len; ch->l+=len;
    if (cl->is_empty()) cl++;
    if (ch->is_empty()) ch++;

  }
  assert (ch == highs2.end());

  // Balance the swaps onto available threads (or by block-size)
  // Do the swaps
  // auto swapss = rebalance_swaps(swaps);

  // Replaced by simple version for checking how important balancing is

  vector<vector<swap_t>> swapss;
  for (auto i : swaps) swapss.push_back({i});

//   clog<<"Doing "<<swapss.size()<<" swap jobs with total len "<<total_swap_len<<endl;

  simple_par_it([&](vector<swap_t> ss) { do_swaps(first,ss); },swapss.begin(),swapss.end());


//   clog<<"Doing "<<swaps.size()<<" swap jobs with total len "<<total_swap_len<<endl;

//   auto do_swap = [&](swap_t s) {
//     assert(s.si + s.len <= s.di || s.di + s.len <= s.si ); // Assert non-overlapping
//     swap_ranges(first + s.si, first + s.si + s.len, first + s.di);
//   };
//
//   simple_par_it(do_swap,swaps.begin(),swaps.end());

//   for ( auto s : swaps ) do_swap(s);

//   for ( auto s : swaps ) {
//     assert(s.si + s.len <= s.di || s.di + s.len <= s.si ); // Assert non-overlapping
//     swap_ranges(first + s.si, first + s.si + s.len, first + s.di);
//   }

  return first + m;
}







template<typename I, typename Compare> I partition_pivot(I first, I last, Compare comp) {
  pivot_to_first(first,last,comp);
  return std::__unguarded_partition(first + 1,last, first, comp);
}

template<typename I, typename Compare> I partition_pivot_parallel(I first, I last, Compare comp) {
  pivot_to_first(first,last,comp);

//   // Estimate how much is lost by less efficient (guarded) partitioning
//   auto comp_pivot = [&](I &b){ return comp(b,first); };
//   return my_partition(first + 1,last, comp_pivot);

  return par_partition(first + 1,last, first, comp);
}



/// This is a helper function for the sort routine.
template<typename I, typename Compare> void par_isort_aux(I first, I last, Compare comp, size_t d)
  {
    size_t size = last-first;

    if (d==0) {
      ++depth_limit;
    }

    if (size < 10000 || d == 0) {
      ++small_partitions;
      std::sort(first,last,comp);
    } else {
      I cut = std::__unguarded_partition_pivot(first, last, __gnu_cxx::__ops::__iter_comp_iter(comp));
      ++big_partitions;

      bool bad_partition = cut - first < size/8 || last-cut < size/8;

      if (bad_partition) {
        par_isort_aux(first,cut,comp,d-1);
        par_isort_aux(cut,last,comp,d-1);
        ++bad_partitions;
      } else {
        auto s1 = std::async(std::launch::async, par_isort_aux<I,Compare>, first,cut,comp,d-1);
        par_isort_aux(cut,last,comp,d-1);
        s1.get();
        ++threads_spawned;
      }

    }
  }

template<typename I, typename Compare> void par_isort_aux2(I first, I last, Compare comp, size_t d)
  {
    size_t size = last-first;

    if (d==0) {
      ++depth_limit;
    }

    if (size < 100000 || d == 0) {
      ++small_partitions;
      //std::__sort(first,last,comp);
      boost_pdqsort(first,last,comp);

    } else {
      ++big_partitions;
      I cut = partition_pivot(first, last, __gnu_cxx::__ops::__iter_comp_iter(comp));

//       clog<<"Partition: "<<cut - first<<"  "<<last-cut<<endl;

      bool bad_partition = cut - first < size/8 || last-cut < size/8;

      if (bad_partition) {
        par_isort_aux2(first,cut,comp,d-1);
        par_isort_aux2(cut,last,comp,d-1);
        ++bad_partitions;
      } else {

        tbb::parallel_invoke( [=]{par_isort_aux2(first,cut,comp,d-1); }, [=]{par_isort_aux2(cut,last,comp,d-1); } );

//         auto s1 = std::async(std::launch::async, par_isort_aux2<I,Compare>, first,cut,comp,d-1);
//         par_isort_aux2(cut,last,comp,d-1);
//         s1.get();
        ++threads_spawned;
      }

    }
  }


template<typename I, typename Compare> void par_isort_aux3(size_t par_min_size, I first, I last, Compare comp, size_t d)
  {
    size_t size = last-first;

//     clog<<"Partition ("<<d<<"): "<<size<<endl;

    if (d==0) {
      ++depth_limit;
    }

    if (size < par_min_size || d == 0) {
      ++small_partitions;
      //std::__sort(first,last,comp);
      boost_pdqsort(first,last,comp);

    } else {
      ++big_partitions;
      I cut = partition_pivot(first, last, __gnu_cxx::__ops::__iter_comp_iter(comp));

//       clog<<"Partition: "<<cut - first<<"  "<<last-cut<<endl;

      bool bad_partition = cut - first < size/8 || last-cut < size/8;

      if (bad_partition) {
        par_isort_aux3(par_min_size,first,cut,comp,d-1);
        par_isort_aux3(par_min_size,cut,last,comp,d-1);
        ++bad_partitions;
      } else {
        auto s1 = std::async(std::launch::async, par_isort_aux3<I,Compare>, par_min_size, first,cut,comp,d-1);
        par_isort_aux3(par_min_size, cut,last,comp,d-1);
        s1.get();
        ++threads_spawned;
      }

    }
  }


template<typename I, typename Compare> void par_isort_aux_pp(size_t par_min_size, I first, I last, Compare comp, size_t d)
  {
    size_t size = last-first;

//     clog<<"Partition ("<<d<<"): "<<size<<endl;

    if (d==0) {
      ++depth_limit;
    }

    if (size < par_min_size || d == 0) {
      ++small_partitions;
      //std::__sort(first,last,comp);
      boost_pdqsort(first,last,comp);

    } else {
      ++big_partitions;
      I cut = partition_pivot_parallel(first, last, __gnu_cxx::__ops::__iter_comp_iter(comp));

//       clog<<"Partition: "<<cut - first<<"  "<<last-cut<<endl;

      bool bad_partition = cut - first < size/8 || last-cut < size/8;

      if (bad_partition) {
        par_isort_aux_pp(par_min_size,first,cut,comp,d-1);
        par_isort_aux_pp(par_min_size,cut,last,comp,d-1);
        ++bad_partitions;
      } else {
        auto s1 = std::async(std::launch::async, par_isort_aux_pp<I,Compare>, par_min_size, first,cut,comp,d-1);
        par_isort_aux_pp(par_min_size, cut,last,comp,d-1);
        s1.get();
        ++threads_spawned;
      }

    }
  }



template<typename I, typename Compare> void par_isort(I first, I last, Compare comp)
{
  big_partitions=0;
  small_partitions=0;
  bad_partitions=0;
  threads_spawned=0;
  depth_limit=0;

  par_isort_aux2(first, last, comp, std::__lg(last - first) * 2);


//   clog<<std::endl;
//   clog<<"Big partitions: "<<big_partitions<<std::endl;
//   clog<<"Small partitions: "<<small_partitions<<std::endl;
//   clog<<"Bad partitions: "<<bad_partitions<<std::endl;
//   clog<<"Threads spawned: "<<threads_spawned<<std::endl;
//   clog<<"Depth limit reached: "<<depth_limit<<std::endl;
}


template<typename I, typename Compare> void par_isort_vs(I first, I last, Compare comp, size_t nthreads = 0)
{
  big_partitions=0;
  small_partitions=0;
  bad_partitions=0;
  threads_spawned=0;
  depth_limit=0;


  if (nthreads==0) nthreads = std::thread::hardware_concurrency();

  size_t size = last-first;

  size_t par_min_size = max(size / (nthreads*4), (size_t)100000);

  par_isort_aux3(par_min_size, first, last, comp, std::__lg(last - first) * 2);


//   clog<<std::endl;
//   clog<<"nthreads: "<<nthreads<<endl;
//   clog<<"par_min_size: "<<par_min_size<<endl;
//
//   clog<<"Big partitions: "<<big_partitions<<std::endl;
//   clog<<"Small partitions: "<<small_partitions<<std::endl;
//   clog<<"Bad partitions: "<<bad_partitions<<std::endl;
//   clog<<"Threads spawned: "<<threads_spawned<<std::endl;
//   clog<<"Depth limit reached: "<<depth_limit<<std::endl;
}

template<typename I, typename Compare> void par_isort_vs_pp(I first, I last, Compare comp, size_t nthreads = 0)
{
  big_partitions=0;
  small_partitions=0;
  bad_partitions=0;
  threads_spawned=0;
  depth_limit=0;


  if (nthreads==0) nthreads = std::thread::hardware_concurrency();

  size_t size = last-first;

  size_t par_min_size = max(size / (nthreads*4), (size_t)100000);

  par_isort_aux_pp(par_min_size, first, last, comp, std::__lg(last - first) * 2);


  clog<<std::endl;
  clog<<"nthreads: "<<nthreads<<endl;
  clog<<"par_min_size: "<<par_min_size<<endl;

  clog<<"Big partitions: "<<big_partitions<<std::endl;
  clog<<"Small partitions: "<<small_partitions<<std::endl;
  clog<<"Bad partitions: "<<bad_partitions<<std::endl;
  clog<<"Threads spawned: "<<threads_spawned<<std::endl;
  clog<<"Depth limit reached: "<<depth_limit<<std::endl;
}






template<typename I> class psort_data {
  I first;
  I last;
  size_t t;

  size_t n;
  size_t d;
  size_t r;


  size_t ridx(size_t i) {
    assert (i<=n);
    if (i<=r) return i*(d+1);
    else return r + i*d;
  }

public:
  psort_data(I _first, I _last, size_t _t): first(_first), last(_last), t(_t) {
    n = last-first;
    d = n / t;
    r = n % t;


    assert(ridx(0) == 0);
    assert(ridx(t) == n);

    for (size_t i=0;i<t;++i) assert(ridx(i) < ridx(i+1));

  }


  I rstart(size_t i) {
    return first + ridx(i);
  }

  template<typename Compare> void do_psort(size_t l, size_t h, Compare comp) {
    assert(l<h);

    if (l+1==h) {
      // boost_pdqsort(rstart(l),rstart(h),comp);
      boost::sort::spinsort<I, Compare>(rstart(l),rstart(h), comp);
    } else {
      size_t m=(l+h)/2;

      tbb::parallel_invoke( [=]{ do_psort(l,m,comp); }, [=]{ do_psort(m,h,comp); } );

//       // Copy data to buffer
//       std::vector v(rstart(l),rstart(h));
//
//       // A bit of arithmetic to find bounds
//
//       auto vl = v.begin();
//       auto vm = v.begin() + (ridx(m)-ridx(l));
//       auto vh = v.begin() + (ridx(h)-ridx(l));

      // Merge back

      //std::merge(vl,vm,vm,vh,rstart(l));

      std::inplace_merge(std::execution::par_unseq, rstart(l), rstart(m), rstart(h), comp);
    }
  }



};


template<typename I, typename Compare> void psort(I first, I last, Compare comp, size_t t = std::thread::hardware_concurrency()) {
  psort_data<I> d(first,last,t);
  d.do_psort(0,t,comp);
}



extern "C" {
  void isabelle_llvm_parallel(void (*f1)(void*), void (*f2)(void*), void *x1, void *x2) {
    tbb::parallel_invoke([=]{f1(x1);}, [=]{f2(x2);});

    // auto s1 = std::async(std::launch::async, f1,x1);
//     f2(x2);
//     s1.get();
  }



}


/////////////////////////////////



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

  // using namespace oneapi::tbb;

  class Apply_Fill_Vector {
      uint64_t *this_a;
  public:
      void operator()( const tbb::blocked_range<size_t>& r ) const {
        //std::mt19937_64 my_rand(r.begin());

        pcg64 my_rand(r.begin());


        clog<<"Chunk size: "<<(r.end()-r.begin())<<endl;

        uint64_t *a = this_a;
        for( size_t i=r.begin(); i!=r.end(); ++i ) a[i]=my_rand();
      }
      Apply_Fill_Vector( uint64_t a[] ) : this_a(a)
      {}
  };


  static void fill_vector_direct_par(vector<uint64_t> &v, size_t n) {
    assert(v.size() >= n);
    size_t grain_size=100000;
    clog<<"Filling vector"<<endl;
    tbb::parallel_for(tbb::blocked_range<size_t>(0,n,grain_size), Apply_Fill_Vector(v.data()),tbb::simple_partitioner());
    clog<<"Done"<<endl;
  }


  static void fill_vector_direct(vector<uint64_t> &v, size_t n, uint64_t seed=0) {
    std::mt19937_64 my_rand(seed);

    for (size_t i = 0;i<n; ++i) v.push_back(my_rand());
  }



  static vector<uint64_t> random(size_t NELEM) {
//     vector<uint64_t> A(NELEM);
//     fill_vector_direct_par(A,NELEM);
    clog<<"Filling vector"<<endl;

    vector<uint64_t> A;
    A.reserve (NELEM);
    A.clear ();
//     fill_vector_direct(A,NELEM);
    if (fill_vector_uint64 ("input.bin", A, NELEM) != 0)
    {
        std::cout << "Error in the input file\n";
        exit(1);
    };
    clog<<"Done"<<endl;
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
  else if (name=="isabelle::parqsort") sort_test(A,B,NITER,comp,[&]{ par_sort(A.data (), A.size());  });
  else if (name=="isabelle::pparqsort") sort_test(A,B,NITER,comp,[&]{ ppar_sort(A.data (), A.size());  });
  else if (name=="isabelle::pdqsort") sort_test(A,B,NITER,comp,[&]{ pdqsort(A.data (), 0, A.size());});
  else
#endif
  if (name=="std::sort") sort_test(A,B,NITER,comp,[&]{ std::sort(A.begin (), A.end (), comp);});
  else if (name=="std::parsort") sort_test(A,B,NITER,comp,[&]{
    //std::sort(A.begin (), A.end (), comp,__gnu_parallel::quicksort_tag());
    std::sort(std::execution::par_unseq,A.begin (), A.end (), comp);
  });
  else if (name=="boost::pdqsort") sort_test(A,B,NITER,comp,[&]{ boost_pdqsort(A.begin (), A.end (), comp);});
  else if (name=="boost::pdqsort_bp") sort_test(A,B,NITER,comp,[&]{ boost::sort::pdqsort(A.begin (), A.end ());});
  else if (name=="boost::sample_sort") sort_test(A,B,NITER,comp,[&]{ boost::sort::sample_sort(A.begin (), A.end (), comp);});
  else if (name=="boost::bi_sort") sort_test(A,B,NITER,comp,[&]{ boost::sort::block_indirect_sort(A.begin (), A.end (), comp);});
  else if (name=="naive::parqsort") sort_test(A,B,NITER,comp,[&]{ par_isort(A.begin (), A.end (), comp);});
  else if (name=="naive::psort") sort_test(A,B,NITER,comp,[&]{ psort(A.begin (), A.end (), comp);});
  else if (name=="naive::parqsort_vs") sort_test(A,B,NITER,comp,[&]{ par_isort_vs(A.begin (), A.end (), comp);});
  else if (name=="naive::parqsort_vs_pp") sort_test(A,B,NITER,comp,[&]{ par_isort_vs_pp(A.begin (), A.end (), comp);});
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
  else if (name=="isabelle::parqsort") sort_test(A,B,NITER,comp,[&]{ str_par_sort(A.data (), A.size());  });
  else if (name=="isabelle::pparqsort") sort_test(A,B,NITER,comp,[&]{ str_ppar_sort(A.data (), A.size());  });
  else if (name=="isabelle::pdqsort") sort_test(A,B,NITER,comp,[&]{ str_pdqsort(A.data (), 0, A.size());});
  else if (name=="boost::pdqsort") sort_test(A,B,NITER,comp,[&]{ boost_pdqsort(A.begin (), A.end (), comp);});
  else if (name=="std::sort") sort_test(A,B,NITER,comp,[&]{ std::sort(A.begin (), A.end (), comp);});
  else if (name=="std::parsort") sort_test(A,B,NITER,comp,[&]{ std::sort(std::execution::par_unseq, A.begin (), A.end (), comp);});
  else if (name=="boost::sample_sort") sort_test(A,B,NITER,comp,[&]{ boost::sort::sample_sort(A.begin (), A.end (), comp);});
  else if (name=="boost::bi_sort") sort_test(A,B,NITER,comp,[&]{ boost::sort::block_indirect_sort(A.begin (), A.end (), comp);});
  else if (name=="naive::parqsort") sort_test(A,B,NITER,comp,[&]{ par_isort(A.begin (), A.end (), comp);});
  else if (name=="naive::parqsort_vs") sort_test(A,B,NITER,comp,[&]{ par_isort_vs(A.begin (), A.end (), comp);});
  else if (name=="naive::parqsort_vs_pp") sort_test(A,B,NITER,comp,[&]{ par_isort_vs_pp(A.begin (), A.end (), comp);});
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












