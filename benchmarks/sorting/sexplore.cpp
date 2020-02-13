
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

#include "int_generator.h"


const size_t N = 100000000;

// const size_t N = 1000;

using namespace std;
namespace bsort = boost::sort;
namespace bsc = boost::sort::common;

#define BOOST_PDQSORT_PREFER_MOVE(x) std::move(x)

#define STAT_INCR(x) ++x
// #define STAT_INCR(x)

class sort_stat {
public:
  size_t bad = 0;
  size_t heapsort = 0;
  size_t leftp = 0;
  size_t ap = 0;
  size_t ap_sorted = 0;
  size_t small=0;

  void reset() {
    bad = 0;
    heapsort = 0;
    leftp = 0;
    ap = 0;
    ap_sorted = 0;
    small=0;
  }

  void print() {
    cout<<"bad: "<<bad<<endl;
    cout<<"heapsort: "<<heapsort<<endl;
    cout<<"leftp: "<<leftp<<endl;
    cout<<"ap: "<<ap<<endl;
    cout<<"ap_sorted: "<<ap_sorted<<endl;
    cout<<"small: "<<small<<endl;
  }
};

sort_stat mystat;
sort_stat pdqstat;


namespace pdqcopy {
  using namespace boost;
  using namespace boost::sort;

    enum {
        // Partitions below this size are sorted using insertion sort.
        insertion_sort_threshold = 24,

        // Partitions above this size use Tukey's ninther to select the pivot.
        ninther_threshold = 128,

        // When we detect an already sorted partition, attempt an insertion sort that allows this
        // amount of element moves before giving up.
        partial_insertion_sort_limit = 8,

        // Must be multiple of 8 due to loop unrolling, and < 256 to fit in unsigned char.
        block_size = 64,

        // Cacheline size, assumes power of two.
        cacheline_size = 64
    };

    template<class T> struct is_default_compare : boost::false_type { };
    template<class T> struct is_default_compare<std::less<T> > : boost::true_type { };
    template<class T> struct is_default_compare<std::greater<T> > : boost::true_type { };

    // Returns floor(log2(n)), assumes n > 0.
    template<class T>
    inline int log2(T n) {
        int log = 0;
        while (n >>= 1) ++log;
        return log;
    }

    // Sorts [begin, end) using insertion sort with the given comparison function.
    template<class Iter, class Compare>
    inline void insertion_sort(Iter begin, Iter end, Compare comp) {
        typedef typename std::iterator_traits<Iter>::value_type T;
        if (begin == end) return;

        for (Iter cur = begin + 1; cur != end; ++cur) {
            Iter sift = cur;
            Iter sift_1 = cur - 1;

            // Compare first so we can avoid 2 moves for an element already positioned correctly.
            if (comp(*sift, *sift_1)) {
                T tmp = BOOST_PDQSORT_PREFER_MOVE(*sift);

                do { *sift-- = BOOST_PDQSORT_PREFER_MOVE(*sift_1); }
                while (sift != begin && comp(tmp, *--sift_1));

                *sift = BOOST_PDQSORT_PREFER_MOVE(tmp);
            }
        }
    }

    // Sorts [begin, end) using insertion sort with the given comparison function. Assumes
    // *(begin - 1) is an element smaller than or equal to any element in [begin, end).
    template<class Iter, class Compare>
    inline void unguarded_insertion_sort(Iter begin, Iter end, Compare comp) {
        typedef typename std::iterator_traits<Iter>::value_type T;
        if (begin == end) return;

        for (Iter cur = begin + 1; cur != end; ++cur) {
            Iter sift = cur;
            Iter sift_1 = cur - 1;

            // Compare first so we can avoid 2 moves for an element already positioned correctly.
            if (comp(*sift, *sift_1)) {
                T tmp = BOOST_PDQSORT_PREFER_MOVE(*sift);

                do { *sift-- = BOOST_PDQSORT_PREFER_MOVE(*sift_1); }
                while (comp(tmp, *--sift_1));

                *sift = BOOST_PDQSORT_PREFER_MOVE(tmp);
            }
        }
    }

    // Attempts to use insertion sort on [begin, end). Will return false if more than
    // partial_insertion_sort_limit elements were moved, and abort sorting. Otherwise it will
    // successfully sort and return true.
    template<class Iter, class Compare>
    inline bool partial_insertion_sort(Iter begin, Iter end, Compare comp) {
        typedef typename std::iterator_traits<Iter>::value_type T;
        if (begin == end) return true;

        int limit = 0;
        for (Iter cur = begin + 1; cur != end; ++cur) {
            if (limit > partial_insertion_sort_limit) return false;

            Iter sift = cur;
            Iter sift_1 = cur - 1;

            // Compare first so we can avoid 2 moves for an element already positioned correctly.
            if (comp(*sift, *sift_1)) {
                T tmp = BOOST_PDQSORT_PREFER_MOVE(*sift);

                do { *sift-- = BOOST_PDQSORT_PREFER_MOVE(*sift_1); }
                while (sift != begin && comp(tmp, *--sift_1));

                *sift = BOOST_PDQSORT_PREFER_MOVE(tmp);
                limit += cur - sift;
            }
        }

        return true;
    }

    template<class Iter, class Compare>
    inline void sort2(Iter a, Iter b, Compare comp) {
        if (comp(*b, *a)) std::iter_swap(a, b);
    }

    // Sorts the elements *a, *b and *c using comparison function comp.
    template<class Iter, class Compare>
    inline void sort3(Iter a, Iter b, Iter c, Compare comp) {
        sort2(a, b, comp);
        sort2(b, c, comp);
        sort2(a, b, comp);
    }

    template<class T>
    inline T* align_cacheline(T* p) {
#if defined(UINTPTR_MAX) && __cplusplus >= 201103L
        std::uintptr_t ip = reinterpret_cast<std::uintptr_t>(p);
#else
        std::size_t ip = reinterpret_cast<std::size_t>(p);
#endif
        ip = (ip + cacheline_size - 1) & -cacheline_size;
        return reinterpret_cast<T*>(ip);
    }

    template<class Iter>
    inline void swap_offsets(Iter first, Iter last,
                             unsigned char* offsets_l, unsigned char* offsets_r,
                             int num, bool use_swaps) {
        typedef typename std::iterator_traits<Iter>::value_type T;
        if (use_swaps) {
            // This case is needed for the descending distribution, where we need
            // to have proper swapping for pdqsort to remain O(n).
            for (int i = 0; i < num; ++i) {
                std::iter_swap(first + offsets_l[i], last - offsets_r[i]);
            }
        } else if (num > 0) {
            Iter l = first + offsets_l[0]; Iter r = last - offsets_r[0];
            T tmp(BOOST_PDQSORT_PREFER_MOVE(*l)); *l = BOOST_PDQSORT_PREFER_MOVE(*r);
            for (int i = 1; i < num; ++i) {
                l = first + offsets_l[i]; *r = BOOST_PDQSORT_PREFER_MOVE(*l);
                r = last - offsets_r[i]; *l = BOOST_PDQSORT_PREFER_MOVE(*r);
            }
            *r = BOOST_PDQSORT_PREFER_MOVE(tmp);
        }
    }

    // Partitions [begin, end) around pivot *begin using comparison function comp. Elements equal
    // to the pivot are put in the right-hand partition. Returns the position of the pivot after
    // partitioning and whether the passed sequence already was correctly partitioned. Assumes the
    // pivot is a median of at least 3 elements and that [begin, end) is at least
    // insertion_sort_threshold long. Uses branchless partitioning.
    template<class Iter, class Compare>
    inline std::pair<Iter, bool> partition_right_branchless(Iter begin, Iter end, Compare comp) {
        typedef typename std::iterator_traits<Iter>::value_type T;

        // Move pivot into local for speed.
        T pivot(BOOST_PDQSORT_PREFER_MOVE(*begin));
        Iter first = begin;
        Iter last = end;

        // Find the first element greater than or equal than the pivot (the median of 3 guarantees
        // this exists).
        while (comp(*++first, pivot));

        // Find the first element strictly smaller than the pivot. We have to guard this search if
        // there was no element before *first.
        if (first - 1 == begin) while (first < last && !comp(*--last, pivot));
        else                    while (                !comp(*--last, pivot));

        // If the first pair of elements that should be swapped to partition are the same element,
        // the passed in sequence already was correctly partitioned.
        bool already_partitioned = first >= last;
        if (!already_partitioned) {
            std::iter_swap(first, last);
            ++first;
        }

        // The following branchless partitioning is derived from "BlockQuicksort: How Branch
        // Mispredictions don't affect Quicksort" by Stefan Edelkamp and Armin Weiss.
        unsigned char offsets_l_storage[block_size + cacheline_size];
        unsigned char offsets_r_storage[block_size + cacheline_size];
        unsigned char* offsets_l = align_cacheline(offsets_l_storage);
        unsigned char* offsets_r = align_cacheline(offsets_r_storage);
        int num_l, num_r, start_l, start_r;
        num_l = num_r = start_l = start_r = 0;

        while (last - first > 2 * block_size) {
            // Fill up offset blocks with elements that are on the wrong side.
            if (num_l == 0) {
                start_l = 0;
                Iter it = first;
                for (unsigned char i = 0; i < block_size;) {
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                    offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
                }
            }
            if (num_r == 0) {
                start_r = 0;
                Iter it = last;
                for (unsigned char i = 0; i < block_size;) {
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                    offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
                }
            }

            // Swap elements and update block sizes and first/last boundaries.
            int num = (std::min)(num_l, num_r);
            swap_offsets(first, last, offsets_l + start_l, offsets_r + start_r,
                         num, num_l == num_r);
            num_l -= num; num_r -= num;
            start_l += num; start_r += num;
            if (num_l == 0) first += block_size;
            if (num_r == 0) last -= block_size;
        }

        int l_size = 0, r_size = 0;
        int unknown_left = (last - first) - ((num_r || num_l) ? block_size : 0);
        if (num_r) {
            // Handle leftover block by assigning the unknown elements to the other block.
            l_size = unknown_left;
            r_size = block_size;
        } else if (num_l) {
            l_size = block_size;
            r_size = unknown_left;
        } else {
            // No leftover block, split the unknown elements in two blocks.
            l_size = unknown_left/2;
            r_size = unknown_left - l_size;
        }

        // Fill offset buffers if needed.
        if (unknown_left && !num_l) {
            start_l = 0;
            Iter it = first;
            for (unsigned char i = 0; i < l_size;) {
                offsets_l[num_l] = i++; num_l += !comp(*it, pivot); ++it;
            }
        }
        if (unknown_left && !num_r) {
            start_r = 0;
            Iter it = last;
            for (unsigned char i = 0; i < r_size;) {
                offsets_r[num_r] = ++i; num_r += comp(*--it, pivot);
            }
        }

        int num = (std::min)(num_l, num_r);
        swap_offsets(first, last, offsets_l + start_l, offsets_r + start_r, num, num_l == num_r);
        num_l -= num; num_r -= num;
        start_l += num; start_r += num;
        if (num_l == 0) first += l_size;
        if (num_r == 0) last -= r_size;

        // We have now fully identified [first, last)'s proper position. Swap the last elements.
        if (num_l) {
            offsets_l += start_l;
            while (num_l--) std::iter_swap(first + offsets_l[num_l], --last);
            first = last;
        }
        if (num_r) {
            offsets_r += start_r;
            while (num_r--) std::iter_swap(last - offsets_r[num_r], first), ++first;
            last = first;
        }

        // Put the pivot in the right place.
        Iter pivot_pos = first - 1;
        *begin = BOOST_PDQSORT_PREFER_MOVE(*pivot_pos);
        *pivot_pos = BOOST_PDQSORT_PREFER_MOVE(pivot);

        return std::make_pair(pivot_pos, already_partitioned);
    }

    // Partitions [begin, end) around pivot *begin using comparison function comp. Elements equal
    // to the pivot are put in the right-hand partition. Returns the position of the pivot after
    // partitioning and whether the passed sequence already was correctly partitioned. Assumes the
    // pivot is a median of at least 3 elements and that [begin, end) is at least
    // insertion_sort_threshold long.
    template<class Iter, class Compare>
    inline std::pair<Iter, bool> partition_right(Iter begin, Iter end, Compare comp) {
        typedef typename std::iterator_traits<Iter>::value_type T;

        // Move pivot into local for speed.
        T pivot(BOOST_PDQSORT_PREFER_MOVE(*begin));

        Iter first = begin;
        Iter last = end;

        // Find the first element greater than or equal than the pivot (the median of 3 guarantees
        // this exists).
        while (comp(*++first, pivot));

        // Find the first element strictly smaller than the pivot. We have to guard this search if
        // there was no element before *first.
        if (first - 1 == begin) while (first < last && !comp(*--last, pivot));
        else                    while (                !comp(*--last, pivot));

        // If the first pair of elements that should be swapped to partition are the same element,
        // the passed in sequence already was correctly partitioned.
        bool already_partitioned = first >= last;

        // Keep swapping pairs of elements that are on the wrong side of the pivot. Previously
        // swapped pairs guard the searches, which is why the first iteration is special-cased
        // above.
        while (first < last) {
            std::iter_swap(first, last);
            while (comp(*++first, pivot));
            while (!comp(*--last, pivot));
        }

        // Put the pivot in the right place.
        Iter pivot_pos = first - 1;
        *begin = BOOST_PDQSORT_PREFER_MOVE(*pivot_pos);
        *pivot_pos = BOOST_PDQSORT_PREFER_MOVE(pivot);

        return std::make_pair(pivot_pos, already_partitioned);
    }

    // Similar function to the one above, except elements equal to the pivot are put to the left of
    // the pivot and it doesn't check or return if the passed sequence already was partitioned.
    // Since this is rarely used (the many equal case), and in that case pdqsort already has O(n)
    // performance, no block quicksort is applied here for simplicity.
    template<class Iter, class Compare>
    inline Iter partition_left(Iter begin, Iter end, Compare comp) {
        typedef typename std::iterator_traits<Iter>::value_type T;

        T pivot(BOOST_PDQSORT_PREFER_MOVE(*begin));
        Iter first = begin;
        Iter last = end;

        while (comp(pivot, *--last));

        if (last + 1 == end) while (first < last && !comp(pivot, *++first));
        else                 while (                !comp(pivot, *++first));

        while (first < last) {
            std::iter_swap(first, last);
            while (comp(pivot, *--last));
            while (!comp(pivot, *++first));
        }

        Iter pivot_pos = last;
        *begin = BOOST_PDQSORT_PREFER_MOVE(*pivot_pos);
        *pivot_pos = BOOST_PDQSORT_PREFER_MOVE(pivot);

        return pivot_pos;
    }


    template<class Iter, class Compare, bool Branchless>
    inline void pdqsort_loop(Iter begin, Iter end, Compare comp, int bad_allowed, bool leftmost = true) {
        typedef typename std::iterator_traits<Iter>::difference_type diff_t;

        // Use a while loop for tail recursion elimination.
        while (true) {
            diff_t size = end - begin;

            // Insertion sort is faster for small arrays.
            if (size < insertion_sort_threshold) {
                STAT_INCR(pdqstat.small);
                if (leftmost) insertion_sort(begin, end, comp);
                else unguarded_insertion_sort(begin, end, comp);
                return;
            }

            // Choose pivot as median of 3 or pseudomedian of 9.
            diff_t s2 = size / 2;
            if (size > ninther_threshold) {
                sort3(begin, begin + s2, end - 1, comp);
                sort3(begin + 1, begin + (s2 - 1), end - 2, comp);
                sort3(begin + 2, begin + (s2 + 1), end - 3, comp);
                sort3(begin + (s2 - 1), begin + s2, begin + (s2 + 1), comp);
                std::iter_swap(begin, begin + s2);
            } else sort3(begin + s2, begin, end - 1, comp);

            // If *(begin - 1) is the end of the right partition of a previous partition operation
            // there is no element in [begin, end) that is smaller than *(begin - 1). Then if our
            // pivot compares equal to *(begin - 1) we change strategy, putting equal elements in
            // the left partition, greater elements in the right partition. We do not have to
            // recurse on the left partition, since it's sorted (all equal).
            if (!leftmost && !comp(*(begin - 1), *begin)) {
                STAT_INCR(pdqstat.leftp);
                begin = partition_left(begin, end, comp) + 1;
                continue;
            }

            // Partition and get results.
            std::pair<Iter, bool> part_result =
                Branchless ? partition_right_branchless(begin, end, comp)
                           : partition_right(begin, end, comp);
            Iter pivot_pos = part_result.first;
            bool already_partitioned = part_result.second;

            // Check for a highly unbalanced partition.
            diff_t l_size = pivot_pos - begin;
            diff_t r_size = end - (pivot_pos + 1);
            bool highly_unbalanced = l_size < size / 8 || r_size < size / 8;

            if (already_partitioned) STAT_INCR(pdqstat.ap);

            // If we got a highly unbalanced partition we shuffle elements to break many patterns.
            if (highly_unbalanced) {
                STAT_INCR(pdqstat.bad);

                // If we had too many bad partitions, switch to heapsort to guarantee O(n log n).
                if (--bad_allowed == 0) {
                    STAT_INCR(pdqstat.heapsort);
                    std::make_heap(begin, end, comp);
                    std::sort_heap(begin, end, comp);
                    return;
                }

                if (l_size >= insertion_sort_threshold) {
                    std::iter_swap(begin,             begin + l_size / 4);
                    std::iter_swap(pivot_pos - 1, pivot_pos - l_size / 4);

                    if (l_size > ninther_threshold) {
                        std::iter_swap(begin + 1,         begin + (l_size / 4 + 1));
                        std::iter_swap(begin + 2,         begin + (l_size / 4 + 2));
                        std::iter_swap(pivot_pos - 2, pivot_pos - (l_size / 4 + 1));
                        std::iter_swap(pivot_pos - 3, pivot_pos - (l_size / 4 + 2));
                    }
                }

                if (r_size >= insertion_sort_threshold) {
                    std::iter_swap(pivot_pos + 1, pivot_pos + (1 + r_size / 4));
                    std::iter_swap(end - 1,                   end - r_size / 4);

                    if (r_size > ninther_threshold) {
                        std::iter_swap(pivot_pos + 2, pivot_pos + (2 + r_size / 4));
                        std::iter_swap(pivot_pos + 3, pivot_pos + (3 + r_size / 4));
                        std::iter_swap(end - 2,             end - (1 + r_size / 4));
                        std::iter_swap(end - 3,             end - (2 + r_size / 4));
                    }
                }
            } else {
                // If we were decently balanced and we tried to sort an already partitioned
                // sequence try to use insertion sort.
                if (already_partitioned && partial_insertion_sort(begin, pivot_pos, comp)
                                        && partial_insertion_sort(pivot_pos + 1, end, comp))
                {
                  STAT_INCR(pdqstat.ap_sorted);
                  return;
                }
            }

            // Sort the left partition first using recursion and do tail recursion elimination for
            // the right-hand partition.
            pdqsort_loop<Iter, Compare, Branchless>(begin, pivot_pos, comp, bad_allowed, leftmost);
            begin = pivot_pos + 1;
            leftmost = false;
        }
    }




};



























template<class IA>
void test_sorted(std::vector<IA> &A)
{
  if (!std::is_sorted(A.begin (), A.end ())) {
    std::cout<<"*** NOT SORTED *** "<<std::endl;
  }
}

template<typename A> void time_op(std::string name, A op) {
  using bsc::now;
  using bsc::subtract_time;

  auto start = now ();
  op();
  auto finish = now ();
  auto duration = subtract_time (finish, start);

  std::cout<<"  "<<name<<"."<<"time: "<<duration<<std::endl;
}

template<typename A> double time_op(A op) {
  auto start = now ();
  op();
  auto finish = now ();
  return subtract_time (finish, start);
}


template<typename SORT> void test_sort(std::string name, SORT op)
{
  cout<<name<<":"; cout.flush();


  {
    auto A = Int_Generator::random(N);
    cout<<" "<<time_op([&]{op(A);}); cout.flush();
    test_sorted(A);
  }

//
//   {
//     auto A = Int_Generator::random_dup(N,N/1000);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }

//   {
//     auto A = Int_Generator::sorted(N*10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }

//   {
//     auto A = Int_Generator::alleq(N*10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }


//   {
//     auto A = Int_Generator::sorted_end(N,N/100);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }
//
//
//   {
//     auto A = Int_Generator::sorted_end(N,N/10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }
//
//
//   {
//     auto A = Int_Generator::sorted_middle(N,N/10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }
//

//   {
//     auto A = Int_Generator::reverse_sorted(N*10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }


//   {
//     auto A = Int_Generator::reverse_sorted_end(N,N/10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }
//
//
//   {
//     auto A = Int_Generator::reverse_sorted_middle(N,N/10);
//     cout<<" "<<time_op([&]{op(A);}); cout.flush();
//     test_sorted(A);
//   }


  cout<<endl;
}


/// This is a helper function...
uint64_t *xunguarded_partition(uint64_t *a, size_t size, uint64_t pivot)
{

  size_t i=0;
  size_t j=size;

  while (true) {
    while (a[i]<pivot)
      ++i;
    --j;
    while (pivot<a[j])
      --j;
    if (!(i < j))
      return a+i;

    std::swap(a[i],a[j]);
    ++i;
  }
}

/// This is a helper function...
inline uint64_t *xpartition_pivot(uint64_t *a, size_t size)
{
  auto __comp = __gnu_cxx::__ops::__iter_less_iter();

  uint64_t *__mid = a + size / 2;
  std::__move_median_to_first(a, a + 1, __mid, a+size - 1, __comp);

  return xunguarded_partition(a+1,size-1,a[0]);

  //return std::__unguarded_partition(a + 1, a+size, a, __comp);
}




void xintrosort(uint64_t *a, size_t size) {
  if (size>int(_S_threshold)) {

    uint64_t *cut = xpartition_pivot(a, size);

    xintrosort(a, cut-a);

    xintrosort(cut,a+size-cut);
  } else {
    auto __comp = __gnu_cxx::__ops::__iter_less_iter();
    std::__insertion_sort(a, a+size, __comp);
  }
}


inline void xsort(uint64_t *a, size_t size)
{
  if (size) {
    xintrosort(a,size);
  }
}


const size_t insertion_sort_threshold = 24;
const size_t ninther_threshold = 128;
const size_t partial_insertion_sort_limit = 8;

inline bool partial_insertion_sort(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return true;

    int limit = 0;
    for (size_t cur = begin + 1; cur != end; ++cur) {
        if (limit > partial_insertion_sort_limit) return false;

        size_t sift = cur;
        size_t sift_1 = cur - 1;

        // Compare first so we can avoid 2 moves for an element already positioned correctly.
        if (a[sift] < a[sift_1]) {
            uint64_t tmp = a[sift];

            do {
              a[sift--] = a[sift_1];
            } while (sift != begin && tmp < a[--sift_1]);

            a[sift] = tmp;
            limit += cur - sift;
        }
    }

    return true;
}


// Dropping compare-first optimization
inline bool partial_insertion_sort2(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return true;

    size_t limit = 0;
    for (size_t cur = begin + 1; cur != end; ++cur) {
        if (limit > partial_insertion_sort_limit) return false;

        uint64_t tmp = a[cur];

        uint64_t i = cur;


        while (i!=begin && tmp < a[i-1]) {
          a[i] = a[i-1];
          --i;
          ++limit;
        }

        a[i] = tmp;
    }

    return true;
}


// Dropping compare-first optimization

inline bool partial_insertion_sort3(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return true;

    size_t limit = 0;
    for (size_t cur = begin + 1; cur != end; ++cur) {
        if (limit > partial_insertion_sort_limit) return false;


        if (a[cur] < a[cur-1]) {
          uint64_t tmp = a[cur];
          a[cur] = a[cur-1];
          uint64_t i = cur - 1;
          ++limit;

          while (i!=begin && tmp < a[i-1]) {
            a[i] = a[i-1];
            --i;
            ++limit;
          }

          a[i] = tmp;
        }
    }

    return true;
}




inline void unguarded_insertion_sort(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return;

    for (size_t cur = begin + 1; cur != end; ++cur) {
        size_t sift = cur;
        size_t sift_1 = cur - 1;

        // Compare first so we can avoid 2 moves for an element already positioned correctly.
        if (a[sift] < a[sift_1]) {
            uint64_t tmp = a[sift];

            do { a[sift--] = a[sift_1]; }
            while (tmp < a[--sift_1]);

            a[sift] = tmp;
        }
    }
}


inline void unguarded_insertion_sort2(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return;

    for (size_t cur = begin + 1; cur != end; ++cur) {
        uint64_t tmp = a[cur];
        uint64_t i = cur;

        while (tmp < a[i-1]) {
          a[i] = a[i-1];
          --i;
        }

        a[i] = tmp;
    }
}

inline void unguarded_insertion_sort3(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return;

    for (size_t cur = begin + 1; cur != end; ++cur) {

        if (a[cur] < a[cur - 1]) {
          uint64_t tmp = a[cur];
          uint64_t i = cur;
          a[i] = a[i-1];
          --i;

          while (tmp < a[i-1]) {
            a[i] = a[i-1];
            --i;
          }

          a[i] = tmp;
        }
    }
}


// Dropping compare-first optimization
inline void guarded_insertion_sort(uint64_t *a, size_t begin, size_t end) {
    if (begin == end) return;

    for (size_t cur = begin + 1; cur != end; ++cur) {
        uint64_t tmp = a[cur];
        uint64_t i = cur;

        while (i>begin && tmp < a[i-1]) {
          a[i] = a[i-1];
          --i;
        }

        a[i] = tmp;
    }
}



inline void sort2(uint64_t *a, size_t i, size_t j) {
    if (a[j]<a[i]) std::swap(a[i],a[j]);
}

// Sorts the elements *a, *b and *c using comparison function comp.
inline void sort3(uint64_t *a, size_t i, size_t j, size_t k) {
    sort2(a, i, j);
    sort2(a, j, k);
    sort2(a,i,j);
}


inline void move_pivot_to_front(uint64_t *a, size_t begin, size_t end) {
  size_t size = end - begin;
  size_t s2 = size / 2;
  if (size > ninther_threshold) {
      sort3(a,begin, begin + s2, end - 1);
      sort3(a,begin + 1, begin + (s2 - 1), end - 2);
      sort3(a,begin + 2, begin + (s2 + 1), end - 3);
      sort3(a,begin + (s2 - 1), begin + s2, begin + (s2 + 1));
      std::swap(a[begin], a[begin + s2]);
  } else sort3(a,begin + s2, begin, end - 1);
}

inline bool shuffle(uint64_t *a, size_t begin, size_t end, size_t pivot_pos) {
  size_t size = end - begin;
  size_t l_size = pivot_pos - begin;
  size_t r_size = end - (pivot_pos + 1);
  bool highly_unbalanced = l_size < size / 8 || r_size < size / 8;

  if (highly_unbalanced) {
      if (l_size >= insertion_sort_threshold) {
          std::swap(a[begin],             a[begin + l_size / 4]);
          std::swap(a[pivot_pos - 1], a[pivot_pos - l_size / 4]);

          if (l_size > ninther_threshold) {
              std::swap(a[begin + 1],     a[begin + (l_size / 4 + 1)]);
              std::swap(a[begin + 2],     a[begin + (l_size / 4 + 2)]);
              std::swap(a[pivot_pos - 2], a[pivot_pos - (l_size / 4 + 1)]);
              std::swap(a[pivot_pos - 3], a[pivot_pos - (l_size / 4 + 2)]);
          }
      }

      if (r_size >= insertion_sort_threshold) {
          std::swap(a[pivot_pos + 1], a[pivot_pos + (1 + r_size / 4)]);
          std::swap(a[end - 1],                   a[end - r_size / 4]);

          if (r_size > ninther_threshold) {
              std::swap(a[pivot_pos + 2], a[pivot_pos + (2 + r_size / 4)]);
              std::swap(a[pivot_pos + 3], a[pivot_pos + (3 + r_size / 4)]);
              std::swap(a[end - 2],             a[end - (1 + r_size / 4)]);
              std::swap(a[end - 3],             a[end - (2 + r_size / 4)]);
          }
      }
  }

  return highly_unbalanced;
}





// Partitions [begin, end) around pivot *begin using comparison function comp. Elements equal
// to the pivot are put in the right-hand partition. Returns the position of the pivot after
// partitioning and whether the passed sequence already was correctly partitioned. Assumes the
// pivot is a median of at least 3 elements and that [begin, end) is at least
// insertion_sort_threshold long.
inline std::pair<size_t, bool> partition_right(uint64_t *a, size_t begin, size_t end) {

    uint64_t pivot = a[begin];

    size_t first = begin;
    size_t last = end;

    // Find the first element greater than or equal than the pivot (the median of 3 guarantees
    // this exists).

    ++first;
    while (a[first] < pivot) ++first;

//    while (a[++first] < pivot);

    // Find the first element strictly smaller than the pivot. We have to guard this search if
    // there was no element before *first.
    if (first - 1 == begin) while (first < last && !(a[--last] < pivot));
    else                    while (                !(a[--last] < pivot));

    // If the first pair of elements that should be swapped to partition are the same element,
    // the passed in sequence already was correctly partitioned.
    bool already_partitioned = first >= last;

    // Keep swapping pairs of elements that are on the wrong side of the pivot. Previously
    // swapped pairs guard the searches, which is why the first iteration is special-cased
    // above.
    while (first < last) {
        std::swap(a[first], a[last]);
        while (a[++first] < pivot);
        while (!(a[--last] < pivot));
    }

    // Put the pivot in the right place.
    size_t pivot_pos = first - 1;

    a[begin] = a[pivot_pos];
    a[pivot_pos] = pivot;

    return std::make_pair(pivot_pos, already_partitioned);
}

// Similar function to the one above, except elements equal to the pivot are put to the left of
// the pivot and it doesn't check or return if the passed sequence already was partitioned.
// Since this is rarely used (the many equal case), and in that case pdqsort already has O(n)
// performance, no block quicksort is applied here for simplicity.

inline size_t partition_left(uint64_t *a, size_t begin, size_t end) {

    uint64_t pivot = a[begin];
    size_t first = begin;
    size_t last = end;

    while (pivot < a[--last]);

    if (last + 1 == end) while (first < last && !(pivot < a[++first]));
    else                 while (                !(pivot < a[++first]));

    while (first < last) {
        std::swap(a[first], a[last]);
        while ((pivot < a[--last]));
        while (!(pivot < a[++first]));
    }

    size_t pivot_pos = last;
    a[begin] = a[pivot_pos];
    a[pivot_pos] = pivot;

    return pivot_pos;
}





void pdqsort_rec(uint64_t *a, size_t begin, size_t end, int bad_allowed, bool leftmost) {
  //typedef typename std::iterator_traits<Iter>::difference_type diff_t;

//   cerr<<"pdqsort_rec "<<begin<<" "<<end<<endl;

  auto comp = std::less<uint64_t>();

  if (end - begin < insertion_sort_threshold) {
     STAT_INCR(mystat.small);
     if (leftmost) guarded_insertion_sort(a,begin, end);
     else unguarded_insertion_sort3(a,begin, end);
  } else {
    move_pivot_to_front(a,begin,end);

    // If *(begin - 1) is the end of the right partition of a previous partition operation
    // there is no element in [begin, end) that is smaller than *(begin - 1). Then if our
    // pivot compares equal to *(begin - 1) we change strategy, putting equal elements in
    // the left partition, greater elements in the right partition. We do not have to
    // recurse on the left partition, since it's sorted (all equal).
    if (!leftmost && !(a[begin - 1] < a[begin])) {
        STAT_INCR(mystat.leftp);
        size_t mid = partition_left(a,begin,end) + 1;
        pdqsort_rec(a,mid,end,bad_allowed,false); // NOTE: Original pdqsort might preserve leftmost=true here, even if no longer in leftmost part!
    } else {
        // Partition and get results.
        auto part_result = partition_right(a,begin, end);
        size_t pivot_pos = part_result.first;
        bool already_partitioned = part_result.second;

        bool highly_unbalanced = shuffle(a,begin,end,pivot_pos);
        if (highly_unbalanced) STAT_INCR(mystat.bad);

        if (already_partitioned) STAT_INCR(mystat.ap);

        if (highly_unbalanced && --bad_allowed == 0) {
            STAT_INCR(mystat.heapsort);
            std::make_heap(a+begin, a+end, comp);
            std::sort_heap(a+begin, a+end, comp);
        } else if (!highly_unbalanced && already_partitioned
              && partial_insertion_sort3(a,begin, pivot_pos)
              && partial_insertion_sort3(a,pivot_pos + 1,end)) {
          STAT_INCR(mystat.ap_sorted);
          //SKIP
        } else {
          pdqsort_rec(a,begin, pivot_pos, bad_allowed, leftmost);
          pdqsort_rec(a,pivot_pos+1,end, bad_allowed,false);
        }
    }
  }
}


inline void psort(uint64_t *a, size_t size) {

    if (size)
      pdqsort_rec( a, 0, size, boost::sort::pdqsort_detail::log2(size), true);
}


template<class Iter, class Compare>
inline void pdqsort(Iter first, Iter last, Compare comp) {
    if (first == last) return;
    pdqcopy::pdqsort_loop<Iter, Compare, false >( first, last, comp, boost::sort::pdqsort_detail::log2(last - first));
}


template<class Iter>
inline void pdqsort(Iter first, Iter last) {
    typedef typename std::iterator_traits<Iter>::value_type T;
    pdqsort(first, last, std::less<T>());
}




int main(int argc, char** argv) {

  bool self_test=true;
  bool pdq=true;
  bool mypdq=true;

  if (argc > 1) {
    self_test=false;
    pdq=false;
    mypdq=false;

    for (size_t i=1; i<argc;++i) {
      string a = argv[i];

      if (a == "pdq") pdq=true;
      else if (a == "mypdq") mypdq=true;
      else if (a == "selftest") self_test=true;
      else {
        cout<<"Invalid arg "<<a<<endl;
        exit(1);
      }
    }
  }


  if (self_test) {
    cout<<"selftest ..."; cout.flush();
    for (size_t i=0;i<100;++i) {
      auto A = Int_Generator::random(1000);
      psort(A.data(),A.size());
      test_sorted(A);
    }
    cout<<"done"<<endl;
  }

//   test_sort("xsort", [](vector<uint64_t> &A){xsort(A.data(),A.size());});
//
//   test_sort("ssort", [](vector<uint64_t> &A){std::sort(A.begin(),A.end());});



  if (mypdq) {
    mystat.reset();
    test_sort("mypsort  ", [](vector<uint64_t> &A){psort(A.data(),A.size());});
    mystat.print();
  }

  if (pdq) {
    pdqstat.reset();
    test_sort("pdqsort", [](vector<uint64_t> &A){pdqsort(A.begin(),A.end());});
    pdqstat.print();
  }

//   test_sort("pdqsort", [](vector<uint64_t> &A){pdqsort(A.begin(),A.end());});



//   {
//     auto A = Int_Generator::random(N);
//     time_op("xsort",[&]{xsort(A.data(),A.size());});
//     test_sorted(A);
//   }
//
//
//   {
//     auto A = Int_Generator::random(N);
//     time_op("std:sort",[&]{sort(A.begin(),A.end());});
//     test_sorted(A);
//   }

}











