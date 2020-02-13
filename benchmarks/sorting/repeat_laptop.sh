#!/bin/bash 
echo -n '# '; date 
echo -n '# '; uname -a 
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort rev-sorted-end-10 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring isabelle::pdqsort rev-sorted-end-10 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort sorted-end-10 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort rev-sorted-middle-.1 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort rev-sorted-middle-10 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort almost-sorted-.1 10000000 10

echo '# Repeated b/c difference > 15\% (154,201)'
./do_benchmark uint64 boost::pdqsort sorted 100000000 10
./do_benchmark uint64 isabelle::pdqsort sorted 100000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort rev-sorted-middle-1 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring isabelle::pdqsort rev-sorted-middle-1 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::pdqsort sorted-middle-10 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring isabelle::pdqsort sorted-middle-10 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring isabelle::pdqsort sorted-end-1 10000000 10

echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring isabelle::pdqsort random-dup-10 10000000 10

