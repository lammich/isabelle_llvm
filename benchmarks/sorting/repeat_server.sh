#!/bin/bash 
echo -n '# '; date 
echo -n '# '; uname -a 
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::pdqsort sorted-end-.1 100000000 10

echo '# Repeated b/c difference > 15\% (8142,6584)'
./do_benchmark llstring boost::pdqsort rev-sorted-middle-10 10000000 10
./do_benchmark llstring isabelle::pdqsort rev-sorted-middle-10 10000000 10

echo '# Repeated b/c difference > 15\% (3899,3371)'
./do_benchmark uint64 boost::pdqsort almost-sorted-1 100000000 10
./do_benchmark uint64 isabelle::pdqsort almost-sorted-1 100000000 10

