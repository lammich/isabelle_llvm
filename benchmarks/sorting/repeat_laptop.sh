#!/bin/bash 
echo -n '# '; date 
echo -n '# '; uname -a 
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring naive::parqsort rev-sorted-end-1 10000000 10
echo '# Repeated b/c difference > 15\% (1433,1751)'
./do_benchmark llstring naive::parqsort random-boolean 10000000 10
./do_benchmark llstring isabelle::parqsort random-boolean 10000000 10
echo '# Repeated b/c difference > 15\% (771,1026)'
./do_benchmark llstring naive::parqsort equal 10000000 10
./do_benchmark llstring isabelle::parqsort equal 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 std::sort random-dup-10 100000000 10
