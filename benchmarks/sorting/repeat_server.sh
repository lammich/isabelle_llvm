#!/bin/bash 
echo -n '# '; date 
echo -n '# '; uname -a 
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 naive::parqsort random-boolean 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort organ-pipe 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort sorted-end-10 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort equal 10000000 10
echo '# Repeated b/c difference > 15\% (561,667)'
./do_benchmark llstring naive::parqsort equal 10000000 10
./do_benchmark llstring isabelle::parqsort equal 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 naive::parqsort equal 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort rev-sorted-middle-.1 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::parqsort rev-sorted-middle-.1 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 naive::parqsort rev-sorted 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::parqsort rev-sorted 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort random 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort almost-sorted-.1 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 naive::parqsort almost-sorted-.1 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::parqsort almost-sorted-.1 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 naive::parqsort sorted 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort sorted-middle-.1 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort almost-sorted-10 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort almost-sorted-1 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 naive::parqsort almost-sorted-1 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark uint64 isabelle::parqsort almost-sorted-1 100000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort rev-sorted-end-.1 10000000 10
echo '# Repeated b/c noise > 2\%'
./do_benchmark llstring boost::sample_sort sorted-end-1 10000000 10
