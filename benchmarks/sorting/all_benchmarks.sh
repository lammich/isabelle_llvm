#!/bin/bash

# make do_benchmark

########################## BEGIN CONFIG SECTION ##################

# Defaults

export NITER=10   # Number of iterations
export NIELEM=100000000 # Number of integer elements
export NSELEM=10000000 # Number of string elements

# Quick benchmark run
# export NITER=3   # Number of iterations
# export NIELEM=1000 # Number of integer elements
# export NSELEM=1000 # Number of string elements

export INT_DATA="random random-dup-10 random-boolean organ-pipe sorted equal almost-sorted-.1 almost-sorted-1 almost-sorted-10 almost-sorted-50 sorted-end-.1 sorted-end-1 sorted-end-10 sorted-middle-.1 sorted-middle-1 sorted-middle-10 rev-sorted rev-sorted-end-.1 rev-sorted-end-1 rev-sorted-end-10 rev-sorted-middle-.1 rev-sorted-middle-1 rev-sorted-middle-10"

export STR_DATA="random random-dup-10 random-boolean organ-pipe sorted equal   almost-sorted-.1 almost-sorted-1 almost-sorted-10 almost-sorted-50 sorted-end-.1 sorted-end-1 sorted-end-10 sorted-middle-.1 sorted-middle-1 sorted-middle-10 rev-sorted rev-sorted-end-.1 rev-sorted-end-1 rev-sorted-end-10 rev-sorted-middle-.1 rev-sorted-middle-1 rev-sorted-middle-10"

# CUSTOM Ad-HOC Overrides

# export INT_DATA="random organ-pipe"
# export STR_DATA=""
# export NIELEM=1000 # Number of integer elements
# export NSELEM=1000 # Number of string elements


########################## END CONFIG SECTION ##################


export LOGFILE="log/sortbench-$(date -Iseconds).log"

echo "Writing log to $LOGFILE"

echo "# Sorting benchmark" | tee "$LOGFILE"

( echo -n "# "; date ) | tee -a "$LOGFILE"

( echo -n "# "; uname -a ) | tee -a "$LOGFILE"

function run() {
  ( ./do_benchmark $@ || echo "\n***ERROR $?" ) 2>&1 | tee -a "$LOGFILE"
  echo | tee -a "$LOGFILE"
}

function run_int_std() {
  run uint64 std::sort $1 $NIELEM $NITER
}

function run_int_std_par() {
  run uint64 std::parsort $1 $NIELEM $NITER
}


function run_int_isa() {
  run uint64 isabelle::sort $1 $NIELEM $NITER
}

function run_int_naive_par() {
  run uint64 naive::parqsort $1 $NIELEM $NITER
}

function run_int_isa_par() {
  run uint64 isabelle::parqsort $1 $NIELEM $NITER
}

function run_int_sample() {
  run uint64 boost::sample_sort $1 $NIELEM $NITER
}



function run_str_std() {
  run llstring std::sort $1 $NSELEM $NITER
}

function run_str_std_par() {
  run llstring std::parsort $1 $NSELEM $NITER
}

function run_str_isa() {
  run llstring isabelle::sort $1 $NSELEM $NITER
}

function run_str_naive_par() {
  run llstring naive::parqsort $1 $NSELEM $NITER
}

function run_str_isa_par() {
  run llstring isabelle::parqsort $1 $NSELEM $NITER
}

function run_str_sample() {
  run llstring boost::sample_sort $1 $NSELEM $NITER
}


function run_pdq_int_std() {
  run uint64 boost::pdqsort $1 $NIELEM $NITER
}

function run_pdq_int_isa() {
  run uint64 isabelle::pdqsort $1 $NIELEM $NITER
}

function run_pdq_str_std() {
  run llstring boost::pdqsort $1 $NSELEM $NITER
}

function run_pdq_str_isa() {
  run llstring isabelle::pdqsort $1 $NSELEM $NITER
}



function run_int_gcc() {
  ( ./do_benchmark_gcc uint64 std::sort $1 $NIELEM $NITER || echo "\n***ERROR $?" ) 2>&1 | tee -a "$LOGFILE"
  echo | tee -a "$LOGFILE"
}

for i in $INT_DATA; do

  run_int_std $i
  run_int_std_par $i
  run_int_isa_par $i
  run_int_naive_par $i
  run_int_sample $i


#   run_int_isa $i
#   run_int_std $i
#   run_pdq_int_isa $i
#   run_pdq_int_std $i
#   run_int_gcc $i
done

for i in $STR_DATA; do
  run_str_std $i
  run_str_std_par $i
  run_str_isa_par $i
  run_str_naive_par $i
  run_str_sample $i

#   run_str_isa $i
#   run_str_std $i
#   run_pdq_str_isa $i
#   run_pdq_str_std $i
done


