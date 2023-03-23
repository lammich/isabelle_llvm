#!/bin/bash

# make do_benchmark

########################## BEGIN CONFIG SECTION ##################

mtype=$1
if [[ $mtype == "server" ]]; then
  function tmask() {
    printf "0x%x" $((2**($1 * 2) - 1 ))
  }

  TNUM=22

elif [[ $mtype == "laptop" ]]; then
  function tmask() {
    printf "0x%x" $((2**$1 - 1 ))
  }

  TNUM=12
else
  echo "Unknown machine config: $mtype"
  exit 1
fi

# Defaults

export NITER=10   # Number of iterations
export NIELEM=100000000 # Number of integer elements
export NSELEM=10000000 # Number of string elements

# Quick benchmark run
# export NITER=3   # Number of iterations
# export NIELEM=100000 # Number of integer elements
# export NSELEM=100000 # Number of string elements

export INT_DATA="random"

export STR_DATA="random"

# export INT_ALGOS="isabelle::parqsort isabelle::pparqsort std::parsort boost::sample_sort"
# export STR_ALGOS="isabelle::parqsort isabelle::pparqsort std::parsort boost::sample_sort"

export INT_ALGOS="isabelle::pparqsort naive::parqsort_vs_pp"
export STR_ALGOS="isabelle::pparqsort naive::parqsort_vs_pp"


# CUSTOM Ad-HOC Overrides

# export INT_DATA="random organ-pipe"
# export STR_DATA=""
# export NIELEM=1000 # Number of integer elements
# export NSELEM=1000 # Number of string elements


########################## END CONFIG SECTION ##################


export LOGFILE="log/sortbench-speedup-$(date -Iseconds).log"

echo "Writing log to $LOGFILE"

echo "# Sorting benchmark" | tee "$LOGFILE"

( echo -n "# "; date ) | tee -a "$LOGFILE"

( echo -n "# "; uname -a ) | tee -a "$LOGFILE"

echo "@ $mtype" | tee -a "$LOGFILE"

function run() {
  TM=$(tmask $1)
  echo "$1 cores (mask: $TM)" | tee -a "$LOGFILE"
  ( taskset $TM ./do_benchmark $2 $3 $4 $5 $6 || echo "\n***ERROR $?" ) 2>&1 | tee -a "$LOGFILE"
  echo | tee -a "$LOGFILE"
}

for distr in $INT_DATA; do
  for algo in $INT_ALGOS; do
    for ((j=1;j<=$TNUM;++j)); do
      run $j uint64 $algo $distr $NIELEM $NITER
    done
  done
done

for distr in $STR_DATA; do
  for algo in $STR_ALGOS; do
    for ((j=1;j<=$TNUM;++j)); do
      run $j llstring $algo $distr $NSELEM $NITER
    done
  done
done



# for i in $STR_DATA; do
#   run_str_std $i
#   run_str_isa_par $i
#   run_str_naive_par $i
#   run_str_sample $i
#
# #   run_str_isa $i
# #   run_str_std $i
# #   run_pdq_str_isa $i
# #   run_pdq_str_std $i
# done


