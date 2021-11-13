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
# export NIELEM=1000000 # Number of integer elements
# export NSELEM=1000000 # Number of string elements

export INT_DATA="random"

export STR_DATA="random"

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

echo "@ $mtype" | tee -a "$LOGFILE"

function run() {
  TM=$(tmask $1)
  echo "$1 cores (mask: $TM)" | tee -a "$LOGFILE"
  ( taskset $TM ./do_benchmark $2 $3 $4 $5 $6 || echo "\n***ERROR $?" ) 2>&1 | tee -a "$LOGFILE"
  echo | tee -a "$LOGFILE"
}

for distr in $INT_DATA; do
  for ((j=1;j<=$TNUM;++j)); do
    run $j uint64 isabelle::parqsort $distr $NIELEM $NITER
  done
  for ((j=1;j<=$TNUM;++j)); do
    run $j uint64 std::parsort $distr $NIELEM $NITER
  done
  for ((j=1;j<=$TNUM;++j)); do
    run $j uint64 naive::parqsort $distr $NIELEM $NITER
  done
  for ((j=1;j<=$TNUM;++j)); do
    run $j uint64 boost::sample_sort $distr $NIELEM $NITER
  done
done

for distr in $STR_DATA; do
  for ((j=1;j<=$TNUM;++j)); do
    run $j llstring isabelle::parqsort $distr $NSELEM $NITER
  done
  for ((j=1;j<=$TNUM;++j)); do
    run $j llstring std::parsort $distr $NSELEM $NITER
  done
  for ((j=1;j<=$TNUM;++j)); do
    run $j llstring naive::parqsort $distr $NSELEM $NITER
  done
  for ((j=1;j<=$TNUM;++j)); do
    run $j llstring boost::sample_sort $distr $NSELEM $NITER
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


