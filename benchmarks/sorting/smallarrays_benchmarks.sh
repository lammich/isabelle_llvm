#!/bin/bash

# make do_benchmark

########################## BEGIN CONFIG SECTION ##################

# Defaults

export NITER=10   # Number of iterations

export I_SIZES="10000 27826 77426 215443 599484 1668101 4641589 12915497 35938137 100000000" # s_i+1 = 2.782559403*s_i

export S_SIZES="1000 2783 7743 21544 59948 166810 464159 1291550 3593814 10000000" # s_i+1 = 2.782559403*s_i


export INT_DATA="random"
export STR_DATA="random"

export INT_ALGOS="isabelle::pparqsort std::parsort boost::sample_sort"
export STR_ALGOS="isabelle::pparqsort std::parsort boost::sample_sort"

# export INT_ALGOS="isabelle::pparqsort naive::parqsort_vs_pp"
# export STR_ALGOS="isabelle::pparqsort naive::parqsort_vs_pp"


# CUSTOM Ad-HOC Overrides

# export INT_DATA="random organ-pipe"
# export STR_DATA=""
# export NIELEM=1000 # Number of integer elements
# export NSELEM=1000 # Number of string elements


########################## END CONFIG SECTION ##################


export LOGFILE="log/sortbench-smallarrays-$(date -Iseconds).log"

echo "Writing log to $LOGFILE"

echo "# Sorting benchmark" | tee "$LOGFILE"

( echo -n "# "; date ) | tee -a "$LOGFILE"

( echo -n "# "; uname -a ) | tee -a "$LOGFILE"

for distr in $INT_DATA; do
  for algo in $INT_ALGOS; do
    for n in $I_SIZES; do
      ./do_benchmark uint64 $algo $distr $n $NITER | tee -a "$LOGFILE"
    done
  done
done

for distr in $STR_DATA; do
  for algo in $STR_ALGOS; do
    for n in $S_SIZES; do
      ./do_benchmark llstring $algo $distr $n $NITER | tee -a "$LOGFILE"
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


