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

  TNUM=$(cat /proc/cpuinfo | grep '^processor' | wc -l)

  echo "Guessing processor allocation: $TNUM cores's at Ids: 0..<$TNUM"
  echo "Guess may be wrong depending on you machine!"

  function tmask() {
    printf "0x%x" $((2**$1 - 1 ))
  }

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

export INT_ALGOS="isabelle::parqsort isabelle::pparqsort std::parsort boost::sample_sort"
export STR_ALGOS="isabelle::parqsort isabelle::pparqsort std::parsort boost::sample_sort"


# CUSTOM Ad-HOC Overrides

# export INT_ALGOS="isabelle::pparqsort naive::parqsort_vs_pp"
# export STR_ALGOS="isabelle::pparqsort naive::parqsort_vs_pp"


# export INT_DATA="random organ-pipe"
# export STR_DATA=""
# export NIELEM=1000 # Number of integer elements
# export NSELEM=1000 # Number of string elements


########################## END CONFIG SECTION ##################


export LOGDATE="$(date -Iseconds)"

export LOGFILE="log/sortbench-speedup-$LOGDATE.log"
rm -f "log/sortbench-speedup-latest.log"
ln -s "sortbench-speedup-$LOGDATE.log" "log/sortbench-speedup-latest.log"

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


# if $CR_REPORT; then
#   rm -rf generate
#   mkdir -p generate
#
#   ./__eval_speedup.awk uint64 < "$LOGFILE" > generate/d_uint64.tex
#   ./__eval_speedup.awk llstring < "$LOGFILE" > generate/d_llstring.tex
#
#   cp speedup_report.tex generate/
#
#   cd generate
#   pdflatex speedup_report
#   cp speedup_report.pdf "../log/speedup_report-$LOGDATE.pdf"
#   cd ..
#
# fi
#


