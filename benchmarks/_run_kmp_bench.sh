#!/bin/bash

# Usage: _run_kmp_bench name kmp_binary iterations

NAME=$1
KMP=$2
ITERS=$3



for als in 16 32 64; do
  SAM="kmp_data/sample-$als.sample"
  for ss in 8 64 512; do
    PAT="kmp_data/pattern-$als-$ss.result"
  
    LOG="kmp-$NAME-$als-$ss.log"
    date >$LOG
  
    sed 's/:.*//' "$PAT" | while read s; do
      # echo "'$s'"
      $KMP $ITERS "$s" "$SAM" | tee -a $LOG
    done  
  
  done
done



