#!/bin/bash
set -e

CONV="$HOME/devel/float_test/build/float_test cnv"

CNT=0
CCNT=0

./mktests.sh | sed -re 's/^b32/b32 /' | while read line; do
  $CONV "$line";

  let "CNT+=1"
  let "CCNT+=1"

  if test "$CNT" -gt 1000 ; then
    echo "$CCNT" >&2
    CNT=0
  fi
done
