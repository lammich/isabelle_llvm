#!/bin/bash
set -e

SEMTEST=./fp_test
CTEST="$HOME/devel/float_test/build/float_test"

CNT=0
CCNT=0

./mktests.sh | while read line; do
  $SEMTEST "$line";
  $CTEST "$line";
  let "CNT+=1"
  let "CCNT+=1"

  if test "$CNT" -gt 1000 ; then
    echo "$CCNT" >&2
    CNT=0
  fi
done
