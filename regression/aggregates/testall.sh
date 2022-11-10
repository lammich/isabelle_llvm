#!/bin/bash

ISABELLE=isabelle

set -e

echo "Aggregate Tests"

echo "  Cleaning up"

rm -f generated/*

echo "  Building thy and generating tests"

$ISABELLE build -c -d . Aggregate_Tests


exitcode=0

function error() {
  echo $1
  exitcode=1
}

echo "  Compiling and running generated tests"

ntest=0

for C_FILE in generated/aggr_test_*.c; do

  STEM="${C_FILE%.c}"

  LL_FILE="$STEM.gen.ll"
  BIN_FILE="$STEM"

  if clang $C_FILE $LL_FILE -o $BIN_FILE; then
    if ! ./$BIN_FILE; then
      clang -S -emit-llvm $C_FILE
      error "FAILED TEST: $STEM"
    fi
  else
    error "FAILED COMPILATION: $STEM"
  fi

  ntest=$((ntest+1))
done

if test $exitcode -eq 0; then
  echo "DONE (Aggregate Tests) $ntest tests completed"
else
  echo "ERROR (Aggregate Tests)"
fi  

exit $exitcode

