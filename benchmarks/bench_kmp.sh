#!/bin/bash

function run() {
  DIR=$1
  NAME=$2
  ITER=$3

  make -C "$DIR" kmp
  
  ./_run_kmp_bench.sh $NAME "$DIR/kmp" $ITER
}

function eval() {
  NAME=$1
  
  for i in kmp-$NAME-*-*.log; do
    echo -n "$i: "
    grep '^@' "$i" | sed 's/.*://' | gawk '{x=x+$1} END {print x/1000}'
  done
}




RUN=false

while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -r|--run)
    RUN=true
    ;;
    *)
    echo "Unknown command line argument $1"        # unknown option
    exit 1
    ;;
esac
shift # past argument or value
done

if $RUN; then
  run ../etc/kmp_c CPP 50
  run ../thys/examples/code LLVM 50
  run ../etc/kmp_impholx SMLX 30
  run ../etc/kmp_imphol SML 10
fi  
  
eval CPP
eval LLVM
eval SMLX
eval SML
