#!/bin/bash


function run() {
  DIR=$1
  NAME=$2

  make -C "$DIR" bs

  LOG="bs-$NAME.log"
  
  date >$LOG

  for ((n=1000000;n<=10000000;n+=1000000)) do
    $DIR/bs $n | tee -a "$LOG"
  done
}

function eval() {
  NAME=$1
  LOG="bs-$NAME.log"
  
  egrep "^@" $LOG | sed -re 's/^@//'
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
  run ../etc/binsearch_c CPP
  run ../thys-2019/examples/code LLVM
  run ../etc/binsearch_impholx SMLX
  run ../etc/binsearch_imphol SML
fi  
  
eval CPP
eval LLVM
eval SMLX
eval SML


