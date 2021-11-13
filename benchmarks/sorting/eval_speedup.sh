#!/bin/bash

rm -f ~/tmp/sudata*.tex

# cat log/sortbench-2020-01-all.log | ./__eval_benchmark.awk > /tmp/data.tex
cat log/par-speedup-2021.log | ./__eval_speedup.awk > ~/tmp/sudata.tex

gawk '$1=="@" { echo=($2=="server"); next }  echo {print} ' ~/tmp/sudata.tex  > ~/tmp/sudata_server.tex
gawk '$1=="@" { echo=($2=="laptop"); next }  echo {print} ' ~/tmp/sudata.tex > ~/tmp/sudata_laptop.tex
#
cp ~/tmp/sudata_server.tex ../../papers/llvm_par/
cp ~/tmp/sudata_laptop.tex ../../papers/llvm_par/
