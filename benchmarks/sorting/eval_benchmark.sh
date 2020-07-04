#!/bin/bash

rm ~/tmp/data*.tex

# cat log/sortbench-2020-01-all.log | ./__eval_benchmark.awk > /tmp/data.tex
cat log/allnew-2020-01.log | ./__eval_benchmark.awk > ~/tmp/data.tex

gawk '$1=="@" { echo=($2=="introsort"); next }  echo {print} ' ~/tmp/data.tex  > ~/tmp/data_introsort.tex
gawk '$1=="@" { echo=($2=="pdqsort"); next }  echo {print} ' ~/tmp/data.tex > ~/tmp/data_pdqsort.tex

# cp ~/tmp/data_introsort.tex ../../papers/sorting/
# cp ~/tmp/data_pdqsort.tex ../../papers/sorting/
