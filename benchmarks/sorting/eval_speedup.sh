#!/bin/bash

rm -f ~/tmp/sudata*.tex

# cat log/sortbench-2020-01-all.log | ./__eval_benchmark.awk > /tmp/data.tex

cat log/par-speedup-2023.log | ./__eval_speedup.awk uint64 > ~/tmp/sudata_uint64_laptop.tex
cat log/server/par-speedup-2023.log | ./__eval_speedup.awk uint64 > ~/tmp/sudata_uint64_server.tex

cat log/par-speedup-2023.log | ./__eval_speedup.awk llstring > ~/tmp/sudata_llstring_laptop.tex
cat log/server/par-speedup-2023.log | ./__eval_speedup.awk llstring > ~/tmp/sudata_llstring_server.tex


# gawk '$1=="@" { echo=($2=="server"); next }  echo {print} ' ~/tmp/sudata.tex  > ~/tmp/sudata_server.tex
# gawk '$1=="@" { echo=($2=="laptop"); next }  echo {print} ' ~/tmp/sudata.tex > ~/tmp/sudata_laptop.tex
#
cp ~/tmp/sudata_{uint64,llstring}_{laptop,server}.tex ../../papers/JAR_SI_ITP2022/
