#!/bin/bash

set -e

function error() {
  echo "Error: $@"
  exit 1
}

rm -rf generate
mkdir generate

LOGFILE="log/sortbench-latest.log"

if [ "$1" != "" ]; then
  LOGFILE="$1"
fi

OUTFILE="${LOGFILE%.log}.pdf"


./__eval_benchmark.awk uint64 < "$LOGFILE" > generate/d_uint64.tex
./__eval_benchmark.awk llstring < "$LOGFILE" > generate/d_llstring.tex

cp distr_report.tex generate/

cd generate
pdflatex distr_report
cd ..

cp "generate/distr_report.pdf" "$OUTFILE"
echo "Generated report at $OUTFILE"


# rm -f ~/tmp/data*.tex
#
# # cat log/sortbench-2020-01-all.log | ./__eval_benchmark.awk > /tmp/data.tex
# cat log/server/par-2023.log | ./__eval_benchmark.awk S uint64 > ~/tmp/data_server_uint64.tex
# cat log/server/par-2023.log | ./__eval_benchmark.awk S llstring > ~/tmp/data_server_llstring.tex
#
# cat log/par-2023.log | ./__eval_benchmark.awk L uint64 > ~/tmp/data_laptop_uint64.tex
# cat log/par-2023.log | ./__eval_benchmark.awk L llstring > ~/tmp/data_laptop_llstring.tex
#
# # cat log/par-2021.log | ./__eval_benchmark.awk
# #
# # exit
#
# # grep ">L" ~/tmp/data.tex | sed -re 's/^>. //' > repeat_laptop.sh
# # grep ">S" ~/tmp/data.tex | sed -re 's/^>. //' > repeat_server.sh
#
#
# # gawk '$1=="@" { echo=($2=="server"); next }  echo {print} ' ~/tmp/data.tex  > ~/tmp/data_server.tex
# # gawk '$1=="@" { echo=($2=="laptop"); next }  echo {print} ' ~/tmp/data.tex > ~/tmp/data_laptop.tex
# #
# cp ~/tmp/data*.tex ../../papers/JAR_SI_ITP2022/
