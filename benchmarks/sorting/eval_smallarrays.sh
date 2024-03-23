#!/bin/bash

LOGFILE="log/sortbench-smallarrays-latest.log"

if [ "$1" != "" ]; then
  LOGFILE="$1"
fi

OUTFILE="${LOGFILE%.log}.pdf"


rm -rf generate
mkdir -p generate

./__eval_smallarrays.awk uint64 < "$LOGFILE" > generate/d_uint64.tex
./__eval_smallarrays.awk llstring < "$LOGFILE" > generate/d_llstring.tex

cp smallarrays_report.tex generate/

cd generate
pdflatex smallarrays_report
cd ..

cp "generate/smallarrays_report.pdf" "$OUTFILE"
echo "Generated report at $OUTFILE"



# rm -f ~/tmp/sadata*.tex
#
# # cat log/sortbench-2020-01-all.log | ./__eval_benchmark.awk > /tmp/data.tex
#
# cat log/par-smallarrays-2023.log | ./__eval_smallarrays.awk uint64 > ~/tmp/sadata_uint64_laptop.tex
# cat log/server/par-smallarrays-2023.log | ./__eval_smallarrays.awk uint64 > ~/tmp/sadata_uint64_server.tex
#
# cat log/par-smallarrays-2023.log | ./__eval_smallarrays.awk llstring > ~/tmp/sadata_llstring_laptop.tex
# cat log/server/par-smallarrays-2023.log | ./__eval_smallarrays.awk llstring > ~/tmp/sadata_llstring_server.tex
#
#
# # gawk '$1=="@" { echo=($2=="server"); next }  echo {print} ' ~/tmp/sudata.tex  > ~/tmp/sudata_server.tex
# # gawk '$1=="@" { echo=($2=="laptop"); next }  echo {print} ' ~/tmp/sudata.tex > ~/tmp/sudata_laptop.tex
# #
# cp ~/tmp/sadata_{uint64,llstring}_{laptop,server}.tex ../../papers/JAR_SI_ITP2022/
