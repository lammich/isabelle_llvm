#!/bin/bash

set -e

CONV="$HOME/devel/float_test/build/float_test cnv"


# for i in fpgen32_testsuite/Basic-Types-Inputs.fptest; do
for i in fpgen32_testsuite/*.fptest; do
  STEM="${i#*/}"
  STEM="${STEM%.*}"
  STEM=$(echo $STEM | sed -re 's/-/_/g')

#     | egrep -v "#| [xuvwozi]+( |$)"\

  echo "$i" >&2

  cat "$i" \
  | egrep '^b32'\
  | egrep -v "#"\
  | sed -re 's/^b32/b32 /'\
  | sed -re 's/ [xuvwozi]+( |$)/ /g' \
  | sed -re 's/ -> / /' \
  | sed -re 's/([+-])([01])\.([0-9A-F]+)P(-?[0-9]+)/\1|\2|0x\3|\4/g;' \
  | $CONV


#   echo -n "val test_$STEM = "
#   ./__mktest.awk "$i"

done

