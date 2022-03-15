#!/bin/bash

set -e

# for i in fpgen32_testsuite/Basic-Types-Inputs.fptest; do
for i in fpgen32_testsuite/*.fptest; do
  STEM="${i#*/}"
  STEM="${STEM%.*}"
  STEM=$(echo $STEM | sed -re 's/-/_/g')

#     | egrep -v "#| [xuvwozi]+( |$)"\


  cat "$i" \
  | egrep '^b32([-+*/V]|\*\+) '\
  | egrep -v "#"\
  | sed -re 's/ [xuvwozi]+( |$)/ /g' \
  | sed -re 's/ -> / /' \
  | sed -re 's/([+-])([01])\.([0-9A-F]+)P(-?[0-9]+)/\1|\2|0x\3|\4/g;'


#   echo -n "val test_$STEM = "
#   ./__mktest.awk "$i"

done

