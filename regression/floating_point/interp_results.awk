#!/bin/gawk -f

BEGIN {
  delete fail
  delete failc

}

$0 ~ /OK/ {next};


$1=="CC" {

  $1=""

  x=$0
  gsub(/^ *|:.*$/,"",x)

#   print ">> " x

  failc[x]=$0

  next
}

{
  x=$0
  gsub(/^ *|:.*$/,"",x)

#   print "<< " x

  fail[x]=$0

  next
}

END {
  for (i in failc) {
    if (!(i in fail)) print "CC " failc[i]
  }

  for (i in fail) {
    if (!(i in failc)) print "SS " fail[i]
  }

  for (i in fail) {
    if ((i in failc)) print "BB " failc[i]
  }

}






