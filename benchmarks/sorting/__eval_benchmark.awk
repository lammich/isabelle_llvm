#!/usr/bin/gawk -f

/^#/ {

    next
}

/^@LAPTOP/ {
  machine="L"
  next
}

/^@SERVER/ {
  machine="S"
  next
}


match ($0,/(.*):.+\[.*\](.*)/,fld) {

  name = fld[1]

  n = split(fld[2], vals)


  dev = (vals[7]-vals[4]) / vals[7]

  sum = 0

  for (i=4;i<=7;++i) {
    sum = sum + vals[i]
  }

  avg = sum / 4


  if ($1 == "NO_LLVM") {
    type=$2
    algo=$3 "-gcc"
    distr=$4
  } else {
    type=$1
    algo=$2
    distr=$3
  }


  if (dev<.02) {
    results[distr][type][algo][machine] = avg
  }
#   else {
#     results[machine][type][distr][algo] = "REPEAT!"
#     print "REPEAT (" dev ") " name
#   }

#   print
}

function pr_res(am) {
  Lstdtime=am["std::sort"]["L"]
  Lisatime=am["isabelle::sort"]["L"]
  Sstdtime=am["std::sort"]["S"]
  Sisatime=am["isabelle::sort"]["S"]

  Lfraction = Lisatime/Lstdtime - 1
  Sfraction = Sisatime/Sstdtime - 1

  printf "%.1f & %.1f", Lfraction*100, Sfraction*100



}

END {

  for (distr in results) {
    printf "%s & ", distr
    pr_res(results[distr]["uint64"])
    printf "&"
    pr_res(results[distr]["llstring"])
    printf "\\\\\n"
  }


#   for (type in results["L"]) {
#     print "###### " type
#     for (distr in results["L"][type]) {
#       printf "%s: ", distr
#
#
#       Lstdtime=results["L"][type][distr]["std::sort"]
#       Lisatime=results["L"][type][distr]["isabelle::sort"]
#       Sstdtime=results["S"][type][distr]["std::sort"]
#       Sisatime=results["S"][type][distr]["isabelle::sort"]
#
#       Lfraction = Lisatime/Lstdtime
#       Sfraction = Sisatime/Sstdtime
#
#       printf "%f", Lfraction*100
#       if (Lfraction < .85 || Lfraction > 1.15) printf " ***"
#
#       printf " %f", Sfraction*100
#       if (Sfraction < .85 || Sfraction > 1.15) printf " ***"
#
#       printf " cc %f %f", (Sstdtime/Lstdtime*100), (Sisatime/Lisatime*100)
#
#
# #       for (algo in times) {
# #         time = results[type][distr][algo]
# #         printf "%s: %d ", algo, time
# #       }
#       printf "\n"
#     }
#   }


}


