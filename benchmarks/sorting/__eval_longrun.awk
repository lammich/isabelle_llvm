#!/usr/bin/gawk -f

/^#/ {

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


  res_sum[algo][distr][type] += avg
  res_count[algo][distr][type] += 1

  if (res_min[algo][distr][type] == 0 || avg < res_min[algo][distr][type]) res_min[algo][distr][type]=avg
  if (res_max[algo][distr][type] == 0 || avg > res_max[algo][distr][type]) res_max[algo][distr][type]=avg


#   else {
#     results[machine][type][distr][algo] = "REPEAT!"
#     print "REPEAT (" dev ") " name
#   }

#   print
}


function pr_res(algo,distr) {
  type="uint64"

  min=res_min[algo][distr][type] / 1000
  max=res_max[algo][distr][type] / 1000

  dev = (max/min - 1)*100

  printf "%.2f & %.2f & %.1f",min,max,dev
}

END {
  printf "random(min,max,dev) organ-pipe(min,max,dev)\n"

  for (algo in res_sum) {
    printf "%s &", algo
    pr_res(algo,"random")
    printf " & "
    pr_res(algo,"organ-pipe")
    printf " \\\\\n"
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


