#!/usr/bin/gawk -f

/^#/ {

    next
}

/^@LAPTOP/ {
  current_machine="L"
  machines[current_machine]=1
  next
}

/^@SERVER/ {
  current_machine="S"
  machines[current_machine]=1
  next
}

function is_valid_point(distr,type,algo,m) {
   return ((distr in results) && (type in results[distr]) && (algo in results[distr][type]) && (m in results[distr][type][algo]) && (results[distr][type][algo][m] != "REPEAT"))

}


function register_point(distr,type,algo,m,dev,val) {

  if (! val) {
    print "ERROR, ZERO VAL"
    exit 1
  }

  # Indicates if the last measurement was noisy
  lfnoise[distr][type][algo][m] = (dev >= .02)

  if (is_valid_point(distr,type,algo,m)) {
    if (val < results[distr][type][algo][m]) {
      results[distr][type][algo][m]=val;
    }
  } else {
    results[distr][type][algo][m]=val
#     if (dev < .02) results[distr][type][algo][m]=val;
#     else results[distr][type][algo][m]="REPEAT"
  }
}


match ($0,/(.*):.+\[.*\](.*)/,fld) {

  name = fld[1]

  n = split(fld[2], vals)


  dev = (vals[7]-vals[4]) / vals[7]
  minv = vals[1]

  sum = 0

  for (i=4;i<=7;++i) {
    sum = sum + vals[i]
  }

  avg = sum / 4


  if ($1 == "NO_LLVM") {
    type=$2
    algo=$3 "-gcc"
    distr=$4
    numxr=$5
  } else {
    type=$1
    algo=$2
    distr=$3
    numxr=$4
  }

  split(numxr,numxra,"x")

  num=numxra[1]
  rpt=numxra[2]

  arraysize[distr][type][algo][current_machine]=num
  iterations[distr][type][algo][current_machine]=rpt

  register_point(distr,type,algo,current_machine,dev,minv)

#   if (dev<.02) {
#     results[distr][type][algo][current_machine] = avg
#   }
#   else {
#     results[distr][type][algo][current_machine] = "REPEAT"
# #    print "REPEAT (" dev ") " name
#   }

#   printf "LOG: %s %s %s %s \n"

#   print

  next
}


# $0 {
#   print "Error. Cannot read line " $0
#   exit 1
# }


function pr_res(am) {
  Lstdtime=am["std::sort"]["L"]
  Lisatime=am["isabelle::sort"]["L"]
  Sstdtime=am["std::sort"]["S"]
  Sisatime=am["isabelle::sort"]["S"]

  Lfraction = Lisatime/Lstdtime - 1
  Sfraction = Sisatime/Sstdtime - 1

  printf "%.1f & %.1f", Lfraction*100, Sfraction*100
}


function pr_res_pgf(name,color,ty,m,alg1,alg2) {
  if (! (m in machines)) return;

  printf "\\addplot[color=%s,fill=%s] coordinates {\n",color,color
  for (distr in results) {
    t1 = results[distr][ty][alg1][m]
    t2 = results[distr][ty][alg2][m]

#     printf "XX %s %s %s %s\n",name,distr,t1,t2

    if (t1>t2) {
      val = t1/t2 - 1
    } else {
      val = -(t2/t1 - 1)
    }

    printf "(%s,%.1f)\n",distr,val*100
  }
  printf "};\n\\addlegendentry{%s};\n", name
}

function output_pgf () {
  print "@ preamble"

  printf "\n\n"
  printf("symbolic x coords={")
  for (distr in results) {
    printf("%s,",distr)
  }
  printf "}\n\n"

  print "@ introsort"

  pr_res_pgf("uint64 (server)","red","uint64","S","isabelle::sort","std::sort");
  pr_res_pgf("uint64 (laptop)","green","uint64","L","isabelle::sort","std::sort");

  pr_res_pgf("string (server)","blue",  "llstring","S","isabelle::sort","std::sort");
  pr_res_pgf("string (laptop)","black","llstring","L","isabelle::sort","std::sort");


  print "@ pdqsort"

  pr_res_pgf("uint64 (server)","red","uint64","S","isabelle::pdqsort","boost::pdqsort");
  pr_res_pgf("uint64 (laptop)","green","uint64","L","isabelle::pdqsort","boost::pdqsort");

  pr_res_pgf("string (server)","blue",   "llstring","S","isabelle::pdqsort","boost::pdqsort");
  pr_res_pgf("string (laptop)","black",  "llstring","L","isabelle::pdqsort","boost::pdqsort");


}


function pr_res_pgf_abs(name,color,ty,m,alg) {
  if (! (m in machines)) return;

  printf "\\addplot[color=%s,fill=%s] coordinates {\n",color,color
  for (distr in results) {
    t = results[distr][ty][alg][m]

    printf "(%s,%d)\n",distr,t
  }
  printf "};\n\\addlegendentry{%s};\n", name
}

function output_pgf_abs () {
  print "@ preamble"

  printf "\n\n"
  printf("symbolic x coords={")
  for (distr in results) {
    printf("%s,",distr)
  }
  printf "}\n\n"

  print "@ introsort"

#   pr_res_pgf_abs("isa-uint64 (server)","red","uint64","S","isabelle::sort");
#   pr_res_pgf_abs("std-uint64 (server)","red","uint64","S","std::sort");
#
#   pr_res_pgf_abs("isa-uint64 (laptop)","green","uint64","L","isabelle::sort");
#   pr_res_pgf_abs("std-uint64 (laptop)","green","uint64","L","std::sort");
#
#   pr_res_pgf_abs("isa-string (server)","blue",  "llstring","S","isabelle::sort");
#   pr_res_pgf_abs("std-string (server)","blue",  "llstring","S","std::sort");
#
#   pr_res_pgf_abs("isa-string (laptop)","black","llstring","L","isabelle::sort");
#   pr_res_pgf_abs("std-string (laptop)","black","llstring","L","std::sort");


  print "@ pdqsort"

#   pr_res_pgf_abs("isa-uint64 (server)","red","uint64","S","isabelle::pdqsort");
#   pr_res_pgf_abs("std-uint64 (server)","red","uint64","S","boost::pdqsort");

  pr_res_pgf_abs("isa-uint64 (laptop)","green","uint64","L","isabelle::pdqsort");
  pr_res_pgf_abs("std-uint64 (laptop)","green","uint64","L","boost::pdqsort");

#   pr_res_pgf_abs("isa-string (server)","blue",   "llstring","S","isabelle::pdqsort");
#   pr_res_pgf_abs("std-string (server)","blue",   "llstring","S","boost::pdqsort");
#
#   pr_res_pgf_abs("isa-string (laptop)","black",  "llstring","L","isabelle::pdqsort");
#   pr_res_pgf_abs("std-string (laptop)","black",  "llstring","L","boost::pdqsort");


}



function pr_rpt_cmd(distr,type,m,alg) {
  num = arraysize[distr][type][alg][m]
  rpt = iterations[distr][type][alg][m]
  printf ">%s ./do_benchmark %s %s %s %d %d\n",m,type,alg,distr,num,rpt
}

function pr_rpt_noise(distr,type,m,alg) {
  printf ">%s echo '# Repeated b/c noise > 2\\%'\n",m
  pr_rpt_cmd(distr,type,m,alg)
  printf "\n",m
}

function pr_rpt_diff(distr,type,m,alg1,alg2,t1,t2) {
  printf ">%s echo '# Repeated b/c difference > 15\\% (%d,%d)'\n",m,t1,t2
  pr_rpt_cmd(distr,type,m,alg1)
  pr_rpt_cmd(distr,type,m,alg2)
  printf "\n",m
}

function check_diverg(distr,type,m,alg1,alg2) {

  if (arraysize[distr][type][alg1][m] != arraysize[distr][type][alg2][m]) {
    printf "%s %s %s: %s/%s DIFFERENT ARRAY SIZES \n", m, type, distr, alg1, alg2
  }

  if (lfnoise[distr][type][alg1][m]) {
    pr_rpt_noise(distr,type,m,alg1)
  }

  if (lfnoise[distr][type][alg2][m]) {
    pr_rpt_noise(distr,type,m,alg2)
  }

  # if (!lfnoise[distr][type][alg1][m] && !lfnoise[distr][type][alg2][m]) {
    if (is_valid_point(distr,type,alg1,m) && is_valid_point(distr,type,alg2,m)) {
      t1 = results[distr][type][alg1][m]
      t2 = results[distr][type][alg2][m]

      frac = t1 / t2

      if (frac < .85 || frac > 1.15) {
        pr_rpt_diff(distr,type,m,alg1,alg2,t1,t2)
      }
    }
  # }

#   if (t1=="REPEAT") {
#     # printf "%s %s %s: %s -> NOISE>2\\%, REPEAT\n",m, type, distr, alg1
#     pr_rpt_noise(distr,type,m,alg1)
#   } else if (t2=="REPEAT") {
#     # printf "%s %s %s: %s -> NOISE>2\\%, REPEAT\n",m, type, distr, alg2
#     pr_rpt_noise(distr,type,m,alg2)
#   } else if (t1 && t2) {
#     frac = t1 / t2
#
#     if (frac < .85 || frac > 1.15) {
#       pr_rpt_diff(distr,type,m,alg1,alg2,t1,t2)
#       # printf "%s %s %s: %s/%s = %f\n", m, type, distr, alg1, alg2, frac
#     }
#   }
}

function pr_rptscript_header(m) {
  printf ">%s #!/bin/bash \n",m
  printf ">%s echo -n '# '; date \n",m
  printf ">%s echo -n '# '; uname -a \n",m
}

function check_divergs() {
  for (m in machines) {
    pr_rptscript_header(m)
    for (distr in results) {
      for (type in results[distr]) {
        check_diverg(distr,type,m,"std::sort","isabelle::sort");
        check_diverg(distr,type,m,"boost::pdqsort","isabelle::pdqsort");
      }
    }
  }
}


END {
 # check_divergs()

#  output_pgf()
 output_pgf_abs()

}


