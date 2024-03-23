#!/usr/bin/gawk -f

BEGIN {
  if (ARGC == 2) {
    sample_elem_type=ARGV[1]

    ARGC=0
  } else {
    print "Usage __eval_benchmark <elem-type>" > "/dev/stderr"
    exit 1
  }

}


/^#/ {

    next
}

match ($0,/:.+\[.*\](.*)/,fld) {

  n = split(fld[1], vals)
  minv = vals[1]

  if ($1 == "NO_LLVM") {
    type=$2
    algo=$3 "-gcc"
    distr=$4
  } else {
    type=$1
    algo=$2
    distr=$3
  }

  results[type][distr][algo] = minv

#   printf "add %s %s %s = %f\n", type,distr,algo, minv

  next
}


function pr_res_pgf_abs(name,color,ty,alg) {

  printf "\\addplot[color=%s,fill=%s] coordinates {\n",color,color
  for (distr in results[ty]) {
    t = results[ty][distr][alg]

    printf "(%s,%f)\n",distr,t
  }
  printf "};\n\\addlegendentry{%s};\n", name
}


function output_pgf_abs (elem_type) {

  pr_res_pgf_abs("verified","red",elem_type,"isabelle::pparqsort");
  pr_res_pgf_abs("verified-old","gray",elem_type,"isabelle::parqsort");
  pr_res_pgf_abs("std::sort","blue",elem_type,"std::parsort");
  pr_res_pgf_abs("sample sort","black",elem_type,"boost::sample_sort");

}

END {

  output_pgf_abs(sample_elem_type)

}


