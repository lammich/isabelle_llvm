#!/usr/bin/gawk -f


BEGIN {
  # Change to configure what is included in plot
  type_display["isabelle::pparqsort"] = "red,verified"
#   type_display["isabelle::parqsort"] = "red,verified-old"
  type_display["boost::sample_sort"] = "black,sample sort"
  type_display["std::parsort"] = "blue,std::sort"


  if (ARGC==2) {
    element_type=ARGV[1]

    ARGC=0
  } else {
    print "Usage: __eval_speedup <elem-type>"
    exit 1
  }





  has_data=0
}



function esc(s) {
  gsub(/_/,"\\_",s)
  return s
}

function printout() {
  if (has_data) {
    for (type in data) {

      if (type in type_display) {

        split (type_display[type],_col_name,",")
        color=_col_name[1]
        name=_col_name[2]

        printf "\n\\addplot+[color=%s, mark color=black, mark options={fill=%s}] coordinates {\n", color, color


        oldorder=PROCINFO["sorted_in"]
        PROCINFO["sorted_in"]="@ind_num_asc"
        for (nelem in data[type]) {
          time = data[type][nelem]
          printf "  (%d, %.2f)\n", nelem, time
        }
        PROCINFO["sorted_in"]=oldorder

        printf "};\n"
        printf "\\addlegendentry{" name "};\n"
      }
    }
  }
}


/^#/ {

    next
}

NF>=9 {

  if ($1 != element_type) next;

  has_data=1
  type=$2
  nelem=$4
  gsub(/x[0-9]+$/,"",nelem)
  time=$9

  data[type][nelem]=time
}


END {
  printout()
}
