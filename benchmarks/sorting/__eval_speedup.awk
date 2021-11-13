#!/usr/bin/gawk -f


BEGIN {
  # Change to configure what is included in plot
  type_display["isabelle::parqsort"] = "red,verified"
  type_display["boost::sample_sort"] = "black,sample sort"
  type_display["std::parsort"] = "blue,std::sort(par-unseq)"


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

        base=data[type][1]

        for (cores in data[type]) {
          time = data[type][cores]
          printf "  (%d, %.2f)\n", cores, (base/time)
        }

        printf "};\n"
        printf "\\addlegendentry{" name "};\n"
      }
    }
    has_data=0
    delete data
  }
}


/^#/ {

    next
}

$1=="@" {
  printout()
  print
  next
}

$2=="cores" {
  cores = $1

  next
}

NF>=9 {
  has_data=1
  type=$2
  time=$9

  data[type][cores]=time
}


END {
  printout()
}
