#!/bin/gawk -f

function error(msg) {
  print ""
  print "Error: " msg > "/dev/stderr"
  print "On input line: " orig_vector > "/dev/stderr"
  exit 1
}


BEGIN {
  xlate_fun["b32+"]="check_fadd32"
  xlate_fun["b32-"]="check_fsub32"
  xlate_fun["b32*"]="check_fmul32"
  xlate_fun["b32/"]="check_fdiv32"
  xlate_fun["b32*+"]="check_fmul_add32"

  xlate_fun_opn["b32+"]=2
  xlate_fun_opn["b32-"]=2
  xlate_fun_opn["b32*"]=2
  xlate_fun_opn["b32/"]=2
  xlate_fun_opn["b32*+"]=3


  xlate_rmode["=0"]="To_nearest"
  xlate_rmode["0"]="round_To_zero"
  xlate_rmode[">"]="To_pinfinity"
  xlate_rmode["<"]="To_ninfinity"

  xlate_op["S"]="sNaN32"
  xlate_op["Q"]="qNaN32"
  xlate_op["+Zero"]="plus_zero32"
  xlate_op["-Zero"]="minus_zero32"
  xlate_op["+Inf"]="plus_inf32"
  xlate_op["-Inf"]="minus_inf32"


  count=0

  print "["
}


function xl_fun(f) {
  if (!(f in xlate_fun)) error("Unknown function " f)
  return xlate_fun[f]
}

function xl_rmode(f) {
  if (!(f in xlate_rmode)) error("Unknown rounding mode " f)
  return xlate_rmode[f]
}

function xl_op(x) {
  if (x in xlate_op) return xlate_op[x];

  delete parts

  if (!match(x,/^([+-])[01]\.([0-9A-F]+)P(-?)([0-9]+)$/,parts)) error("Unknown operand format: " x)

  if (parts[1]=="+") sign=0; else sign=1

  if (parts[3]=="-") esign="~"; else esign=""

  return "fp32 " sign " 0x" parts[2] " (" esign parts[4] ")"

}


{
  orig_vector=$0

}


!($1 in xlate_fun) {next}


{
  gsub(/ [xuvwozi]+( |$)/," ")
  gsub(/ -> /," ")

}

$0 ~ /#/ {
  next
}

{

  fname=xl_fun($1)
  argnum=xlate_fun_opn[$1]
  rmode=xl_rmode($2)

  if (NF != 3+argnum) error("Wrong number of operands")

  res = fname " " rmode

  for (i=3;i<=NF;i++) {
    if (i==NF) res=res ", "
    res = res " (" xl_op($i) ")"
  }

  if (count) print ","

  printf ("(%d,%s)",count,res)

  count++

}

END {
  print ""
  print "]"
}

