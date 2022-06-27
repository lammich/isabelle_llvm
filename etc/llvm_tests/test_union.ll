target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%size_t = type i64

%struct1 = type {i32,double}
%struct2 = type {i64,i64,i64}


%structraw = type [
  (ptrtoint (getelementptr(%struct1*, null, i32 1) to %size_t)) x i8
]

%structraw = type { [
  (select(
    icmp ugt (
      ptrtoint (getelementptr(%struct1*, null, i32 1) to %size_t),
      ptrtoint (getelementptr(%struct2*, null, i32 1) to %size_t)
    ),
    ptrtoint (getelementptr(%struct1*, null, i32 1) to %size_t),
    ptrtoint (getelementptr(%struct2*, null, i32 1) to %size_t)
  )) x i8
] }

%size_struct1 = ptrtoint (getelementptr(%struct1*, null, i32 1) to %size_t)


define i32 main(i32 %argc, i8** %argv) {


  ret 0
}




