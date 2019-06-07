 
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct_test = type { i64, i64, i64 }


define %struct_test @create_test() {
  start:
    ret %struct_test zeroinitializer

}
