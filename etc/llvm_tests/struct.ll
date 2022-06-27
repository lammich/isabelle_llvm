 
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct_test = type { i64, i64, i64 }
%struct_test2 = type { double, double, double }
%pat_test = type { float, float, double, double }

; declare i20000 @llvm.ctlz.i20000(i20000, i1)
;
; define i20000 @test(i20000 %x) {
;   %y = call i20000 @llvm.ctlz.i20000(i20000 %x, i1 true)
;
;   ret i20000 %y
; }


define i64 @create_test(%pat_test %arg) {
  start:

    %r1 = alloca %struct_test
    %r2 = bitcast %struct_test * %r1 to %pat_test *
    store %pat_test %arg, %pat_test * %r2
    %r3 = load %struct_test, %struct_test * %r1

    %r4 = extractvalue %struct_test %r3, 0

    ret i64 %r4
}
