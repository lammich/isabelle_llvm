; Generated by Isabelle/LLVM-shallow
target datalayout = "e-m:e-p:64:64:64-a:0:64-n8:16:32:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f16:16:16-f32:32:32-f64:64:64-f128:128:128"
target triple = "x86_64-pc-linux-gnu"



declare i8* @isabelle_llvm_calloc(i64, i64)
declare void @isabelle_llvm_parallel(void ( i8* ) *, void ( i8* ) *, i8*, i8*)

define void @__isabelle_llvm_par_wrapper_0_1 (i8 * %clpv) {

  %clp = bitcast i8* %clpv to {i64 *, i64} *

  %cl = load {i64 *, i64}, {i64 *, i64} *%clp

  %resp = extractvalue {i64 *, i64} %cl, 0
  %arg = extractvalue {i64 *, i64} %cl, 1

  %res = call i64 @LLVM_Codegen_Preproc_experiment7478462_fib (i64 %arg)

  store i64 %res, i64 *%resp

  ret void
}


define void @__isabelle_llvm_par_wrapper_0_2 (i8 * %clpv) {

  %clp = bitcast i8* %clpv to {i16 *, i32} *

  %cl = load {i16 *, i32}, {i16 *, i32} *%clp

  %resp = extractvalue {i16 *, i32} %cl, 0
  %arg = extractvalue {i16 *, i32} %cl, 1

  %res = call i16 @LLVM_Codegen_Preproc_experiment7478462_test2 (i32 %arg)

  store i16 %res, i16 *%resp

  ret void
}


define {i64, i16} @__isabelle_llvm_par_call_0(i64 %arg1, i32 %arg2) {
  ; Build closure1
  %resp1 = alloca i64

  %cl1a = insertvalue {i64 *, i64} zeroinitializer, i64* %resp1, 0
  %cl1 = insertvalue {i64 *, i64} %cl1a, i64 %arg1, 1

  %cl1p = alloca {i64 *, i64}
  store {i64 *, i64} %cl1, {i64 *, i64}* %cl1p

  ; Build closure2
  %resp2 = alloca i16

  %cl2a = insertvalue {i16 *, i32} zeroinitializer, i16* %resp2, 0
  %cl2 = insertvalue {i16 *, i32} %cl2a, i32 %arg2, 1

  %cl2p = alloca {i16 *, i32}
  store {i16 *, i32} %cl2, {i16 *, i32}* %cl2p

  ; Invoke parallel
  %cl1pv = bitcast {i64 *, i64}* %cl1p to i8*
  %cl2pv = bitcast {i16 *, i32}* %cl2p to i8*

  call void @isabelle_llvm_parallel (void (i8 *) *@__isabelle_llvm_par_wrapper_0_1, void (i8 *) *@__isabelle_llvm_par_wrapper_0_2, i8 * %cl1pv, i8 * %cl2pv)

  ; Extract results
  %res1 = load i64, i64* %resp1
  %res2 = load i16, i16* %resp2

  ; Assemble result
  %resa = insertvalue {i64, i16} zeroinitializer, i64 %res1, 0
  %res = insertvalue {i64, i16} %resa, i16 %res2, 1

  ret {i64, i16} %res
}


attributes #0 = { strictfp }

define i64 @LLVM_Codegen_Preproc_experiment7478462_fib(i64 %n) #0 {

  start:
    %x = call i64 @LLVM_Codegen_Preproc_experiment7478462_fib_f_07519954 (i64 %n)
    ret i64 %x
}

define i16 @LLVM_Codegen_Preproc_experiment7478462_test2(i32 %n) #0 {

  start:
    %n1 = add i32 %n, 42
    %a = zext i32 %n1 to i64
    %t = getelementptr i16, i16* null, i64 1
    %b = ptrtoint i16* %t to i64
    %c = call i8* @isabelle_llvm_calloc (i64 %a, i64 %b)
    %p = bitcast i8* %c to i16*
    %pa = getelementptr i16, i16* %p, i32 5
    store i16 42, i16* %pa
    %x = load i16, i16* %pa
    ret i16 %x
}

define { i64, i16 } @LLVM_Codegen_Preproc_experiment7478462_test_ppar() #0 {

  start:
    %x = call { i64, i16 } @__isabelle_llvm_par_call_0 (i64 3, i32 3)
    ret { i64, i16 } %x
}

define i64 @LLVM_Codegen_Preproc_experiment7478462_fib_f_07519954(i64 %x) #0 {

  start:
    %t = icmp ule i64 %x, 1
    br i1 %t, label %then, label %else

  then:
    br label %ctd_if

  else:
    %n_1 = sub i64 %x, 1
    %a = call i64 @LLVM_Codegen_Preproc_experiment7478462_fib_f_07519954 (i64 %n_1)
    %n_2 = sub i64 %x, 2
    %x1 = call i64 @LLVM_Codegen_Preproc_experiment7478462_fib_f_07519954 (i64 %n_2)
    %x2 = add i64 %a, %x1
    br label %ctd_if

  ctd_if:
    %x3 = phi i64 [ %x2, %else ], [ %x, %then ]
    ret i64 %x3
}
