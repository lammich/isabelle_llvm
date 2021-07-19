; ModuleID = 'calling_conv.c'
source_filename = "calling_conv.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.s1 = type { i8, i8, i8 }
%struct.s2 = type { i64, i64 }
%struct.s3 = type { i64, i64, i64 }

; Function Attrs: noinline nounwind optnone uwtable
define dso_local signext i8 @f1(i24 %0) #0 {
  %2 = alloca %struct.s1, align 1
  %3 = alloca i24, align 4
  store i24 %0, i24* %3, align 4
  %4 = bitcast i24* %3 to i8*
  %5 = bitcast %struct.s1* %2 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 %5, i8* align 4 %4, i64 3, i1 false)
  %6 = getelementptr inbounds %struct.s1, %struct.s1* %2, i32 0, i32 1
  %7 = load i8, i8* %6, align 1
  ret i8 %7
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i64 @f2(i64 %0, i64 %1) #0 {
  %3 = alloca %struct.s2, align 8
  %4 = bitcast %struct.s2* %3 to { i64, i64 }*
  %5 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %4, i32 0, i32 0
  store i64 %0, i64* %5, align 8
  %6 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %4, i32 0, i32 1
  store i64 %1, i64* %6, align 8
  %7 = getelementptr inbounds %struct.s2, %struct.s2* %3, i32 0, i32 1
  %8 = load i64, i64* %7, align 8
  ret i64 %8
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i64 @f3(%struct.s3* byval(%struct.s3) align 8 %0) #0 {
  %2 = getelementptr inbounds %struct.s3, %struct.s3* %0, i32 0, i32 1
  %3 = load i64, i64* %2, align 8
  ret i64 %3
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 %0, i8** %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  store i8** %1, i8*** %5, align 8
  ret i32 0
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 10.0.0-4ubuntu1 "}
