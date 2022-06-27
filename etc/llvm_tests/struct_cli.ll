; ModuleID = 'struct_cli.c'
source_filename = "struct_cli.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%union.test = type { double, [8 x i8] }
%union.testXX = type { %struct.anon.0, [8 x i8] }
%struct.anon.0 = type { i64 }
%struct.anon = type { i32, i32, i32 }

@s1 = dso_local global i64 1, align 8
@s2 = dso_local global i64 16, align 8
@t2 = common dso_local global %union.test zeroinitializer, align 8

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @foo(%union.testXX* %0) #0 {
  %2 = alloca %union.testXX*, align 8
  %3 = alloca %union.testXX, align 8
  store %union.testXX* %0, %union.testXX** %2, align 8
  %4 = bitcast %union.testXX* %3 to %struct.anon*
  %5 = getelementptr inbounds %struct.anon, %struct.anon* %4, i32 0, i32 0
  store i32 -1, i32* %5, align 8
  %6 = bitcast %union.testXX* %3 to %struct.anon.0*
  %7 = getelementptr inbounds %struct.anon.0, %struct.anon.0* %6, i32 0, i32 0
  store i64 42, i64* %7, align 8
  %8 = load %union.testXX*, %union.testXX** %2, align 8
  %9 = bitcast %union.testXX* %8 to i8*
  %10 = bitcast %union.testXX* %3 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %9, i8* align 8 %10, i64 16, i1 false)
  ret void
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 %0, i8** %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  %6 = alloca %union.testXX, align 8
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  store i8** %1, i8*** %5, align 8
  %7 = bitcast %union.testXX* %6 to %struct.anon*
  %8 = getelementptr inbounds %struct.anon, %struct.anon* %7, i32 0, i32 0
  store i32 -1, i32* %8, align 8
  %9 = bitcast %union.testXX* %6 to %struct.anon.0*
  %10 = getelementptr inbounds %struct.anon.0, %struct.anon.0* %9, i32 0, i32 0
  store i64 42, i64* %10, align 8
  ret i32 0
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 10.0.0-4ubuntu1 "}
