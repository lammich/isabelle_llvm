; ModuleID = 'struct_cli.c'
source_filename = "struct_cli.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.test = type { i64, i64, i64 }

@.str = private unnamed_addr constant [13 x i8] c"%ld,%ld,%ld\0A\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i64 @read_test(%struct.test* byval align 8) #0 {
  %2 = getelementptr inbounds %struct.test, %struct.test* %0, i32 0, i32 1
  %3 = load i64, i64* %2, align 8
  ret i64 %3
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @create_test2(%struct.test* noalias sret) #0 {
  %2 = getelementptr inbounds %struct.test, %struct.test* %0, i32 0, i32 0
  store i64 0, i64* %2, align 8
  %3 = getelementptr inbounds %struct.test, %struct.test* %0, i32 0, i32 1
  store i64 0, i64* %3, align 8
  %4 = getelementptr inbounds %struct.test, %struct.test* %0, i32 0, i32 2
  store i64 0, i64* %4, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32, i8**) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  %6 = alloca %struct.test, align 8
  %7 = alloca %struct.test, align 8
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  store i8** %1, i8*** %5, align 8
  %8 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 0
  store i64 -1, i64* %8, align 8
  %9 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 1
  store i64 -1, i64* %9, align 8
  %10 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 2
  store i64 -1, i64* %10, align 8
  %11 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 0
  %12 = load i64, i64* %11, align 8
  %13 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 1
  %14 = load i64, i64* %13, align 8
  %15 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 2
  %16 = load i64, i64* %15, align 8
  %17 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str, i32 0, i32 0), i64 %12, i64 %14, i64 %16)
  call void @create_test(%struct.test* sret %7)
  %18 = bitcast %struct.test* %6 to i8*
  %19 = bitcast %struct.test* %7 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %18, i8* align 8 %19, i64 24, i1 false)
  %20 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 0
  %21 = load i64, i64* %20, align 8
  %22 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 1
  %23 = load i64, i64* %22, align 8
  %24 = getelementptr inbounds %struct.test, %struct.test* %6, i32 0, i32 2
  %25 = load i64, i64* %24, align 8
  %26 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str, i32 0, i32 0), i64 %21, i64 %23, i64 %25)
  ret i32 0
}

declare dso_local i32 @printf(i8*, ...) #1

declare dso_local void @create_test(%struct.test* sret) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1) #2

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { argmemonly nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 8.0.0 (tags/RELEASE_800/final)"}
