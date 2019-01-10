; ModuleID = 'arraycpy_cli.c'
source_filename = "arraycpy_cli.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: norecurse nounwind uwtable
define void @arraycp2(i8* nocapture, i8* nocapture readonly, i64) local_unnamed_addr #0 {
  %4 = icmp sgt i64 %2, 0
  br i1 %4, label %5, label %132

; <label>:5:                                      ; preds = %3
  %6 = icmp ult i64 %2, 32
  br i1 %6, label %93, label %7

; <label>:7:                                      ; preds = %5
  %8 = getelementptr i8, i8* %0, i64 %2
  %9 = getelementptr i8, i8* %1, i64 %2
  %10 = icmp ugt i8* %9, %0
  %11 = icmp ugt i8* %8, %1
  %12 = and i1 %10, %11
  br i1 %12, label %93, label %13

; <label>:13:                                     ; preds = %7
  %14 = and i64 %2, -32
  %15 = add i64 %14, -32
  %16 = lshr exact i64 %15, 5
  %17 = add nuw nsw i64 %16, 1
  %18 = and i64 %17, 3
  %19 = icmp ult i64 %15, 96
  br i1 %19, label %71, label %20

; <label>:20:                                     ; preds = %13
  %21 = sub nsw i64 %17, %18
  br label %22

; <label>:22:                                     ; preds = %22, %20
  %23 = phi i64 [ 0, %20 ], [ %68, %22 ]
  %24 = phi i64 [ %21, %20 ], [ %69, %22 ]
  %25 = getelementptr inbounds i8, i8* %1, i64 %23
  %26 = bitcast i8* %25 to <16 x i8>*
  %27 = load <16 x i8>, <16 x i8>* %26, align 1, !tbaa !2, !alias.scope !5
  %28 = getelementptr i8, i8* %25, i64 16
  %29 = bitcast i8* %28 to <16 x i8>*
  %30 = load <16 x i8>, <16 x i8>* %29, align 1, !tbaa !2, !alias.scope !5
  %31 = getelementptr inbounds i8, i8* %0, i64 %23
  %32 = bitcast i8* %31 to <16 x i8>*
  store <16 x i8> %27, <16 x i8>* %32, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %33 = getelementptr i8, i8* %31, i64 16
  %34 = bitcast i8* %33 to <16 x i8>*
  store <16 x i8> %30, <16 x i8>* %34, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %35 = or i64 %23, 32
  %36 = getelementptr inbounds i8, i8* %1, i64 %35
  %37 = bitcast i8* %36 to <16 x i8>*
  %38 = load <16 x i8>, <16 x i8>* %37, align 1, !tbaa !2, !alias.scope !5
  %39 = getelementptr i8, i8* %36, i64 16
  %40 = bitcast i8* %39 to <16 x i8>*
  %41 = load <16 x i8>, <16 x i8>* %40, align 1, !tbaa !2, !alias.scope !5
  %42 = getelementptr inbounds i8, i8* %0, i64 %35
  %43 = bitcast i8* %42 to <16 x i8>*
  store <16 x i8> %38, <16 x i8>* %43, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %44 = getelementptr i8, i8* %42, i64 16
  %45 = bitcast i8* %44 to <16 x i8>*
  store <16 x i8> %41, <16 x i8>* %45, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %46 = or i64 %23, 64
  %47 = getelementptr inbounds i8, i8* %1, i64 %46
  %48 = bitcast i8* %47 to <16 x i8>*
  %49 = load <16 x i8>, <16 x i8>* %48, align 1, !tbaa !2, !alias.scope !5
  %50 = getelementptr i8, i8* %47, i64 16
  %51 = bitcast i8* %50 to <16 x i8>*
  %52 = load <16 x i8>, <16 x i8>* %51, align 1, !tbaa !2, !alias.scope !5
  %53 = getelementptr inbounds i8, i8* %0, i64 %46
  %54 = bitcast i8* %53 to <16 x i8>*
  store <16 x i8> %49, <16 x i8>* %54, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %55 = getelementptr i8, i8* %53, i64 16
  %56 = bitcast i8* %55 to <16 x i8>*
  store <16 x i8> %52, <16 x i8>* %56, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %57 = or i64 %23, 96
  %58 = getelementptr inbounds i8, i8* %1, i64 %57
  %59 = bitcast i8* %58 to <16 x i8>*
  %60 = load <16 x i8>, <16 x i8>* %59, align 1, !tbaa !2, !alias.scope !5
  %61 = getelementptr i8, i8* %58, i64 16
  %62 = bitcast i8* %61 to <16 x i8>*
  %63 = load <16 x i8>, <16 x i8>* %62, align 1, !tbaa !2, !alias.scope !5
  %64 = getelementptr inbounds i8, i8* %0, i64 %57
  %65 = bitcast i8* %64 to <16 x i8>*
  store <16 x i8> %60, <16 x i8>* %65, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %66 = getelementptr i8, i8* %64, i64 16
  %67 = bitcast i8* %66 to <16 x i8>*
  store <16 x i8> %63, <16 x i8>* %67, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %68 = add i64 %23, 128
  %69 = add i64 %24, -4
  %70 = icmp eq i64 %69, 0
  br i1 %70, label %71, label %22, !llvm.loop !10

; <label>:71:                                     ; preds = %22, %13
  %72 = phi i64 [ 0, %13 ], [ %68, %22 ]
  %73 = icmp eq i64 %18, 0
  br i1 %73, label %91, label %74

; <label>:74:                                     ; preds = %71
  br label %75

; <label>:75:                                     ; preds = %75, %74
  %76 = phi i64 [ %72, %74 ], [ %88, %75 ]
  %77 = phi i64 [ %18, %74 ], [ %89, %75 ]
  %78 = getelementptr inbounds i8, i8* %1, i64 %76
  %79 = bitcast i8* %78 to <16 x i8>*
  %80 = load <16 x i8>, <16 x i8>* %79, align 1, !tbaa !2, !alias.scope !5
  %81 = getelementptr i8, i8* %78, i64 16
  %82 = bitcast i8* %81 to <16 x i8>*
  %83 = load <16 x i8>, <16 x i8>* %82, align 1, !tbaa !2, !alias.scope !5
  %84 = getelementptr inbounds i8, i8* %0, i64 %76
  %85 = bitcast i8* %84 to <16 x i8>*
  store <16 x i8> %80, <16 x i8>* %85, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %86 = getelementptr i8, i8* %84, i64 16
  %87 = bitcast i8* %86 to <16 x i8>*
  store <16 x i8> %83, <16 x i8>* %87, align 1, !tbaa !2, !alias.scope !8, !noalias !5
  %88 = add i64 %76, 32
  %89 = add i64 %77, -1
  %90 = icmp eq i64 %89, 0
  br i1 %90, label %91, label %75, !llvm.loop !12

; <label>:91:                                     ; preds = %75, %71
  %92 = icmp eq i64 %14, %2
  br i1 %92, label %132, label %93

; <label>:93:                                     ; preds = %91, %7, %5
  %94 = phi i64 [ 0, %7 ], [ 0, %5 ], [ %14, %91 ]
  %95 = add i64 %2, -1
  %96 = sub i64 %95, %94
  %97 = and i64 %2, 3
  %98 = icmp eq i64 %97, 0
  br i1 %98, label %109, label %99

; <label>:99:                                     ; preds = %93
  br label %100

; <label>:100:                                    ; preds = %100, %99
  %101 = phi i64 [ %106, %100 ], [ %94, %99 ]
  %102 = phi i64 [ %107, %100 ], [ %97, %99 ]
  %103 = getelementptr inbounds i8, i8* %1, i64 %101
  %104 = load i8, i8* %103, align 1, !tbaa !2
  %105 = getelementptr inbounds i8, i8* %0, i64 %101
  store i8 %104, i8* %105, align 1, !tbaa !2
  %106 = add nuw nsw i64 %101, 1
  %107 = add i64 %102, -1
  %108 = icmp eq i64 %107, 0
  br i1 %108, label %109, label %100, !llvm.loop !14

; <label>:109:                                    ; preds = %100, %93
  %110 = phi i64 [ %94, %93 ], [ %106, %100 ]
  %111 = icmp ult i64 %96, 3
  br i1 %111, label %132, label %112

; <label>:112:                                    ; preds = %109
  br label %113

; <label>:113:                                    ; preds = %113, %112
  %114 = phi i64 [ %110, %112 ], [ %130, %113 ]
  %115 = getelementptr inbounds i8, i8* %1, i64 %114
  %116 = load i8, i8* %115, align 1, !tbaa !2
  %117 = getelementptr inbounds i8, i8* %0, i64 %114
  store i8 %116, i8* %117, align 1, !tbaa !2
  %118 = add nuw nsw i64 %114, 1
  %119 = getelementptr inbounds i8, i8* %1, i64 %118
  %120 = load i8, i8* %119, align 1, !tbaa !2
  %121 = getelementptr inbounds i8, i8* %0, i64 %118
  store i8 %120, i8* %121, align 1, !tbaa !2
  %122 = add nsw i64 %114, 2
  %123 = getelementptr inbounds i8, i8* %1, i64 %122
  %124 = load i8, i8* %123, align 1, !tbaa !2
  %125 = getelementptr inbounds i8, i8* %0, i64 %122
  store i8 %124, i8* %125, align 1, !tbaa !2
  %126 = add nsw i64 %114, 3
  %127 = getelementptr inbounds i8, i8* %1, i64 %126
  %128 = load i8, i8* %127, align 1, !tbaa !2
  %129 = getelementptr inbounds i8, i8* %0, i64 %126
  store i8 %128, i8* %129, align 1, !tbaa !2
  %130 = add nsw i64 %114, 4
  %131 = icmp eq i64 %130, %2
  br i1 %131, label %132, label %113, !llvm.loop !15

; <label>:132:                                    ; preds = %109, %113, %91, %3
  ret void
}

; Function Attrs: nounwind uwtable
define i32 @main(i32, i8** nocapture readnone) local_unnamed_addr #1 {
  %3 = tail call noalias i8* @calloc(i64 1, i64 1048576000) #5
  %4 = tail call noalias i8* @calloc(i64 1, i64 1048576000) #5
  tail call void @llvm.memset.p0i8.i64(i8* %4, i8 27, i64 1048576000, i32 1, i1 false)
  tail call void @arraycpy(i8* %3, i8* %4, i64 1048576000) #5
  br label %5

; <label>:5:                                      ; preds = %5, %2
  %6 = phi i64 [ 0, %2 ], [ %30, %5 ]
  %7 = phi <4 x i32> [ zeroinitializer, %2 ], [ %28, %5 ]
  %8 = phi <4 x i32> [ zeroinitializer, %2 ], [ %29, %5 ]
  %9 = getelementptr inbounds i8, i8* %3, i64 %6
  %10 = bitcast i8* %9 to <4 x i8>*
  %11 = load <4 x i8>, <4 x i8>* %10, align 1, !tbaa !2
  %12 = getelementptr i8, i8* %9, i64 4
  %13 = bitcast i8* %12 to <4 x i8>*
  %14 = load <4 x i8>, <4 x i8>* %13, align 1, !tbaa !2
  %15 = sext <4 x i8> %11 to <4 x i32>
  %16 = sext <4 x i8> %14 to <4 x i32>
  %17 = add nsw <4 x i32> %7, %15
  %18 = add nsw <4 x i32> %8, %16
  %19 = or i64 %6, 8
  %20 = getelementptr inbounds i8, i8* %3, i64 %19
  %21 = bitcast i8* %20 to <4 x i8>*
  %22 = load <4 x i8>, <4 x i8>* %21, align 1, !tbaa !2
  %23 = getelementptr i8, i8* %20, i64 4
  %24 = bitcast i8* %23 to <4 x i8>*
  %25 = load <4 x i8>, <4 x i8>* %24, align 1, !tbaa !2
  %26 = sext <4 x i8> %22 to <4 x i32>
  %27 = sext <4 x i8> %25 to <4 x i32>
  %28 = add nsw <4 x i32> %17, %26
  %29 = add nsw <4 x i32> %18, %27
  %30 = add nuw nsw i64 %6, 16
  %31 = icmp eq i64 %30, 1048576000
  br i1 %31, label %32, label %5, !llvm.loop !16

; <label>:32:                                     ; preds = %5
  %33 = add <4 x i32> %29, %28
  %34 = shufflevector <4 x i32> %33, <4 x i32> undef, <4 x i32> <i32 2, i32 3, i32 undef, i32 undef>
  %35 = add <4 x i32> %33, %34
  %36 = shufflevector <4 x i32> %35, <4 x i32> undef, <4 x i32> <i32 1, i32 undef, i32 undef, i32 undef>
  %37 = add <4 x i32> %35, %36
  %38 = extractelement <4 x i32> %37, i32 0
  ret i32 %38
}

; Function Attrs: nounwind
declare noalias i8* @calloc(i64, i64) local_unnamed_addr #2

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1) #3

declare void @arraycpy(i8*, i8*, i64) local_unnamed_addr #4

attributes #0 = { norecurse nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind }
attributes #4 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 6.0.0-1ubuntu2~16.04.1 (tags/RELEASE_600/final)"}
!2 = !{!3, !3, i64 0}
!3 = !{!"omnipotent char", !4, i64 0}
!4 = !{!"Simple C/C++ TBAA"}
!5 = !{!6}
!6 = distinct !{!6, !7}
!7 = distinct !{!7, !"LVerDomain"}
!8 = !{!9}
!9 = distinct !{!9, !7}
!10 = distinct !{!10, !11}
!11 = !{!"llvm.loop.isvectorized", i32 1}
!12 = distinct !{!12, !13}
!13 = !{!"llvm.loop.unroll.disable"}
!14 = distinct !{!14, !13}
!15 = distinct !{!15, !11}
!16 = distinct !{!16, !11}
