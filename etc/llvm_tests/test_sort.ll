; ModuleID = 'test_sort.cpp'
source_filename = "test_sort.cpp"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%"class.std::ios_base::Init" = type { i8 }
%"struct.__gnu_cxx::__ops::_Iter_less_iter" = type { i8 }

$_ZSt4sortIPiEvT_S1_ = comdat any

$_ZSt16__introsort_loopIPilN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_T1_ = comdat any

$_ZSt22__final_insertion_sortIPiN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_ = comdat any

$_ZSt11__make_heapIPiN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_RT0_ = comdat any

@_ZStL8__ioinit = internal global %"class.std::ios_base::Init" zeroinitializer, align 1
@__dso_handle = external hidden global i8
@llvm.global_ctors = appending global [1 x { i32, void ()*, i8* }] [{ i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_test_sort.cpp, i8* null }]

declare void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"*) unnamed_addr #0

; Function Attrs: nounwind
declare void @_ZNSt8ios_base4InitD1Ev(%"class.std::ios_base::Init"*) unnamed_addr #1

; Function Attrs: nounwind
declare i32 @__cxa_atexit(void (i8*)*, i8*, i8*) local_unnamed_addr #2

; Function Attrs: norecurse noreturn uwtable
define i32 @main(i32, i8** nocapture readnone) local_unnamed_addr #3 {
  tail call void @_ZSt4sortIPiEvT_S1_(i32* null, i32* inttoptr (i64 40 to i32*))
  tail call void @llvm.trap()
  unreachable
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #4

; Function Attrs: inlinehint uwtable
define linkonce_odr void @_ZSt4sortIPiEvT_S1_(i32*, i32*) local_unnamed_addr #5 comdat {
  %3 = icmp eq i32* %0, %1
  br i1 %3, label %12, label %4

; <label>:4:                                      ; preds = %2
  %5 = ptrtoint i32* %1 to i64
  %6 = ptrtoint i32* %0 to i64
  %7 = sub i64 %5, %6
  %8 = ashr exact i64 %7, 2
  %9 = tail call i64 @llvm.ctlz.i64(i64 %8, i1 true) #2, !range !2
  %10 = shl nuw nsw i64 %9, 1
  %11 = xor i64 %10, 126
  tail call void @_ZSt16__introsort_loopIPilN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_T1_(i32* %0, i32* %1, i64 %11)
  tail call void @_ZSt22__final_insertion_sortIPiN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_(i32* %0, i32* %1)
  br label %12

; <label>:12:                                     ; preds = %2, %4
  ret void
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #4

; Function Attrs: uwtable
define linkonce_odr void @_ZSt16__introsort_loopIPilN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_T1_(i32*, i32*, i64) local_unnamed_addr #6 comdat {
  %4 = alloca %"struct.__gnu_cxx::__ops::_Iter_less_iter", align 1
  %5 = ptrtoint i32* %1 to i64
  %6 = ptrtoint i32* %0 to i64
  %7 = sub i64 %5, %6
  %8 = icmp sgt i64 %7, 64
  br i1 %8, label %9, label %127

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds i32, i32* %0, i64 1
  br label %11

; <label>:11:                                     ; preds = %9, %123
  %12 = phi i64 [ %7, %9 ], [ %125, %123 ]
  %13 = phi i32* [ %1, %9 ], [ %110, %123 ]
  %14 = phi i64 [ %2, %9 ], [ %78, %123 ]
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %16, label %77

; <label>:16:                                     ; preds = %11
  %17 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_less_iter", %"struct.__gnu_cxx::__ops::_Iter_less_iter"* %4, i64 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %17)
  call void @_ZSt11__make_heapIPiN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_RT0_(i32* %0, i32* %13, %"struct.__gnu_cxx::__ops::_Iter_less_iter"* nonnull dereferenceable(1) %4)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %17)
  br label %18

; <label>:18:                                     ; preds = %73, %16
  %19 = phi i32* [ %13, %16 ], [ %20, %73 ]
  %20 = getelementptr inbounds i32, i32* %19, i64 -1
  %21 = load i32, i32* %20, align 4, !tbaa !3
  %22 = load i32, i32* %0, align 4, !tbaa !3
  store i32 %22, i32* %20, align 4, !tbaa !3
  %23 = ptrtoint i32* %20 to i64
  %24 = sub i64 %23, %6
  %25 = ashr exact i64 %24, 2
  %26 = add nsw i64 %25, -1
  %27 = sdiv i64 %26, 2
  %28 = icmp sgt i64 %24, 8
  br i1 %28, label %29, label %45

; <label>:29:                                     ; preds = %18
  br label %30

; <label>:30:                                     ; preds = %29, %30
  %31 = phi i64 [ %40, %30 ], [ 0, %29 ]
  %32 = shl i64 %31, 1
  %33 = add i64 %32, 2
  %34 = getelementptr inbounds i32, i32* %0, i64 %33
  %35 = or i64 %32, 1
  %36 = getelementptr inbounds i32, i32* %0, i64 %35
  %37 = load i32, i32* %34, align 4, !tbaa !3
  %38 = load i32, i32* %36, align 4, !tbaa !3
  %39 = icmp slt i32 %37, %38
  %40 = select i1 %39, i64 %35, i64 %33
  %41 = getelementptr inbounds i32, i32* %0, i64 %40
  %42 = load i32, i32* %41, align 4, !tbaa !3
  %43 = getelementptr inbounds i32, i32* %0, i64 %31
  store i32 %42, i32* %43, align 4, !tbaa !3
  %44 = icmp slt i64 %40, %27
  br i1 %44, label %30, label %45

; <label>:45:                                     ; preds = %30, %18
  %46 = phi i64 [ 0, %18 ], [ %40, %30 ]
  %47 = and i64 %24, 4
  %48 = icmp eq i64 %47, 0
  br i1 %48, label %49, label %59

; <label>:49:                                     ; preds = %45
  %50 = add nsw i64 %25, -2
  %51 = sdiv i64 %50, 2
  %52 = icmp eq i64 %46, %51
  br i1 %52, label %53, label %59

; <label>:53:                                     ; preds = %49
  %54 = shl i64 %46, 1
  %55 = or i64 %54, 1
  %56 = getelementptr inbounds i32, i32* %0, i64 %55
  %57 = load i32, i32* %56, align 4, !tbaa !3
  %58 = getelementptr inbounds i32, i32* %0, i64 %46
  store i32 %57, i32* %58, align 4, !tbaa !3
  br label %59

; <label>:59:                                     ; preds = %53, %49, %45
  %60 = phi i64 [ %55, %53 ], [ %46, %49 ], [ %46, %45 ]
  %61 = icmp sgt i64 %60, 0
  br i1 %61, label %62, label %73

; <label>:62:                                     ; preds = %59
  br label %63

; <label>:63:                                     ; preds = %62, %70
  %64 = phi i64 [ %66, %70 ], [ %60, %62 ]
  %65 = add nsw i64 %64, -1
  %66 = sdiv i64 %65, 2
  %67 = getelementptr inbounds i32, i32* %0, i64 %66
  %68 = load i32, i32* %67, align 4, !tbaa !3
  %69 = icmp slt i32 %68, %21
  br i1 %69, label %70, label %73

; <label>:70:                                     ; preds = %63
  %71 = getelementptr inbounds i32, i32* %0, i64 %64
  store i32 %68, i32* %71, align 4, !tbaa !3
  %72 = icmp sgt i64 %64, 2
  br i1 %72, label %63, label %73

; <label>:73:                                     ; preds = %70, %63, %59
  %74 = phi i64 [ %60, %59 ], [ %64, %63 ], [ %66, %70 ]
  %75 = getelementptr inbounds i32, i32* %0, i64 %74
  store i32 %21, i32* %75, align 4, !tbaa !3
  %76 = icmp sgt i64 %24, 4
  br i1 %76, label %18, label %127

; <label>:77:                                     ; preds = %11
  %78 = add nsw i64 %14, -1
  %79 = lshr i64 %12, 3
  %80 = getelementptr inbounds i32, i32* %0, i64 %79
  %81 = getelementptr inbounds i32, i32* %13, i64 -1
  %82 = load i32, i32* %10, align 4, !tbaa !3
  %83 = load i32, i32* %80, align 4, !tbaa !3
  %84 = icmp slt i32 %82, %83
  %85 = load i32, i32* %81, align 4, !tbaa !3
  br i1 %84, label %86, label %95

; <label>:86:                                     ; preds = %77
  %87 = icmp slt i32 %83, %85
  br i1 %87, label %88, label %90

; <label>:88:                                     ; preds = %86
  %89 = load i32, i32* %0, align 4, !tbaa !3
  store i32 %83, i32* %0, align 4, !tbaa !3
  store i32 %89, i32* %80, align 4, !tbaa !3
  br label %104

; <label>:90:                                     ; preds = %86
  %91 = icmp slt i32 %82, %85
  %92 = load i32, i32* %0, align 4, !tbaa !3
  br i1 %91, label %93, label %94

; <label>:93:                                     ; preds = %90
  store i32 %85, i32* %0, align 4, !tbaa !3
  store i32 %92, i32* %81, align 4, !tbaa !3
  br label %104

; <label>:94:                                     ; preds = %90
  store i32 %82, i32* %0, align 4, !tbaa !3
  store i32 %92, i32* %10, align 4, !tbaa !3
  br label %104

; <label>:95:                                     ; preds = %77
  %96 = icmp slt i32 %82, %85
  br i1 %96, label %97, label %99

; <label>:97:                                     ; preds = %95
  %98 = load i32, i32* %0, align 4, !tbaa !3
  store i32 %82, i32* %0, align 4, !tbaa !3
  store i32 %98, i32* %10, align 4, !tbaa !3
  br label %104

; <label>:99:                                     ; preds = %95
  %100 = icmp slt i32 %83, %85
  %101 = load i32, i32* %0, align 4, !tbaa !3
  br i1 %100, label %102, label %103

; <label>:102:                                    ; preds = %99
  store i32 %85, i32* %0, align 4, !tbaa !3
  store i32 %101, i32* %81, align 4, !tbaa !3
  br label %104

; <label>:103:                                    ; preds = %99
  store i32 %83, i32* %0, align 4, !tbaa !3
  store i32 %101, i32* %80, align 4, !tbaa !3
  br label %104

; <label>:104:                                    ; preds = %103, %102, %97, %94, %93, %88
  br label %105

; <label>:105:                                    ; preds = %104, %122
  %106 = phi i32* [ %117, %122 ], [ %13, %104 ]
  %107 = phi i32* [ %113, %122 ], [ %10, %104 ]
  %108 = load i32, i32* %0, align 4, !tbaa !3
  br label %109

; <label>:109:                                    ; preds = %109, %105
  %110 = phi i32* [ %107, %105 ], [ %113, %109 ]
  %111 = load i32, i32* %110, align 4, !tbaa !3
  %112 = icmp slt i32 %111, %108
  %113 = getelementptr inbounds i32, i32* %110, i64 1
  br i1 %112, label %109, label %114

; <label>:114:                                    ; preds = %109
  br label %115

; <label>:115:                                    ; preds = %114, %115
  %116 = phi i32* [ %117, %115 ], [ %106, %114 ]
  %117 = getelementptr inbounds i32, i32* %116, i64 -1
  %118 = load i32, i32* %117, align 4, !tbaa !3
  %119 = icmp slt i32 %108, %118
  br i1 %119, label %115, label %120

; <label>:120:                                    ; preds = %115
  %121 = icmp ult i32* %110, %117
  br i1 %121, label %122, label %123

; <label>:122:                                    ; preds = %120
  store i32 %118, i32* %110, align 4, !tbaa !3
  store i32 %111, i32* %117, align 4, !tbaa !3
  br label %105

; <label>:123:                                    ; preds = %120
  tail call void @_ZSt16__introsort_loopIPilN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_T1_(i32* %110, i32* %13, i64 %78)
  %124 = ptrtoint i32* %110 to i64
  %125 = sub i64 %124, %6
  %126 = icmp sgt i64 %125, 64
  br i1 %126, label %11, label %127

; <label>:127:                                    ; preds = %123, %73, %3
  ret void
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt22__final_insertion_sortIPiN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_T0_(i32*, i32*) local_unnamed_addr #6 comdat {
  %3 = ptrtoint i32* %0 to i64
  %4 = ptrtoint i32* %1 to i64
  %5 = sub i64 %4, %3
  %6 = icmp sgt i64 %5, 64
  br i1 %6, label %7, label %79

; <label>:7:                                      ; preds = %2
  %8 = bitcast i32* %0 to i8*
  %9 = getelementptr i32, i32* %0, i64 1
  %10 = bitcast i32* %9 to i8*
  %11 = getelementptr inbounds i32, i32* %0, i64 1
  %12 = load i32, i32* %11, align 4, !tbaa !3
  %13 = load i32, i32* %0, align 4, !tbaa !3
  %14 = icmp slt i32 %12, %13
  %15 = load i32, i32* %0, align 4
  br i1 %14, label %16, label %17

; <label>:16:                                     ; preds = %7
  store i32 %15, i32* %9, align 4
  br label %27

; <label>:17:                                     ; preds = %7
  %18 = icmp slt i32 %12, %15
  br i1 %18, label %19, label %27

; <label>:19:                                     ; preds = %17
  br label %20

; <label>:20:                                     ; preds = %19, %20
  %21 = phi i32 [ %25, %20 ], [ %15, %19 ]
  %22 = phi i32* [ %24, %20 ], [ %0, %19 ]
  %23 = phi i32* [ %22, %20 ], [ %11, %19 ]
  store i32 %21, i32* %23, align 4, !tbaa !3
  %24 = getelementptr inbounds i32, i32* %22, i64 -1
  %25 = load i32, i32* %24, align 4, !tbaa !3
  %26 = icmp slt i32 %12, %25
  br i1 %26, label %20, label %27

; <label>:27:                                     ; preds = %20, %17, %16
  %28 = phi i32* [ %0, %16 ], [ %11, %17 ], [ %22, %20 ]
  store i32 %12, i32* %28, align 4, !tbaa !3
  %29 = getelementptr inbounds i32, i32* %0, i64 2
  %30 = load i32, i32* %29, align 4, !tbaa !3
  %31 = load i32, i32* %0, align 4, !tbaa !3
  %32 = icmp slt i32 %30, %31
  br i1 %32, label %141, label %130

; <label>:33:                                     ; preds = %379
  %34 = getelementptr i32, i32* %1, i64 -17
  %35 = ptrtoint i32* %34 to i64
  %36 = sub i64 %35, %3
  %37 = and i64 %36, 4
  %38 = icmp eq i64 %37, 0
  br i1 %38, label %39, label %55

; <label>:39:                                     ; preds = %33
  %40 = load i32, i32* %381, align 4, !tbaa !3
  %41 = getelementptr inbounds i32, i32* %0, i64 15
  %42 = load i32, i32* %41, align 4, !tbaa !3
  %43 = icmp slt i32 %40, %42
  br i1 %43, label %44, label %52

; <label>:44:                                     ; preds = %39
  br label %45

; <label>:45:                                     ; preds = %45, %44
  %46 = phi i32 [ %50, %45 ], [ %42, %44 ]
  %47 = phi i32* [ %49, %45 ], [ %41, %44 ]
  %48 = phi i32* [ %47, %45 ], [ %381, %44 ]
  store i32 %46, i32* %48, align 4, !tbaa !3
  %49 = getelementptr inbounds i32, i32* %47, i64 -1
  %50 = load i32, i32* %49, align 4, !tbaa !3
  %51 = icmp slt i32 %40, %50
  br i1 %51, label %45, label %52

; <label>:52:                                     ; preds = %45, %39
  %53 = phi i32* [ %381, %39 ], [ %47, %45 ]
  store i32 %40, i32* %53, align 4, !tbaa !3
  %54 = getelementptr inbounds i32, i32* %0, i64 17
  br label %55

; <label>:55:                                     ; preds = %52, %33
  %56 = phi i32* [ %381, %33 ], [ %54, %52 ]
  %57 = icmp ult i64 %36, 4
  br i1 %57, label %117, label %58

; <label>:58:                                     ; preds = %55
  br label %59

; <label>:59:                                     ; preds = %126, %58
  %60 = phi i32* [ %56, %58 ], [ %128, %126 ]
  %61 = load i32, i32* %60, align 4, !tbaa !3
  %62 = getelementptr inbounds i32, i32* %60, i64 -1
  %63 = load i32, i32* %62, align 4, !tbaa !3
  %64 = icmp slt i32 %61, %63
  br i1 %64, label %65, label %73

; <label>:65:                                     ; preds = %59
  br label %66

; <label>:66:                                     ; preds = %65, %66
  %67 = phi i32 [ %71, %66 ], [ %63, %65 ]
  %68 = phi i32* [ %70, %66 ], [ %62, %65 ]
  %69 = phi i32* [ %68, %66 ], [ %60, %65 ]
  store i32 %67, i32* %69, align 4, !tbaa !3
  %70 = getelementptr inbounds i32, i32* %68, i64 -1
  %71 = load i32, i32* %70, align 4, !tbaa !3
  %72 = icmp slt i32 %61, %71
  br i1 %72, label %66, label %73

; <label>:73:                                     ; preds = %66, %59
  %74 = phi i32* [ %60, %59 ], [ %68, %66 ]
  store i32 %61, i32* %74, align 4, !tbaa !3
  %75 = getelementptr inbounds i32, i32* %60, i64 1
  %76 = load i32, i32* %75, align 4, !tbaa !3
  %77 = load i32, i32* %60, align 4, !tbaa !3
  %78 = icmp slt i32 %76, %77
  br i1 %78, label %118, label %126

; <label>:79:                                     ; preds = %2
  %80 = icmp eq i32* %0, %1
  br i1 %80, label %117, label %81

; <label>:81:                                     ; preds = %79
  %82 = getelementptr inbounds i32, i32* %0, i64 1
  %83 = icmp eq i32* %82, %1
  br i1 %83, label %117, label %84

; <label>:84:                                     ; preds = %81
  %85 = bitcast i32* %0 to i8*
  br label %86

; <label>:86:                                     ; preds = %113, %84
  %87 = phi i32* [ %82, %84 ], [ %115, %113 ]
  %88 = phi i32* [ %0, %84 ], [ %87, %113 ]
  %89 = load i32, i32* %87, align 4, !tbaa !3
  %90 = load i32, i32* %0, align 4, !tbaa !3
  %91 = icmp slt i32 %89, %90
  br i1 %91, label %92, label %102

; <label>:92:                                     ; preds = %86
  %93 = ptrtoint i32* %87 to i64
  %94 = sub i64 %93, %3
  %95 = icmp eq i64 %94, 0
  br i1 %95, label %113, label %96

; <label>:96:                                     ; preds = %92
  %97 = getelementptr inbounds i32, i32* %88, i64 2
  %98 = ashr exact i64 %94, 2
  %99 = sub nsw i64 0, %98
  %100 = getelementptr inbounds i32, i32* %97, i64 %99
  %101 = bitcast i32* %100 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %101, i8* nonnull %85, i64 %94, i32 4, i1 false) #2
  br label %113

; <label>:102:                                    ; preds = %86
  %103 = load i32, i32* %88, align 4, !tbaa !3
  %104 = icmp slt i32 %89, %103
  br i1 %104, label %105, label %113

; <label>:105:                                    ; preds = %102
  br label %106

; <label>:106:                                    ; preds = %105, %106
  %107 = phi i32 [ %111, %106 ], [ %103, %105 ]
  %108 = phi i32* [ %110, %106 ], [ %88, %105 ]
  %109 = phi i32* [ %108, %106 ], [ %87, %105 ]
  store i32 %107, i32* %109, align 4, !tbaa !3
  %110 = getelementptr inbounds i32, i32* %108, i64 -1
  %111 = load i32, i32* %110, align 4, !tbaa !3
  %112 = icmp slt i32 %89, %111
  br i1 %112, label %106, label %113

; <label>:113:                                    ; preds = %106, %102, %92, %96
  %114 = phi i32* [ %0, %96 ], [ %0, %92 ], [ %87, %102 ], [ %108, %106 ]
  store i32 %89, i32* %114, align 4, !tbaa !3
  %115 = getelementptr inbounds i32, i32* %87, i64 1
  %116 = icmp eq i32* %115, %1
  br i1 %116, label %117, label %86

; <label>:117:                                    ; preds = %113, %55, %126, %81, %79, %379
  ret void

; <label>:118:                                    ; preds = %73
  br label %119

; <label>:119:                                    ; preds = %119, %118
  %120 = phi i32 [ %124, %119 ], [ %77, %118 ]
  %121 = phi i32* [ %123, %119 ], [ %60, %118 ]
  %122 = phi i32* [ %121, %119 ], [ %75, %118 ]
  store i32 %120, i32* %122, align 4, !tbaa !3
  %123 = getelementptr inbounds i32, i32* %121, i64 -1
  %124 = load i32, i32* %123, align 4, !tbaa !3
  %125 = icmp slt i32 %76, %124
  br i1 %125, label %119, label %126

; <label>:126:                                    ; preds = %119, %73
  %127 = phi i32* [ %75, %73 ], [ %121, %119 ]
  store i32 %76, i32* %127, align 4, !tbaa !3
  %128 = getelementptr inbounds i32, i32* %60, i64 2
  %129 = icmp eq i32* %128, %1
  br i1 %129, label %117, label %59

; <label>:130:                                    ; preds = %27
  %131 = load i32, i32* %11, align 4, !tbaa !3
  %132 = icmp slt i32 %30, %131
  br i1 %132, label %133, label %145

; <label>:133:                                    ; preds = %130
  br label %134

; <label>:134:                                    ; preds = %134, %133
  %135 = phi i32 [ %139, %134 ], [ %131, %133 ]
  %136 = phi i32* [ %138, %134 ], [ %11, %133 ]
  %137 = phi i32* [ %136, %134 ], [ %29, %133 ]
  store i32 %135, i32* %137, align 4, !tbaa !3
  %138 = getelementptr inbounds i32, i32* %136, i64 -1
  %139 = load i32, i32* %138, align 4, !tbaa !3
  %140 = icmp slt i32 %30, %139
  br i1 %140, label %134, label %145

; <label>:141:                                    ; preds = %27
  %142 = bitcast i32* %0 to i64*
  %143 = bitcast i32* %9 to i64*
  %144 = load i64, i64* %142, align 4
  store i64 %144, i64* %143, align 4
  br label %145

; <label>:145:                                    ; preds = %134, %141, %130
  %146 = phi i32* [ %0, %141 ], [ %29, %130 ], [ %136, %134 ]
  store i32 %30, i32* %146, align 4, !tbaa !3
  %147 = getelementptr inbounds i32, i32* %0, i64 3
  %148 = load i32, i32* %147, align 4, !tbaa !3
  %149 = load i32, i32* %0, align 4, !tbaa !3
  %150 = icmp slt i32 %148, %149
  br i1 %150, label %162, label %151

; <label>:151:                                    ; preds = %145
  %152 = load i32, i32* %29, align 4, !tbaa !3
  %153 = icmp slt i32 %148, %152
  br i1 %153, label %154, label %163

; <label>:154:                                    ; preds = %151
  br label %155

; <label>:155:                                    ; preds = %155, %154
  %156 = phi i32 [ %160, %155 ], [ %152, %154 ]
  %157 = phi i32* [ %159, %155 ], [ %29, %154 ]
  %158 = phi i32* [ %157, %155 ], [ %147, %154 ]
  store i32 %156, i32* %158, align 4, !tbaa !3
  %159 = getelementptr inbounds i32, i32* %157, i64 -1
  %160 = load i32, i32* %159, align 4, !tbaa !3
  %161 = icmp slt i32 %148, %160
  br i1 %161, label %155, label %163

; <label>:162:                                    ; preds = %145
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 12, i32 4, i1 false) #2
  br label %163

; <label>:163:                                    ; preds = %155, %162, %151
  %164 = phi i32* [ %0, %162 ], [ %147, %151 ], [ %157, %155 ]
  store i32 %148, i32* %164, align 4, !tbaa !3
  %165 = getelementptr inbounds i32, i32* %0, i64 4
  %166 = load i32, i32* %165, align 4, !tbaa !3
  %167 = load i32, i32* %0, align 4, !tbaa !3
  %168 = icmp slt i32 %166, %167
  br i1 %168, label %180, label %169

; <label>:169:                                    ; preds = %163
  %170 = load i32, i32* %147, align 4, !tbaa !3
  %171 = icmp slt i32 %166, %170
  br i1 %171, label %172, label %181

; <label>:172:                                    ; preds = %169
  br label %173

; <label>:173:                                    ; preds = %173, %172
  %174 = phi i32 [ %178, %173 ], [ %170, %172 ]
  %175 = phi i32* [ %177, %173 ], [ %147, %172 ]
  %176 = phi i32* [ %175, %173 ], [ %165, %172 ]
  store i32 %174, i32* %176, align 4, !tbaa !3
  %177 = getelementptr inbounds i32, i32* %175, i64 -1
  %178 = load i32, i32* %177, align 4, !tbaa !3
  %179 = icmp slt i32 %166, %178
  br i1 %179, label %173, label %181

; <label>:180:                                    ; preds = %163
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 16, i32 4, i1 false) #2
  br label %181

; <label>:181:                                    ; preds = %173, %180, %169
  %182 = phi i32* [ %0, %180 ], [ %165, %169 ], [ %175, %173 ]
  store i32 %166, i32* %182, align 4, !tbaa !3
  %183 = getelementptr inbounds i32, i32* %0, i64 5
  %184 = load i32, i32* %183, align 4, !tbaa !3
  %185 = load i32, i32* %0, align 4, !tbaa !3
  %186 = icmp slt i32 %184, %185
  br i1 %186, label %198, label %187

; <label>:187:                                    ; preds = %181
  %188 = load i32, i32* %165, align 4, !tbaa !3
  %189 = icmp slt i32 %184, %188
  br i1 %189, label %190, label %199

; <label>:190:                                    ; preds = %187
  br label %191

; <label>:191:                                    ; preds = %191, %190
  %192 = phi i32 [ %196, %191 ], [ %188, %190 ]
  %193 = phi i32* [ %195, %191 ], [ %165, %190 ]
  %194 = phi i32* [ %193, %191 ], [ %183, %190 ]
  store i32 %192, i32* %194, align 4, !tbaa !3
  %195 = getelementptr inbounds i32, i32* %193, i64 -1
  %196 = load i32, i32* %195, align 4, !tbaa !3
  %197 = icmp slt i32 %184, %196
  br i1 %197, label %191, label %199

; <label>:198:                                    ; preds = %181
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 20, i32 4, i1 false) #2
  br label %199

; <label>:199:                                    ; preds = %191, %198, %187
  %200 = phi i32* [ %0, %198 ], [ %183, %187 ], [ %193, %191 ]
  store i32 %184, i32* %200, align 4, !tbaa !3
  %201 = getelementptr inbounds i32, i32* %0, i64 6
  %202 = load i32, i32* %201, align 4, !tbaa !3
  %203 = load i32, i32* %0, align 4, !tbaa !3
  %204 = icmp slt i32 %202, %203
  br i1 %204, label %216, label %205

; <label>:205:                                    ; preds = %199
  %206 = load i32, i32* %183, align 4, !tbaa !3
  %207 = icmp slt i32 %202, %206
  br i1 %207, label %208, label %217

; <label>:208:                                    ; preds = %205
  br label %209

; <label>:209:                                    ; preds = %209, %208
  %210 = phi i32 [ %214, %209 ], [ %206, %208 ]
  %211 = phi i32* [ %213, %209 ], [ %183, %208 ]
  %212 = phi i32* [ %211, %209 ], [ %201, %208 ]
  store i32 %210, i32* %212, align 4, !tbaa !3
  %213 = getelementptr inbounds i32, i32* %211, i64 -1
  %214 = load i32, i32* %213, align 4, !tbaa !3
  %215 = icmp slt i32 %202, %214
  br i1 %215, label %209, label %217

; <label>:216:                                    ; preds = %199
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 24, i32 4, i1 false) #2
  br label %217

; <label>:217:                                    ; preds = %209, %216, %205
  %218 = phi i32* [ %0, %216 ], [ %201, %205 ], [ %211, %209 ]
  store i32 %202, i32* %218, align 4, !tbaa !3
  %219 = getelementptr inbounds i32, i32* %0, i64 7
  %220 = load i32, i32* %219, align 4, !tbaa !3
  %221 = load i32, i32* %0, align 4, !tbaa !3
  %222 = icmp slt i32 %220, %221
  br i1 %222, label %234, label %223

; <label>:223:                                    ; preds = %217
  %224 = load i32, i32* %201, align 4, !tbaa !3
  %225 = icmp slt i32 %220, %224
  br i1 %225, label %226, label %235

; <label>:226:                                    ; preds = %223
  br label %227

; <label>:227:                                    ; preds = %227, %226
  %228 = phi i32 [ %232, %227 ], [ %224, %226 ]
  %229 = phi i32* [ %231, %227 ], [ %201, %226 ]
  %230 = phi i32* [ %229, %227 ], [ %219, %226 ]
  store i32 %228, i32* %230, align 4, !tbaa !3
  %231 = getelementptr inbounds i32, i32* %229, i64 -1
  %232 = load i32, i32* %231, align 4, !tbaa !3
  %233 = icmp slt i32 %220, %232
  br i1 %233, label %227, label %235

; <label>:234:                                    ; preds = %217
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 28, i32 4, i1 false) #2
  br label %235

; <label>:235:                                    ; preds = %227, %234, %223
  %236 = phi i32* [ %0, %234 ], [ %219, %223 ], [ %229, %227 ]
  store i32 %220, i32* %236, align 4, !tbaa !3
  %237 = getelementptr inbounds i32, i32* %0, i64 8
  %238 = load i32, i32* %237, align 4, !tbaa !3
  %239 = load i32, i32* %0, align 4, !tbaa !3
  %240 = icmp slt i32 %238, %239
  br i1 %240, label %252, label %241

; <label>:241:                                    ; preds = %235
  %242 = load i32, i32* %219, align 4, !tbaa !3
  %243 = icmp slt i32 %238, %242
  br i1 %243, label %244, label %253

; <label>:244:                                    ; preds = %241
  br label %245

; <label>:245:                                    ; preds = %245, %244
  %246 = phi i32 [ %250, %245 ], [ %242, %244 ]
  %247 = phi i32* [ %249, %245 ], [ %219, %244 ]
  %248 = phi i32* [ %247, %245 ], [ %237, %244 ]
  store i32 %246, i32* %248, align 4, !tbaa !3
  %249 = getelementptr inbounds i32, i32* %247, i64 -1
  %250 = load i32, i32* %249, align 4, !tbaa !3
  %251 = icmp slt i32 %238, %250
  br i1 %251, label %245, label %253

; <label>:252:                                    ; preds = %235
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 32, i32 4, i1 false) #2
  br label %253

; <label>:253:                                    ; preds = %245, %252, %241
  %254 = phi i32* [ %0, %252 ], [ %237, %241 ], [ %247, %245 ]
  store i32 %238, i32* %254, align 4, !tbaa !3
  %255 = getelementptr inbounds i32, i32* %0, i64 9
  %256 = load i32, i32* %255, align 4, !tbaa !3
  %257 = load i32, i32* %0, align 4, !tbaa !3
  %258 = icmp slt i32 %256, %257
  br i1 %258, label %270, label %259

; <label>:259:                                    ; preds = %253
  %260 = load i32, i32* %237, align 4, !tbaa !3
  %261 = icmp slt i32 %256, %260
  br i1 %261, label %262, label %271

; <label>:262:                                    ; preds = %259
  br label %263

; <label>:263:                                    ; preds = %263, %262
  %264 = phi i32 [ %268, %263 ], [ %260, %262 ]
  %265 = phi i32* [ %267, %263 ], [ %237, %262 ]
  %266 = phi i32* [ %265, %263 ], [ %255, %262 ]
  store i32 %264, i32* %266, align 4, !tbaa !3
  %267 = getelementptr inbounds i32, i32* %265, i64 -1
  %268 = load i32, i32* %267, align 4, !tbaa !3
  %269 = icmp slt i32 %256, %268
  br i1 %269, label %263, label %271

; <label>:270:                                    ; preds = %253
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 36, i32 4, i1 false) #2
  br label %271

; <label>:271:                                    ; preds = %263, %270, %259
  %272 = phi i32* [ %0, %270 ], [ %255, %259 ], [ %265, %263 ]
  store i32 %256, i32* %272, align 4, !tbaa !3
  %273 = getelementptr inbounds i32, i32* %0, i64 10
  %274 = load i32, i32* %273, align 4, !tbaa !3
  %275 = load i32, i32* %0, align 4, !tbaa !3
  %276 = icmp slt i32 %274, %275
  br i1 %276, label %288, label %277

; <label>:277:                                    ; preds = %271
  %278 = load i32, i32* %255, align 4, !tbaa !3
  %279 = icmp slt i32 %274, %278
  br i1 %279, label %280, label %289

; <label>:280:                                    ; preds = %277
  br label %281

; <label>:281:                                    ; preds = %281, %280
  %282 = phi i32 [ %286, %281 ], [ %278, %280 ]
  %283 = phi i32* [ %285, %281 ], [ %255, %280 ]
  %284 = phi i32* [ %283, %281 ], [ %273, %280 ]
  store i32 %282, i32* %284, align 4, !tbaa !3
  %285 = getelementptr inbounds i32, i32* %283, i64 -1
  %286 = load i32, i32* %285, align 4, !tbaa !3
  %287 = icmp slt i32 %274, %286
  br i1 %287, label %281, label %289

; <label>:288:                                    ; preds = %271
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 40, i32 4, i1 false) #2
  br label %289

; <label>:289:                                    ; preds = %281, %288, %277
  %290 = phi i32* [ %0, %288 ], [ %273, %277 ], [ %283, %281 ]
  store i32 %274, i32* %290, align 4, !tbaa !3
  %291 = getelementptr inbounds i32, i32* %0, i64 11
  %292 = load i32, i32* %291, align 4, !tbaa !3
  %293 = load i32, i32* %0, align 4, !tbaa !3
  %294 = icmp slt i32 %292, %293
  br i1 %294, label %306, label %295

; <label>:295:                                    ; preds = %289
  %296 = load i32, i32* %273, align 4, !tbaa !3
  %297 = icmp slt i32 %292, %296
  br i1 %297, label %298, label %307

; <label>:298:                                    ; preds = %295
  br label %299

; <label>:299:                                    ; preds = %299, %298
  %300 = phi i32 [ %304, %299 ], [ %296, %298 ]
  %301 = phi i32* [ %303, %299 ], [ %273, %298 ]
  %302 = phi i32* [ %301, %299 ], [ %291, %298 ]
  store i32 %300, i32* %302, align 4, !tbaa !3
  %303 = getelementptr inbounds i32, i32* %301, i64 -1
  %304 = load i32, i32* %303, align 4, !tbaa !3
  %305 = icmp slt i32 %292, %304
  br i1 %305, label %299, label %307

; <label>:306:                                    ; preds = %289
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 44, i32 4, i1 false) #2
  br label %307

; <label>:307:                                    ; preds = %299, %306, %295
  %308 = phi i32* [ %0, %306 ], [ %291, %295 ], [ %301, %299 ]
  store i32 %292, i32* %308, align 4, !tbaa !3
  %309 = getelementptr inbounds i32, i32* %0, i64 12
  %310 = load i32, i32* %309, align 4, !tbaa !3
  %311 = load i32, i32* %0, align 4, !tbaa !3
  %312 = icmp slt i32 %310, %311
  br i1 %312, label %324, label %313

; <label>:313:                                    ; preds = %307
  %314 = load i32, i32* %291, align 4, !tbaa !3
  %315 = icmp slt i32 %310, %314
  br i1 %315, label %316, label %325

; <label>:316:                                    ; preds = %313
  br label %317

; <label>:317:                                    ; preds = %317, %316
  %318 = phi i32 [ %322, %317 ], [ %314, %316 ]
  %319 = phi i32* [ %321, %317 ], [ %291, %316 ]
  %320 = phi i32* [ %319, %317 ], [ %309, %316 ]
  store i32 %318, i32* %320, align 4, !tbaa !3
  %321 = getelementptr inbounds i32, i32* %319, i64 -1
  %322 = load i32, i32* %321, align 4, !tbaa !3
  %323 = icmp slt i32 %310, %322
  br i1 %323, label %317, label %325

; <label>:324:                                    ; preds = %307
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 48, i32 4, i1 false) #2
  br label %325

; <label>:325:                                    ; preds = %317, %324, %313
  %326 = phi i32* [ %0, %324 ], [ %309, %313 ], [ %319, %317 ]
  store i32 %310, i32* %326, align 4, !tbaa !3
  %327 = getelementptr inbounds i32, i32* %0, i64 13
  %328 = load i32, i32* %327, align 4, !tbaa !3
  %329 = load i32, i32* %0, align 4, !tbaa !3
  %330 = icmp slt i32 %328, %329
  br i1 %330, label %342, label %331

; <label>:331:                                    ; preds = %325
  %332 = load i32, i32* %309, align 4, !tbaa !3
  %333 = icmp slt i32 %328, %332
  br i1 %333, label %334, label %343

; <label>:334:                                    ; preds = %331
  br label %335

; <label>:335:                                    ; preds = %335, %334
  %336 = phi i32 [ %340, %335 ], [ %332, %334 ]
  %337 = phi i32* [ %339, %335 ], [ %309, %334 ]
  %338 = phi i32* [ %337, %335 ], [ %327, %334 ]
  store i32 %336, i32* %338, align 4, !tbaa !3
  %339 = getelementptr inbounds i32, i32* %337, i64 -1
  %340 = load i32, i32* %339, align 4, !tbaa !3
  %341 = icmp slt i32 %328, %340
  br i1 %341, label %335, label %343

; <label>:342:                                    ; preds = %325
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 52, i32 4, i1 false) #2
  br label %343

; <label>:343:                                    ; preds = %335, %342, %331
  %344 = phi i32* [ %0, %342 ], [ %327, %331 ], [ %337, %335 ]
  store i32 %328, i32* %344, align 4, !tbaa !3
  %345 = getelementptr inbounds i32, i32* %0, i64 14
  %346 = load i32, i32* %345, align 4, !tbaa !3
  %347 = load i32, i32* %0, align 4, !tbaa !3
  %348 = icmp slt i32 %346, %347
  br i1 %348, label %360, label %349

; <label>:349:                                    ; preds = %343
  %350 = load i32, i32* %327, align 4, !tbaa !3
  %351 = icmp slt i32 %346, %350
  br i1 %351, label %352, label %361

; <label>:352:                                    ; preds = %349
  br label %353

; <label>:353:                                    ; preds = %353, %352
  %354 = phi i32 [ %358, %353 ], [ %350, %352 ]
  %355 = phi i32* [ %357, %353 ], [ %327, %352 ]
  %356 = phi i32* [ %355, %353 ], [ %345, %352 ]
  store i32 %354, i32* %356, align 4, !tbaa !3
  %357 = getelementptr inbounds i32, i32* %355, i64 -1
  %358 = load i32, i32* %357, align 4, !tbaa !3
  %359 = icmp slt i32 %346, %358
  br i1 %359, label %353, label %361

; <label>:360:                                    ; preds = %343
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 56, i32 4, i1 false) #2
  br label %361

; <label>:361:                                    ; preds = %353, %360, %349
  %362 = phi i32* [ %0, %360 ], [ %345, %349 ], [ %355, %353 ]
  store i32 %346, i32* %362, align 4, !tbaa !3
  %363 = getelementptr inbounds i32, i32* %0, i64 15
  %364 = load i32, i32* %363, align 4, !tbaa !3
  %365 = load i32, i32* %0, align 4, !tbaa !3
  %366 = icmp slt i32 %364, %365
  br i1 %366, label %378, label %367

; <label>:367:                                    ; preds = %361
  %368 = load i32, i32* %345, align 4, !tbaa !3
  %369 = icmp slt i32 %364, %368
  br i1 %369, label %370, label %379

; <label>:370:                                    ; preds = %367
  br label %371

; <label>:371:                                    ; preds = %371, %370
  %372 = phi i32 [ %376, %371 ], [ %368, %370 ]
  %373 = phi i32* [ %375, %371 ], [ %345, %370 ]
  %374 = phi i32* [ %373, %371 ], [ %363, %370 ]
  store i32 %372, i32* %374, align 4, !tbaa !3
  %375 = getelementptr inbounds i32, i32* %373, i64 -1
  %376 = load i32, i32* %375, align 4, !tbaa !3
  %377 = icmp slt i32 %364, %376
  br i1 %377, label %371, label %379

; <label>:378:                                    ; preds = %361
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 60, i32 4, i1 false) #2
  br label %379

; <label>:379:                                    ; preds = %371, %378, %367
  %380 = phi i32* [ %0, %378 ], [ %363, %367 ], [ %373, %371 ]
  store i32 %364, i32* %380, align 4, !tbaa !3
  %381 = getelementptr inbounds i32, i32* %0, i64 16
  %382 = icmp eq i32* %381, %1
  br i1 %382, label %117, label %33
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt11__make_heapIPiN9__gnu_cxx5__ops15_Iter_less_iterEEvT_S4_RT0_(i32*, i32*, %"struct.__gnu_cxx::__ops::_Iter_less_iter"* dereferenceable(1)) local_unnamed_addr #6 comdat {
  %4 = ptrtoint i32* %1 to i64
  %5 = ptrtoint i32* %0 to i64
  %6 = sub i64 %4, %5
  %7 = ashr exact i64 %6, 2
  %8 = icmp slt i64 %6, 8
  br i1 %8, label %106, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 4
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %17, label %16

; <label>:16:                                     ; preds = %9
  br label %67

; <label>:17:                                     ; preds = %9
  %18 = shl nsw i64 %11, 1
  %19 = or i64 %18, 1
  %20 = getelementptr inbounds i32, i32* %0, i64 %19
  %21 = getelementptr inbounds i32, i32* %0, i64 %11
  br label %22

; <label>:22:                                     ; preds = %62, %17
  %23 = phi i64 [ %11, %17 ], [ %66, %62 ]
  %24 = getelementptr inbounds i32, i32* %0, i64 %23
  %25 = load i32, i32* %24, align 4, !tbaa !3
  %26 = icmp sgt i64 %13, %23
  br i1 %26, label %27, label %43

; <label>:27:                                     ; preds = %22
  br label %28

; <label>:28:                                     ; preds = %27, %28
  %29 = phi i64 [ %38, %28 ], [ %23, %27 ]
  %30 = shl i64 %29, 1
  %31 = add i64 %30, 2
  %32 = getelementptr inbounds i32, i32* %0, i64 %31
  %33 = or i64 %30, 1
  %34 = getelementptr inbounds i32, i32* %0, i64 %33
  %35 = load i32, i32* %32, align 4, !tbaa !3
  %36 = load i32, i32* %34, align 4, !tbaa !3
  %37 = icmp slt i32 %35, %36
  %38 = select i1 %37, i64 %33, i64 %31
  %39 = getelementptr inbounds i32, i32* %0, i64 %38
  %40 = load i32, i32* %39, align 4, !tbaa !3
  %41 = getelementptr inbounds i32, i32* %0, i64 %29
  store i32 %40, i32* %41, align 4, !tbaa !3
  %42 = icmp slt i64 %38, %13
  br i1 %42, label %28, label %43

; <label>:43:                                     ; preds = %28, %22
  %44 = phi i64 [ %23, %22 ], [ %38, %28 ]
  %45 = icmp eq i64 %44, %11
  br i1 %45, label %46, label %48

; <label>:46:                                     ; preds = %43
  %47 = load i32, i32* %20, align 4, !tbaa !3
  store i32 %47, i32* %21, align 4, !tbaa !3
  br label %48

; <label>:48:                                     ; preds = %46, %43
  %49 = phi i64 [ %19, %46 ], [ %44, %43 ]
  %50 = icmp sgt i64 %49, %23
  br i1 %50, label %51, label %62

; <label>:51:                                     ; preds = %48
  br label %52

; <label>:52:                                     ; preds = %51, %59
  %53 = phi i64 [ %55, %59 ], [ %49, %51 ]
  %54 = add nsw i64 %53, -1
  %55 = sdiv i64 %54, 2
  %56 = getelementptr inbounds i32, i32* %0, i64 %55
  %57 = load i32, i32* %56, align 4, !tbaa !3
  %58 = icmp slt i32 %57, %25
  br i1 %58, label %59, label %62

; <label>:59:                                     ; preds = %52
  %60 = getelementptr inbounds i32, i32* %0, i64 %53
  store i32 %57, i32* %60, align 4, !tbaa !3
  %61 = icmp sgt i64 %55, %23
  br i1 %61, label %52, label %62

; <label>:62:                                     ; preds = %52, %59, %48
  %63 = phi i64 [ %49, %48 ], [ %55, %59 ], [ %53, %52 ]
  %64 = getelementptr inbounds i32, i32* %0, i64 %63
  store i32 %25, i32* %64, align 4, !tbaa !3
  %65 = icmp eq i64 %23, 0
  %66 = add nsw i64 %23, -1
  br i1 %65, label %106, label %22

; <label>:67:                                     ; preds = %16, %101
  %68 = phi i64 [ %105, %101 ], [ %11, %16 ]
  %69 = getelementptr inbounds i32, i32* %0, i64 %68
  %70 = load i32, i32* %69, align 4, !tbaa !3
  %71 = icmp sgt i64 %13, %68
  br i1 %71, label %72, label %101

; <label>:72:                                     ; preds = %67
  br label %73

; <label>:73:                                     ; preds = %72, %73
  %74 = phi i64 [ %83, %73 ], [ %68, %72 ]
  %75 = shl i64 %74, 1
  %76 = add i64 %75, 2
  %77 = getelementptr inbounds i32, i32* %0, i64 %76
  %78 = or i64 %75, 1
  %79 = getelementptr inbounds i32, i32* %0, i64 %78
  %80 = load i32, i32* %77, align 4, !tbaa !3
  %81 = load i32, i32* %79, align 4, !tbaa !3
  %82 = icmp slt i32 %80, %81
  %83 = select i1 %82, i64 %78, i64 %76
  %84 = getelementptr inbounds i32, i32* %0, i64 %83
  %85 = load i32, i32* %84, align 4, !tbaa !3
  %86 = getelementptr inbounds i32, i32* %0, i64 %74
  store i32 %85, i32* %86, align 4, !tbaa !3
  %87 = icmp slt i64 %83, %13
  br i1 %87, label %73, label %88

; <label>:88:                                     ; preds = %73
  %89 = icmp sgt i64 %83, %68
  br i1 %89, label %90, label %101

; <label>:90:                                     ; preds = %88
  br label %91

; <label>:91:                                     ; preds = %90, %98
  %92 = phi i64 [ %94, %98 ], [ %83, %90 ]
  %93 = add nsw i64 %92, -1
  %94 = sdiv i64 %93, 2
  %95 = getelementptr inbounds i32, i32* %0, i64 %94
  %96 = load i32, i32* %95, align 4, !tbaa !3
  %97 = icmp slt i32 %96, %70
  br i1 %97, label %98, label %101

; <label>:98:                                     ; preds = %91
  %99 = getelementptr inbounds i32, i32* %0, i64 %92
  store i32 %96, i32* %99, align 4, !tbaa !3
  %100 = icmp sgt i64 %94, %68
  br i1 %100, label %91, label %101

; <label>:101:                                    ; preds = %91, %98, %67, %88
  %102 = phi i64 [ %83, %88 ], [ %68, %67 ], [ %94, %98 ], [ %92, %91 ]
  %103 = getelementptr inbounds i32, i32* %0, i64 %102
  store i32 %70, i32* %103, align 4, !tbaa !3
  %104 = icmp eq i64 %68, 0
  %105 = add nsw i64 %68, -1
  br i1 %104, label %106, label %67

; <label>:106:                                    ; preds = %101, %62, %3
  ret void
}

; Function Attrs: nounwind readnone speculatable
declare i64 @llvm.ctlz.i64(i64, i1) #7

; Function Attrs: argmemonly nounwind
declare void @llvm.memmove.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #4

; Function Attrs: uwtable
define internal void @_GLOBAL__sub_I_test_sort.cpp() #6 section ".text.startup" {
  tail call void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"* nonnull @_ZStL8__ioinit)
  %1 = tail call i32 @__cxa_atexit(void (i8*)* bitcast (void (%"class.std::ios_base::Init"*)* @_ZNSt8ios_base4InitD1Ev to void (i8*)*), i8* getelementptr inbounds (%"class.std::ios_base::Init", %"class.std::ios_base::Init"* @_ZStL8__ioinit, i64 0, i32 0), i8* nonnull @__dso_handle) #2
  ret void
}

; Function Attrs: noreturn nounwind
declare void @llvm.trap() #8

attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }
attributes #3 = { norecurse noreturn uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { argmemonly nounwind }
attributes #5 = { inlinehint uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { nounwind readnone speculatable }
attributes #8 = { noreturn nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!2 = !{i64 0, i64 65}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C++ TBAA"}
