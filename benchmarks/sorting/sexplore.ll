; ModuleID = 'sexplore.cpp'
source_filename = "sexplore.cpp"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%"class.std::ios_base::Init" = type { i8 }
%"class.std::basic_ostream" = type { i32 (...)**, %"class.std::basic_ios" }
%"class.std::basic_ios" = type { %"class.std::ios_base", %"class.std::basic_ostream"*, i8, i8, %"class.std::basic_streambuf"*, %"class.std::ctype"*, %"class.std::num_put"*, %"class.std::num_get"* }
%"class.std::ios_base" = type { i32 (...)**, i64, i64, i32, i32, i32, %"struct.std::ios_base::_Callback_list"*, %"struct.std::ios_base::_Words", [8 x %"struct.std::ios_base::_Words"], i32, %"struct.std::ios_base::_Words"*, %"class.std::locale" }
%"struct.std::ios_base::_Callback_list" = type { %"struct.std::ios_base::_Callback_list"*, void (i32, %"class.std::ios_base"*, i32)*, i32, i32 }
%"struct.std::ios_base::_Words" = type { i8*, i64 }
%"class.std::locale" = type { %"class.std::locale::_Impl"* }
%"class.std::locale::_Impl" = type { i32, %"class.std::locale::facet"**, i64, %"class.std::locale::facet"**, i8** }
%"class.std::locale::facet" = type <{ i32 (...)**, i32, [4 x i8] }>
%"class.std::basic_streambuf" = type { i32 (...)**, i8*, i8*, i8*, i8*, i8*, i8*, %"class.std::locale" }
%"class.std::ctype" = type <{ %"class.std::locale::facet.base", [4 x i8], %struct.__locale_struct*, i8, [7 x i8], i32*, i32*, i16*, i8, [256 x i8], [256 x i8], i8, [6 x i8] }>
%"class.std::locale::facet.base" = type <{ i32 (...)**, i32 }>
%struct.__locale_struct = type { [13 x %struct.__locale_data*], i16*, i32*, i32*, [13 x i8*] }
%struct.__locale_data = type opaque
%"class.std::num_put" = type { %"class.std::locale::facet.base", [4 x i8] }
%"class.std::num_get" = type { %"class.std::locale::facet.base", [4 x i8] }
%"struct.std::chrono::time_point" = type { %"struct.std::chrono::duration" }
%"struct.std::chrono::duration" = type { i64 }
%"struct.__gnu_cxx::__ops::_Iter_comp_iter" = type { %"struct.std::less" }
%"struct.std::less" = type { i8 }
%"class.std::vector" = type { %"struct.std::_Vector_base" }
%"struct.std::_Vector_base" = type { %"struct.std::_Vector_base<unsigned long, std::allocator<unsigned long> >::_Vector_impl" }
%"struct.std::_Vector_base<unsigned long, std::allocator<unsigned long> >::_Vector_impl" = type { i64*, i64*, i64* }
%"class.std::__cxx11::basic_string" = type { %"struct.std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >::_Alloc_hider", i64, %union.anon }
%"struct.std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >::_Alloc_hider" = type { i8* }
%union.anon = type { i64, [8 x i8] }
%"class.std::basic_ifstream" = type { %"class.std::basic_istream.base", %"class.std::basic_filebuf", %"class.std::basic_ios" }
%"class.std::basic_istream.base" = type { i32 (...)**, i64 }
%"class.std::basic_filebuf" = type { %"class.std::basic_streambuf", %union.pthread_mutex_t, %"class.std::__basic_file", i32, %struct.__mbstate_t, %struct.__mbstate_t, %struct.__mbstate_t, i8*, i64, i8, i8, i8, i8, i8*, i8*, i8, %"class.std::codecvt"*, i8*, i64, i8*, i8* }
%union.pthread_mutex_t = type { %struct.__pthread_mutex_s }
%struct.__pthread_mutex_s = type { i32, i32, i32, i32, i32, i16, i16, %struct.__pthread_internal_list }
%struct.__pthread_internal_list = type { %struct.__pthread_internal_list*, %struct.__pthread_internal_list* }
%"class.std::__basic_file" = type <{ %struct._IO_FILE*, i8, [7 x i8] }>
%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }
%struct.__mbstate_t = type { i32, %union.anon.6 }
%union.anon.6 = type { i32 }
%"class.std::codecvt" = type { %"class.std::__codecvt_abstract_base.base", %struct.__locale_struct* }
%"class.std::__codecvt_abstract_base.base" = type { %"class.std::locale::facet.base" }
%"struct.std::error_code" = type { i32, %"class.std::_V2::error_category"* }
%"class.std::_V2::error_category" = type { i32 (...)** }
%"class.std::ios_base::failure" = type { %"class.std::system_error" }
%"class.std::system_error" = type { %"class.std::runtime_error", %"struct.std::error_code" }
%"class.std::runtime_error" = type { %"class.std::exception", %"struct.std::__cow_string" }
%"class.std::exception" = type { i32 (...)** }
%"struct.std::__cow_string" = type { %union.anon.7 }
%union.anon.7 = type { i8* }
%"class.std::basic_istream" = type { i32 (...)**, i64, %"class.std::basic_ios" }
%"struct.__gnu_cxx::__ops::_Iter_less_iter" = type { i8 }

$_Z19move_pivot_to_frontPmmm = comdat any

$_Z7shufflePmmmm = comdat any

$_ZN13Int_Generator6randomEm = comdat any

$_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE = comdat any

$_ZNSt6vectorImSaImEE9push_backERKm = comdat any

$_ZSt11__make_heapIPmN9__gnu_cxx5__ops15_Iter_comp_iterISt4lessImEEEEvT_S7_RT0_ = comdat any

$_ZN13Int_Generator10random_dupEmm = comdat any

$_ZN13Int_Generator10sorted_endEmm = comdat any

$_ZN13Int_Generator13sorted_middleEmm = comdat any

$_ZN13Int_Generator18reverse_sorted_endEmm = comdat any

$_ZN13Int_Generator21reverse_sorted_middleEmm = comdat any

$_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib = comdat any

$_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_comp_iterISt4lessImEEEEvT_SC_RT0_ = comdat any

$_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_ = comdat any

$_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_ = comdat any

$_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_RT0_ = comdat any

$_ZNSt6vectorImSaImEEaSERKS1_ = comdat any

$_ZNSt6vectorImSaImEE17_M_default_appendEm = comdat any

@_ZStL8__ioinit = internal global %"class.std::ios_base::Init" zeroinitializer, align 1
@__dso_handle = external hidden global i8
@_ZSt4cout = external global %"class.std::basic_ostream", align 8
@.str = private unnamed_addr constant [6 x i8] c"Hello\00", align 1
@.str.1 = private unnamed_addr constant [8 x i8] c"pdqsort\00", align 1
@.str.2 = private unnamed_addr constant [8 x i8] c"psort  \00", align 1
@.str.3 = private unnamed_addr constant [10 x i8] c"input.bin\00", align 1
@.str.5 = private unnamed_addr constant [16 x i8] c"vector::reserve\00", align 1
@.str.6 = private unnamed_addr constant [22 x i8] c"could not open file \0A\00", align 1
@_ZTINSt8ios_base7failureB5cxx11E = external constant i8*
@.str.7 = private unnamed_addr constant [30 x i8] c"incorrect lenght of the file\0A\00", align 1
@.str.10 = private unnamed_addr constant [20 x i8] c"*** NOT SORTED *** \00", align 1
@.str.11 = private unnamed_addr constant [2 x i8] c":\00", align 1
@.str.12 = private unnamed_addr constant [2 x i8] c" \00", align 1
@.str.13 = private unnamed_addr constant [26 x i8] c"vector::_M_default_append\00", align 1
@llvm.global_ctors = appending global [1 x { i32, void ()*, i8* }] [{ i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_sexplore.cpp, i8* null }]

declare void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"*) unnamed_addr #0

; Function Attrs: nounwind
declare void @_ZNSt8ios_base4InitD1Ev(%"class.std::ios_base::Init"*) unnamed_addr #1

; Function Attrs: nounwind
declare i32 @__cxa_atexit(void (i8*)*, i8*, i8*) local_unnamed_addr #2

; Function Attrs: nounwind uwtable
define i64 @_ZN5boost4sort6common3nowEv() local_unnamed_addr #3 {
  %1 = tail call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  ret i64 %1
}

; Function Attrs: nounwind
declare i64 @_ZNSt6chrono3_V212steady_clock3nowEv() local_unnamed_addr #1

; Function Attrs: readonly uwtable
define double @_ZN5boost4sort6common13subtract_timeERKNSt6chrono10time_pointINS2_3_V212steady_clockENS2_8durationIlSt5ratioILl1ELl1000000000EEEEEESC_(%"struct.std::chrono::time_point"* nocapture readonly dereferenceable(8), %"struct.std::chrono::time_point"* nocapture readonly dereferenceable(8)) local_unnamed_addr #4 {
  %3 = getelementptr inbounds %"struct.std::chrono::time_point", %"struct.std::chrono::time_point"* %0, i64 0, i32 0, i32 0
  %4 = load i64, i64* %3, align 8
  %5 = getelementptr inbounds %"struct.std::chrono::time_point", %"struct.std::chrono::time_point"* %1, i64 0, i32 0, i32 0
  %6 = load i64, i64* %5, align 8
  %7 = sub nsw i64 %4, %6
  %8 = sitofp i64 %7 to double
  %9 = fdiv double %8, 1.000000e+09
  ret double %9
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #5

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #5

; Function Attrs: norecurse nounwind uwtable
define i64* @_Z20xunguarded_partitionPmmm(i64*, i64, i64) local_unnamed_addr #6 {
  br label %4

; <label>:4:                                      ; preds = %24, %3
  %5 = phi i64 [ 0, %3 ], [ %12, %24 ]
  %6 = phi i64 [ %1, %3 ], [ %17, %24 ]
  br label %7

; <label>:7:                                      ; preds = %7, %4
  %8 = phi i64 [ %5, %4 ], [ %12, %7 ]
  %9 = getelementptr inbounds i64, i64* %0, i64 %8
  %10 = load i64, i64* %9, align 8, !tbaa !2
  %11 = icmp ult i64 %10, %2
  %12 = add i64 %8, 1
  br i1 %11, label %7, label %13

; <label>:13:                                     ; preds = %7
  %14 = getelementptr inbounds i64, i64* %0, i64 %8
  br label %15

; <label>:15:                                     ; preds = %15, %13
  %16 = phi i64 [ %6, %13 ], [ %17, %15 ]
  %17 = add i64 %16, -1
  %18 = getelementptr inbounds i64, i64* %0, i64 %17
  %19 = load i64, i64* %18, align 8, !tbaa !2
  %20 = icmp ugt i64 %19, %2
  br i1 %20, label %15, label %21

; <label>:21:                                     ; preds = %15
  %22 = icmp ult i64 %8, %17
  br i1 %22, label %24, label %23

; <label>:23:                                     ; preds = %21
  ret i64* %14

; <label>:24:                                     ; preds = %21
  %25 = getelementptr inbounds i64, i64* %0, i64 %17
  store i64 %19, i64* %14, align 8, !tbaa !2
  store i64 %10, i64* %25, align 8, !tbaa !2
  br label %4
}

; Function Attrs: uwtable
define void @_Z10xintrosortPmm(i64*, i64) local_unnamed_addr #7 {
  %3 = icmp ugt i64 %1, 16
  br i1 %3, label %4, label %68

; <label>:4:                                      ; preds = %2
  br label %5

; <label>:5:                                      ; preds = %4, %59
  %6 = phi i64 [ %66, %59 ], [ %1, %4 ]
  %7 = phi i64* [ %48, %59 ], [ %0, %4 ]
  %8 = lshr i64 %6, 1
  %9 = getelementptr inbounds i64, i64* %7, i64 %8
  %10 = getelementptr inbounds i64, i64* %7, i64 1
  %11 = getelementptr inbounds i64, i64* %7, i64 %6
  %12 = getelementptr inbounds i64, i64* %11, i64 -1
  %13 = load i64, i64* %10, align 8, !tbaa !2
  %14 = load i64, i64* %9, align 8, !tbaa !2
  %15 = icmp ult i64 %13, %14
  %16 = load i64, i64* %12, align 8, !tbaa !2
  br i1 %15, label %17, label %26

; <label>:17:                                     ; preds = %5
  %18 = icmp ult i64 %14, %16
  br i1 %18, label %19, label %21

; <label>:19:                                     ; preds = %17
  %20 = load i64, i64* %7, align 8, !tbaa !2
  store i64 %14, i64* %7, align 8, !tbaa !2
  store i64 %20, i64* %9, align 8, !tbaa !2
  br label %35

; <label>:21:                                     ; preds = %17
  %22 = icmp ult i64 %13, %16
  %23 = load i64, i64* %7, align 8, !tbaa !2
  br i1 %22, label %24, label %25

; <label>:24:                                     ; preds = %21
  store i64 %16, i64* %7, align 8, !tbaa !2
  store i64 %23, i64* %12, align 8, !tbaa !2
  br label %35

; <label>:25:                                     ; preds = %21
  store i64 %13, i64* %7, align 8, !tbaa !2
  store i64 %23, i64* %10, align 8, !tbaa !2
  br label %35

; <label>:26:                                     ; preds = %5
  %27 = icmp ult i64 %13, %16
  br i1 %27, label %28, label %30

; <label>:28:                                     ; preds = %26
  %29 = load i64, i64* %7, align 8, !tbaa !2
  store i64 %13, i64* %7, align 8, !tbaa !2
  store i64 %29, i64* %10, align 8, !tbaa !2
  br label %35

; <label>:30:                                     ; preds = %26
  %31 = icmp ult i64 %14, %16
  %32 = load i64, i64* %7, align 8, !tbaa !2
  br i1 %31, label %33, label %34

; <label>:33:                                     ; preds = %30
  store i64 %16, i64* %7, align 8, !tbaa !2
  store i64 %32, i64* %12, align 8, !tbaa !2
  br label %35

; <label>:34:                                     ; preds = %30
  store i64 %14, i64* %7, align 8, !tbaa !2
  store i64 %32, i64* %9, align 8, !tbaa !2
  br label %35

; <label>:35:                                     ; preds = %34, %33, %28, %25, %24, %19
  %36 = add i64 %6, -1
  %37 = load i64, i64* %7, align 8, !tbaa !2
  br label %38

; <label>:38:                                     ; preds = %57, %35
  %39 = phi i64 [ 0, %35 ], [ %46, %57 ]
  %40 = phi i64 [ %36, %35 ], [ %51, %57 ]
  br label %41

; <label>:41:                                     ; preds = %41, %38
  %42 = phi i64 [ %39, %38 ], [ %46, %41 ]
  %43 = getelementptr inbounds i64, i64* %10, i64 %42
  %44 = load i64, i64* %43, align 8, !tbaa !2
  %45 = icmp ult i64 %44, %37
  %46 = add i64 %42, 1
  br i1 %45, label %41, label %47

; <label>:47:                                     ; preds = %41
  %48 = getelementptr inbounds i64, i64* %10, i64 %42
  br label %49

; <label>:49:                                     ; preds = %49, %47
  %50 = phi i64 [ %40, %47 ], [ %51, %49 ]
  %51 = add i64 %50, -1
  %52 = getelementptr inbounds i64, i64* %7, i64 %50
  %53 = load i64, i64* %52, align 8, !tbaa !2
  %54 = icmp ugt i64 %53, %37
  br i1 %54, label %49, label %55

; <label>:55:                                     ; preds = %49
  %56 = icmp ult i64 %42, %51
  br i1 %56, label %57, label %59

; <label>:57:                                     ; preds = %55
  %58 = getelementptr inbounds i64, i64* %7, i64 %50
  store i64 %53, i64* %48, align 8, !tbaa !2
  store i64 %44, i64* %58, align 8, !tbaa !2
  br label %38

; <label>:59:                                     ; preds = %55
  %60 = ptrtoint i64* %48 to i64
  %61 = ptrtoint i64* %7 to i64
  %62 = sub i64 %60, %61
  %63 = ashr exact i64 %62, 3
  tail call void @_Z10xintrosortPmm(i64* nonnull %7, i64 %63)
  %64 = ptrtoint i64* %11 to i64
  %65 = sub i64 %64, %60
  %66 = ashr exact i64 %65, 3
  %67 = icmp ugt i64 %66, 16
  br i1 %67, label %5, label %68

; <label>:68:                                     ; preds = %59, %2
  %69 = phi i64* [ %0, %2 ], [ %48, %59 ]
  %70 = phi i64 [ %1, %2 ], [ %66, %59 ]
  %71 = getelementptr inbounds i64, i64* %69, i64 %70
  %72 = icmp ult i64 %70, 2
  br i1 %72, label %108, label %73

; <label>:73:                                     ; preds = %68
  %74 = getelementptr inbounds i64, i64* %69, i64 1
  %75 = ptrtoint i64* %69 to i64
  %76 = bitcast i64* %69 to i8*
  br label %77

; <label>:77:                                     ; preds = %104, %73
  %78 = phi i64* [ %74, %73 ], [ %106, %104 ]
  %79 = phi i64* [ %69, %73 ], [ %78, %104 ]
  %80 = load i64, i64* %78, align 8, !tbaa !2
  %81 = load i64, i64* %69, align 8, !tbaa !2
  %82 = icmp ult i64 %80, %81
  br i1 %82, label %83, label %93

; <label>:83:                                     ; preds = %77
  %84 = ptrtoint i64* %78 to i64
  %85 = sub i64 %84, %75
  %86 = icmp eq i64 %85, 0
  br i1 %86, label %104, label %87

; <label>:87:                                     ; preds = %83
  %88 = getelementptr inbounds i64, i64* %79, i64 2
  %89 = ashr exact i64 %85, 3
  %90 = sub nsw i64 0, %89
  %91 = getelementptr inbounds i64, i64* %88, i64 %90
  %92 = bitcast i64* %91 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %92, i8* nonnull %76, i64 %85, i32 8, i1 false) #2
  br label %104

; <label>:93:                                     ; preds = %77
  %94 = load i64, i64* %79, align 8, !tbaa !2
  %95 = icmp ult i64 %80, %94
  br i1 %95, label %96, label %104

; <label>:96:                                     ; preds = %93
  br label %97

; <label>:97:                                     ; preds = %96, %97
  %98 = phi i64 [ %102, %97 ], [ %94, %96 ]
  %99 = phi i64* [ %101, %97 ], [ %79, %96 ]
  %100 = phi i64* [ %99, %97 ], [ %78, %96 ]
  store i64 %98, i64* %100, align 8, !tbaa !2
  %101 = getelementptr inbounds i64, i64* %99, i64 -1
  %102 = load i64, i64* %101, align 8, !tbaa !2
  %103 = icmp ult i64 %80, %102
  br i1 %103, label %97, label %104

; <label>:104:                                    ; preds = %97, %93, %83, %87
  %105 = phi i64* [ %69, %87 ], [ %69, %83 ], [ %78, %93 ], [ %99, %97 ]
  store i64 %80, i64* %105, align 8, !tbaa !2
  %106 = getelementptr inbounds i64, i64* %78, i64 1
  %107 = icmp eq i64* %106, %71
  br i1 %107, label %108, label %77

; <label>:108:                                    ; preds = %104, %68
  ret void
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i32, i1) #5

; Function Attrs: uwtable
define void @_Z11pdqsort_recPmmmib(i64*, i64, i64, i32, i1 zeroext) local_unnamed_addr #7 {
  %6 = alloca %"struct.__gnu_cxx::__ops::_Iter_comp_iter", align 1
  %7 = sub i64 %1, %2
  %8 = icmp ult i64 %7, 24
  br i1 %8, label %9, label %125

; <label>:9:                                      ; preds = %5
  %10 = getelementptr inbounds i64, i64* %0, i64 %1
  %11 = getelementptr inbounds i64, i64* %0, i64 %2
  %12 = icmp eq i64 %1, %2
  br i1 %4, label %13, label %72

; <label>:13:                                     ; preds = %9
  br i1 %12, label %423, label %14

; <label>:14:                                     ; preds = %13
  %15 = getelementptr inbounds i64, i64* %10, i64 1
  %16 = icmp eq i64* %15, %11
  br i1 %16, label %423, label %17

; <label>:17:                                     ; preds = %14
  %18 = shl i64 %2, 3
  %19 = add i64 %18, -16
  %20 = shl i64 %1, 3
  %21 = sub i64 %19, %20
  %22 = and i64 %21, 8
  %23 = icmp eq i64 %22, 0
  br i1 %23, label %24, label %43

; <label>:24:                                     ; preds = %17
  %25 = load i64, i64* %15, align 8, !tbaa !2
  %26 = load i64, i64* %10, align 8, !tbaa !2
  %27 = icmp ult i64 %25, %26
  br i1 %27, label %28, label %41

; <label>:28:                                     ; preds = %24
  br label %29

; <label>:29:                                     ; preds = %35, %28
  %30 = phi i64 [ %37, %35 ], [ %26, %28 ]
  %31 = phi i64* [ %33, %35 ], [ %15, %28 ]
  %32 = phi i64* [ %36, %35 ], [ %10, %28 ]
  %33 = getelementptr inbounds i64, i64* %31, i64 -1
  store i64 %30, i64* %31, align 8, !tbaa !2
  %34 = icmp eq i64* %33, %10
  br i1 %34, label %39, label %35

; <label>:35:                                     ; preds = %29
  %36 = getelementptr inbounds i64, i64* %32, i64 -1
  %37 = load i64, i64* %36, align 8, !tbaa !2
  %38 = icmp ult i64 %25, %37
  br i1 %38, label %29, label %39

; <label>:39:                                     ; preds = %35, %29
  %40 = phi i64* [ %10, %29 ], [ %33, %35 ]
  store i64 %25, i64* %40, align 8, !tbaa !2
  br label %41

; <label>:41:                                     ; preds = %39, %24
  %42 = getelementptr inbounds i64, i64* %15, i64 1
  br label %43

; <label>:43:                                     ; preds = %41, %17
  %44 = phi i64* [ %15, %17 ], [ %42, %41 ]
  %45 = phi i64* [ %10, %17 ], [ %15, %41 ]
  %46 = icmp eq i64 %21, 0
  br i1 %46, label %423, label %47

; <label>:47:                                     ; preds = %43
  br label %48

; <label>:48:                                     ; preds = %437, %47
  %49 = phi i64* [ %44, %47 ], [ %438, %437 ]
  %50 = phi i64* [ %45, %47 ], [ %68, %437 ]
  %51 = load i64, i64* %49, align 8, !tbaa !2
  %52 = load i64, i64* %50, align 8, !tbaa !2
  %53 = icmp ult i64 %51, %52
  br i1 %53, label %54, label %67

; <label>:54:                                     ; preds = %48
  br label %55

; <label>:55:                                     ; preds = %54, %61
  %56 = phi i64 [ %63, %61 ], [ %52, %54 ]
  %57 = phi i64* [ %59, %61 ], [ %49, %54 ]
  %58 = phi i64* [ %62, %61 ], [ %50, %54 ]
  %59 = getelementptr inbounds i64, i64* %57, i64 -1
  store i64 %56, i64* %57, align 8, !tbaa !2
  %60 = icmp eq i64* %59, %10
  br i1 %60, label %65, label %61

; <label>:61:                                     ; preds = %55
  %62 = getelementptr inbounds i64, i64* %58, i64 -1
  %63 = load i64, i64* %62, align 8, !tbaa !2
  %64 = icmp ult i64 %51, %63
  br i1 %64, label %55, label %65

; <label>:65:                                     ; preds = %61, %55
  %66 = phi i64* [ %10, %55 ], [ %59, %61 ]
  store i64 %51, i64* %66, align 8, !tbaa !2
  br label %67

; <label>:67:                                     ; preds = %65, %48
  %68 = getelementptr inbounds i64, i64* %49, i64 1
  %69 = load i64, i64* %68, align 8, !tbaa !2
  %70 = load i64, i64* %49, align 8, !tbaa !2
  %71 = icmp ult i64 %69, %70
  br i1 %71, label %424, label %437

; <label>:72:                                     ; preds = %9
  br i1 %12, label %423, label %73

; <label>:73:                                     ; preds = %72
  %74 = getelementptr inbounds i64, i64* %10, i64 1
  %75 = icmp eq i64* %74, %11
  br i1 %75, label %423, label %76

; <label>:76:                                     ; preds = %73
  %77 = shl i64 %2, 3
  %78 = add i64 %77, -16
  %79 = shl i64 %1, 3
  %80 = sub i64 %78, %79
  %81 = and i64 %80, 8
  %82 = icmp eq i64 %81, 0
  br i1 %82, label %83, label %99

; <label>:83:                                     ; preds = %76
  %84 = load i64, i64* %74, align 8, !tbaa !2
  %85 = load i64, i64* %10, align 8, !tbaa !2
  %86 = icmp ult i64 %84, %85
  br i1 %86, label %87, label %97

; <label>:87:                                     ; preds = %83
  br label %88

; <label>:88:                                     ; preds = %88, %87
  %89 = phi i64 [ %94, %88 ], [ %85, %87 ]
  %90 = phi i64* [ %92, %88 ], [ %74, %87 ]
  %91 = phi i64* [ %93, %88 ], [ %10, %87 ]
  %92 = getelementptr inbounds i64, i64* %90, i64 -1
  store i64 %89, i64* %90, align 8, !tbaa !2
  %93 = getelementptr inbounds i64, i64* %91, i64 -1
  %94 = load i64, i64* %93, align 8, !tbaa !2
  %95 = icmp ult i64 %84, %94
  br i1 %95, label %88, label %96

; <label>:96:                                     ; preds = %88
  store i64 %84, i64* %92, align 8, !tbaa !2
  br label %97

; <label>:97:                                     ; preds = %96, %83
  %98 = getelementptr inbounds i64, i64* %74, i64 1
  br label %99

; <label>:99:                                     ; preds = %97, %76
  %100 = phi i64* [ %74, %76 ], [ %98, %97 ]
  %101 = phi i64* [ %10, %76 ], [ %74, %97 ]
  %102 = icmp eq i64 %80, 0
  br i1 %102, label %423, label %103

; <label>:103:                                    ; preds = %99
  br label %104

; <label>:104:                                    ; preds = %450, %103
  %105 = phi i64* [ %100, %103 ], [ %451, %450 ]
  %106 = phi i64* [ %101, %103 ], [ %121, %450 ]
  %107 = load i64, i64* %105, align 8, !tbaa !2
  %108 = load i64, i64* %106, align 8, !tbaa !2
  %109 = icmp ult i64 %107, %108
  br i1 %109, label %110, label %120

; <label>:110:                                    ; preds = %104
  br label %111

; <label>:111:                                    ; preds = %110, %111
  %112 = phi i64 [ %117, %111 ], [ %108, %110 ]
  %113 = phi i64* [ %115, %111 ], [ %105, %110 ]
  %114 = phi i64* [ %116, %111 ], [ %106, %110 ]
  %115 = getelementptr inbounds i64, i64* %113, i64 -1
  store i64 %112, i64* %113, align 8, !tbaa !2
  %116 = getelementptr inbounds i64, i64* %114, i64 -1
  %117 = load i64, i64* %116, align 8, !tbaa !2
  %118 = icmp ult i64 %107, %117
  br i1 %118, label %111, label %119

; <label>:119:                                    ; preds = %111
  store i64 %107, i64* %115, align 8, !tbaa !2
  br label %120

; <label>:120:                                    ; preds = %119, %104
  %121 = getelementptr inbounds i64, i64* %105, i64 1
  %122 = load i64, i64* %121, align 8, !tbaa !2
  %123 = load i64, i64* %105, align 8, !tbaa !2
  %124 = icmp ult i64 %122, %123
  br i1 %124, label %440, label %450

; <label>:125:                                    ; preds = %5
  tail call void @_Z19move_pivot_to_frontPmmm(i64* %0, i64 %1, i64 %2)
  br i1 %4, label %126, label %129

; <label>:126:                                    ; preds = %125
  %127 = getelementptr inbounds i64, i64* %0, i64 %1
  %128 = load i64, i64* %127, align 8, !tbaa !2
  br label %192

; <label>:129:                                    ; preds = %125
  %130 = add i64 %1, -1
  %131 = getelementptr inbounds i64, i64* %0, i64 %130
  %132 = getelementptr inbounds i64, i64* %0, i64 %1
  %133 = load i64, i64* %131, align 8, !tbaa !2
  %134 = load i64, i64* %132, align 8, !tbaa !2
  %135 = icmp ult i64 %133, %134
  br i1 %135, label %192, label %136

; <label>:136:                                    ; preds = %129
  %137 = getelementptr inbounds i64, i64* %0, i64 %2
  br label %138

; <label>:138:                                    ; preds = %138, %136
  %139 = phi i64* [ %137, %136 ], [ %140, %138 ]
  %140 = getelementptr inbounds i64, i64* %139, i64 -1
  %141 = load i64, i64* %140, align 8, !tbaa !2
  %142 = icmp ult i64 %134, %141
  br i1 %142, label %138, label %143

; <label>:143:                                    ; preds = %138
  %144 = icmp eq i64* %139, %137
  br i1 %144, label %146, label %145

; <label>:145:                                    ; preds = %143
  br label %156

; <label>:146:                                    ; preds = %143
  %147 = icmp ugt i64* %140, %132
  br i1 %147, label %148, label %161

; <label>:148:                                    ; preds = %146
  br label %149

; <label>:149:                                    ; preds = %148, %149
  %150 = phi i64* [ %151, %149 ], [ %132, %148 ]
  %151 = getelementptr inbounds i64, i64* %150, i64 1
  %152 = load i64, i64* %151, align 8, !tbaa !2
  %153 = icmp uge i64 %134, %152
  %154 = icmp ult i64* %151, %140
  %155 = and i1 %153, %154
  br i1 %155, label %149, label %161

; <label>:156:                                    ; preds = %145, %156
  %157 = phi i64* [ %158, %156 ], [ %132, %145 ]
  %158 = getelementptr inbounds i64, i64* %157, i64 1
  %159 = load i64, i64* %158, align 8, !tbaa !2
  %160 = icmp ult i64 %134, %159
  br i1 %160, label %161, label %156

; <label>:161:                                    ; preds = %156, %149, %146
  %162 = phi i64 [ %134, %146 ], [ %152, %149 ], [ %159, %156 ]
  %163 = phi i64* [ %132, %146 ], [ %151, %149 ], [ %158, %156 ]
  %164 = icmp ult i64* %163, %140
  br i1 %164, label %165, label %184

; <label>:165:                                    ; preds = %161
  br label %166

; <label>:166:                                    ; preds = %165, %182
  %167 = phi i64 [ %174, %182 ], [ %141, %165 ]
  %168 = phi i64 [ %180, %182 ], [ %162, %165 ]
  %169 = phi i64* [ %179, %182 ], [ %163, %165 ]
  %170 = phi i64* [ %173, %182 ], [ %140, %165 ]
  store i64 %167, i64* %169, align 8, !tbaa !2
  store i64 %168, i64* %170, align 8, !tbaa !2
  br label %171

; <label>:171:                                    ; preds = %171, %166
  %172 = phi i64* [ %170, %166 ], [ %173, %171 ]
  %173 = getelementptr inbounds i64, i64* %172, i64 -1
  %174 = load i64, i64* %173, align 8, !tbaa !2
  %175 = icmp ult i64 %134, %174
  br i1 %175, label %171, label %176

; <label>:176:                                    ; preds = %171
  br label %177

; <label>:177:                                    ; preds = %176, %177
  %178 = phi i64* [ %179, %177 ], [ %169, %176 ]
  %179 = getelementptr inbounds i64, i64* %178, i64 1
  %180 = load i64, i64* %179, align 8, !tbaa !2
  %181 = icmp ult i64 %134, %180
  br i1 %181, label %182, label %177

; <label>:182:                                    ; preds = %177
  %183 = icmp ult i64* %179, %173
  br i1 %183, label %166, label %184

; <label>:184:                                    ; preds = %182, %161
  %185 = phi i64 [ %141, %161 ], [ %174, %182 ]
  %186 = phi i64* [ %140, %161 ], [ %173, %182 ]
  store i64 %185, i64* %132, align 8, !tbaa !2
  store i64 %134, i64* %186, align 8, !tbaa !2
  %187 = getelementptr inbounds i64, i64* %186, i64 1
  %188 = ptrtoint i64* %187 to i64
  %189 = ptrtoint i64* %0 to i64
  %190 = sub i64 %188, %189
  %191 = ashr exact i64 %190, 3
  tail call void @_Z11pdqsort_recPmmmib(i64* %0, i64 %191, i64 %2, i32 %3, i1 zeroext false)
  br label %423

; <label>:192:                                    ; preds = %126, %129
  %193 = phi i64* [ %127, %126 ], [ %132, %129 ]
  %194 = phi i64 [ %128, %126 ], [ %134, %129 ]
  %195 = getelementptr inbounds i64, i64* %0, i64 %1
  br label %196

; <label>:196:                                    ; preds = %196, %192
  %197 = phi i64 [ 0, %192 ], [ %198, %196 ]
  %198 = add nuw nsw i64 %197, 1
  %199 = getelementptr inbounds i64, i64* %195, i64 %198
  %200 = load i64, i64* %199, align 8, !tbaa !2
  %201 = icmp ult i64 %200, %194
  br i1 %201, label %196, label %202

; <label>:202:                                    ; preds = %196
  %203 = getelementptr inbounds i64, i64* %195, i64 %198
  %204 = getelementptr inbounds i64, i64* %0, i64 %2
  %205 = icmp eq i64 %197, 0
  br i1 %205, label %207, label %206

; <label>:206:                                    ; preds = %202
  br label %217

; <label>:207:                                    ; preds = %202
  %208 = icmp ult i64* %203, %204
  br i1 %208, label %209, label %222

; <label>:209:                                    ; preds = %207
  br label %210

; <label>:210:                                    ; preds = %209, %210
  %211 = phi i64* [ %212, %210 ], [ %204, %209 ]
  %212 = getelementptr inbounds i64, i64* %211, i64 -1
  %213 = load i64, i64* %212, align 8, !tbaa !2
  %214 = icmp uge i64 %213, %194
  %215 = icmp ult i64* %203, %212
  %216 = and i1 %214, %215
  br i1 %216, label %210, label %222

; <label>:217:                                    ; preds = %206, %217
  %218 = phi i64* [ %219, %217 ], [ %204, %206 ]
  %219 = getelementptr inbounds i64, i64* %218, i64 -1
  %220 = load i64, i64* %219, align 8, !tbaa !2
  %221 = icmp ult i64 %220, %194
  br i1 %221, label %222, label %217

; <label>:222:                                    ; preds = %217, %210, %207
  %223 = phi i64* [ %204, %207 ], [ %212, %210 ], [ %219, %217 ]
  %224 = icmp ult i64* %203, %223
  br i1 %224, label %225, label %250

; <label>:225:                                    ; preds = %222
  %226 = load i64, i64* %223, align 8, !tbaa !2
  %227 = getelementptr inbounds i64, i64* %0, i64 %1
  %228 = getelementptr inbounds i64, i64* %0, i64 %1
  br label %229

; <label>:229:                                    ; preds = %248, %225
  %230 = phi i64 [ %226, %225 ], [ %246, %248 ]
  %231 = phi i64 [ %200, %225 ], [ %239, %248 ]
  %232 = phi i64* [ %223, %225 ], [ %245, %248 ]
  %233 = phi i64 [ %198, %225 ], [ %237, %248 ]
  %234 = getelementptr inbounds i64, i64* %227, i64 %233
  store i64 %230, i64* %234, align 8, !tbaa !2
  store i64 %231, i64* %232, align 8, !tbaa !2
  br label %235

; <label>:235:                                    ; preds = %235, %229
  %236 = phi i64 [ %233, %229 ], [ %237, %235 ]
  %237 = add nsw i64 %236, 1
  %238 = getelementptr inbounds i64, i64* %228, i64 %237
  %239 = load i64, i64* %238, align 8, !tbaa !2
  %240 = icmp ult i64 %239, %194
  br i1 %240, label %235, label %241

; <label>:241:                                    ; preds = %235
  %242 = getelementptr inbounds i64, i64* %228, i64 %237
  br label %243

; <label>:243:                                    ; preds = %243, %241
  %244 = phi i64* [ %232, %241 ], [ %245, %243 ]
  %245 = getelementptr inbounds i64, i64* %244, i64 -1
  %246 = load i64, i64* %245, align 8, !tbaa !2
  %247 = icmp ult i64 %246, %194
  br i1 %247, label %248, label %243

; <label>:248:                                    ; preds = %243
  %249 = icmp ult i64* %242, %245
  br i1 %249, label %229, label %250

; <label>:250:                                    ; preds = %248, %222
  %251 = phi i64 [ %197, %222 ], [ %236, %248 ]
  %252 = getelementptr inbounds i64, i64* %0, i64 %1
  %253 = getelementptr inbounds i64, i64* %252, i64 %251
  %254 = load i64, i64* %253, align 8, !tbaa !2
  store i64 %254, i64* %193, align 8, !tbaa !2
  store i64 %194, i64* %253, align 8, !tbaa !2
  %255 = ptrtoint i64* %253 to i64
  %256 = ptrtoint i64* %0 to i64
  %257 = sub i64 %255, %256
  %258 = ashr exact i64 %257, 3
  %259 = tail call zeroext i1 @_Z7shufflePmmmm(i64* %0, i64 %1, i64 %2, i64 %258)
  br i1 %259, label %260, label %338

; <label>:260:                                    ; preds = %250
  %261 = add nsw i32 %3, -1
  %262 = icmp eq i32 %261, 0
  br i1 %262, label %263, label %338

; <label>:263:                                    ; preds = %260
  %264 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_comp_iter", %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* %6, i64 0, i32 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %264) #2
  call void @_ZSt11__make_heapIPmN9__gnu_cxx5__ops15_Iter_comp_iterISt4lessImEEEEvT_S7_RT0_(i64* nonnull %193, i64* nonnull %204, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* nonnull dereferenceable(1) %6)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %264) #2
  %265 = ptrtoint i64* %204 to i64
  %266 = ptrtoint i64* %193 to i64
  %267 = sub i64 %265, %266
  %268 = icmp sgt i64 %267, 8
  br i1 %268, label %269, label %423

; <label>:269:                                    ; preds = %263
  %270 = getelementptr inbounds i64, i64* %0, i64 %1
  %271 = getelementptr inbounds i64, i64* %0, i64 %1
  %272 = getelementptr inbounds i64, i64* %0, i64 %1
  %273 = getelementptr inbounds i64, i64* %0, i64 %1
  %274 = getelementptr inbounds i64, i64* %0, i64 %1
  %275 = getelementptr inbounds i64, i64* %0, i64 %1
  %276 = getelementptr inbounds i64, i64* %0, i64 %1
  %277 = getelementptr inbounds i64, i64* %0, i64 %1
  %278 = getelementptr inbounds i64, i64* %0, i64 %1
  br label %279

; <label>:279:                                    ; preds = %334, %269
  %280 = phi i64* [ %204, %269 ], [ %281, %334 ]
  %281 = getelementptr inbounds i64, i64* %280, i64 -1
  %282 = load i64, i64* %281, align 8, !tbaa !2
  %283 = load i64, i64* %193, align 8, !tbaa !2
  store i64 %283, i64* %281, align 8, !tbaa !2
  %284 = ptrtoint i64* %281 to i64
  %285 = sub i64 %284, %266
  %286 = ashr exact i64 %285, 3
  %287 = add nsw i64 %286, -1
  %288 = sdiv i64 %287, 2
  %289 = icmp sgt i64 %285, 16
  br i1 %289, label %290, label %306

; <label>:290:                                    ; preds = %279
  br label %291

; <label>:291:                                    ; preds = %290, %291
  %292 = phi i64 [ %301, %291 ], [ 0, %290 ]
  %293 = shl i64 %292, 1
  %294 = add i64 %293, 2
  %295 = getelementptr inbounds i64, i64* %273, i64 %294
  %296 = or i64 %293, 1
  %297 = getelementptr inbounds i64, i64* %272, i64 %296
  %298 = load i64, i64* %295, align 8, !tbaa !2
  %299 = load i64, i64* %297, align 8, !tbaa !2
  %300 = icmp ult i64 %298, %299
  %301 = select i1 %300, i64 %296, i64 %294
  %302 = getelementptr inbounds i64, i64* %271, i64 %301
  %303 = load i64, i64* %302, align 8, !tbaa !2
  %304 = getelementptr inbounds i64, i64* %270, i64 %292
  store i64 %303, i64* %304, align 8, !tbaa !2
  %305 = icmp slt i64 %301, %288
  br i1 %305, label %291, label %306

; <label>:306:                                    ; preds = %291, %279
  %307 = phi i64 [ 0, %279 ], [ %301, %291 ]
  %308 = and i64 %285, 8
  %309 = icmp eq i64 %308, 0
  br i1 %309, label %310, label %320

; <label>:310:                                    ; preds = %306
  %311 = add nsw i64 %286, -2
  %312 = sdiv i64 %311, 2
  %313 = icmp eq i64 %307, %312
  br i1 %313, label %314, label %320

; <label>:314:                                    ; preds = %310
  %315 = shl i64 %307, 1
  %316 = or i64 %315, 1
  %317 = getelementptr inbounds i64, i64* %275, i64 %316
  %318 = load i64, i64* %317, align 8, !tbaa !2
  %319 = getelementptr inbounds i64, i64* %274, i64 %307
  store i64 %318, i64* %319, align 8, !tbaa !2
  br label %320

; <label>:320:                                    ; preds = %314, %310, %306
  %321 = phi i64 [ %316, %314 ], [ %307, %310 ], [ %307, %306 ]
  %322 = icmp sgt i64 %321, 0
  br i1 %322, label %323, label %334

; <label>:323:                                    ; preds = %320
  br label %324

; <label>:324:                                    ; preds = %323, %331
  %325 = phi i64 [ %327, %331 ], [ %321, %323 ]
  %326 = add nsw i64 %325, -1
  %327 = sdiv i64 %326, 2
  %328 = getelementptr inbounds i64, i64* %277, i64 %327
  %329 = load i64, i64* %328, align 8, !tbaa !2
  %330 = icmp ult i64 %329, %282
  br i1 %330, label %331, label %334

; <label>:331:                                    ; preds = %324
  %332 = getelementptr inbounds i64, i64* %276, i64 %325
  store i64 %329, i64* %332, align 8, !tbaa !2
  %333 = icmp sgt i64 %325, 2
  br i1 %333, label %324, label %334

; <label>:334:                                    ; preds = %331, %324, %320
  %335 = phi i64 [ %321, %320 ], [ %325, %324 ], [ %327, %331 ]
  %336 = getelementptr inbounds i64, i64* %278, i64 %335
  store i64 %282, i64* %336, align 8, !tbaa !2
  %337 = icmp sgt i64 %285, 8
  br i1 %337, label %279, label %423

; <label>:338:                                    ; preds = %260, %250
  %339 = phi i32 [ %261, %260 ], [ %3, %250 ]
  br i1 %224, label %421, label %340

; <label>:340:                                    ; preds = %338
  %341 = icmp ult i64 %251, 2
  br i1 %341, label %377, label %342

; <label>:342:                                    ; preds = %340
  %343 = getelementptr inbounds i64, i64* %0, i64 %1
  %344 = getelementptr inbounds i64, i64* %343, i64 1
  br label %345

; <label>:345:                                    ; preds = %373, %342
  %346 = phi i64* [ %344, %342 ], [ %375, %373 ]
  %347 = phi i64* [ %193, %342 ], [ %346, %373 ]
  %348 = phi i32 [ 0, %342 ], [ %374, %373 ]
  %349 = icmp sgt i32 %348, 8
  br i1 %349, label %421, label %350

; <label>:350:                                    ; preds = %345
  %351 = load i64, i64* %346, align 8, !tbaa !2
  %352 = load i64, i64* %347, align 8, !tbaa !2
  %353 = icmp ult i64 %351, %352
  br i1 %353, label %354, label %373

; <label>:354:                                    ; preds = %350
  br label %355

; <label>:355:                                    ; preds = %354, %361
  %356 = phi i64 [ %363, %361 ], [ %352, %354 ]
  %357 = phi i64* [ %359, %361 ], [ %346, %354 ]
  %358 = phi i64* [ %362, %361 ], [ %347, %354 ]
  %359 = getelementptr inbounds i64, i64* %357, i64 -1
  store i64 %356, i64* %357, align 8, !tbaa !2
  %360 = icmp eq i64* %359, %193
  br i1 %360, label %365, label %361

; <label>:361:                                    ; preds = %355
  %362 = getelementptr inbounds i64, i64* %358, i64 -1
  %363 = load i64, i64* %362, align 8, !tbaa !2
  %364 = icmp ult i64 %351, %363
  br i1 %364, label %355, label %365

; <label>:365:                                    ; preds = %361, %355
  %366 = phi i64* [ %193, %355 ], [ %359, %361 ]
  store i64 %351, i64* %366, align 8, !tbaa !2
  %367 = ptrtoint i64* %346 to i64
  %368 = ptrtoint i64* %366 to i64
  %369 = sub i64 %367, %368
  %370 = lshr exact i64 %369, 3
  %371 = trunc i64 %370 to i32
  %372 = add i32 %348, %371
  br label %373

; <label>:373:                                    ; preds = %365, %350
  %374 = phi i32 [ %372, %365 ], [ %348, %350 ]
  %375 = getelementptr inbounds i64, i64* %346, i64 1
  %376 = icmp eq i64* %375, %253
  br i1 %376, label %377, label %345

; <label>:377:                                    ; preds = %373, %340
  %378 = getelementptr inbounds i64, i64* %253, i64 1
  %379 = icmp eq i64* %378, %204
  %380 = getelementptr inbounds i64, i64* %253, i64 2
  %381 = icmp eq i64* %380, %204
  %382 = or i1 %379, %381
  br i1 %382, label %423, label %383

; <label>:383:                                    ; preds = %377
  br label %384

; <label>:384:                                    ; preds = %383, %416
  %385 = phi i64 [ %418, %416 ], [ 2, %383 ]
  %386 = phi i64* [ %388, %416 ], [ %378, %383 ]
  %387 = phi i32 [ %417, %416 ], [ 0, %383 ]
  %388 = getelementptr inbounds i64, i64* %253, i64 %385
  %389 = icmp sgt i32 %387, 8
  br i1 %389, label %421, label %390

; <label>:390:                                    ; preds = %384
  %391 = load i64, i64* %388, align 8, !tbaa !2
  %392 = load i64, i64* %386, align 8, !tbaa !2
  %393 = icmp ult i64 %391, %392
  br i1 %393, label %394, label %416

; <label>:394:                                    ; preds = %390
  br label %395

; <label>:395:                                    ; preds = %394, %402
  %396 = phi i64 [ %404, %402 ], [ %392, %394 ]
  %397 = phi i64 [ %400, %402 ], [ %385, %394 ]
  %398 = phi i64* [ %403, %402 ], [ %386, %394 ]
  %399 = getelementptr inbounds i64, i64* %253, i64 %397
  %400 = add nsw i64 %397, -1
  store i64 %396, i64* %399, align 8, !tbaa !2
  %401 = icmp eq i64 %400, 1
  br i1 %401, label %408, label %402

; <label>:402:                                    ; preds = %395
  %403 = getelementptr inbounds i64, i64* %398, i64 -1
  %404 = load i64, i64* %403, align 8, !tbaa !2
  %405 = icmp ult i64 %391, %404
  br i1 %405, label %395, label %406

; <label>:406:                                    ; preds = %402
  %407 = getelementptr inbounds i64, i64* %253, i64 %400
  br label %408

; <label>:408:                                    ; preds = %395, %406
  %409 = phi i64* [ %407, %406 ], [ %378, %395 ]
  store i64 %391, i64* %409, align 8, !tbaa !2
  %410 = ptrtoint i64* %388 to i64
  %411 = ptrtoint i64* %409 to i64
  %412 = sub i64 %410, %411
  %413 = lshr exact i64 %412, 3
  %414 = trunc i64 %413 to i32
  %415 = add i32 %387, %414
  br label %416

; <label>:416:                                    ; preds = %408, %390
  %417 = phi i32 [ %415, %408 ], [ %387, %390 ]
  %418 = add nuw nsw i64 %385, 1
  %419 = getelementptr inbounds i64, i64* %253, i64 %418
  %420 = icmp eq i64* %419, %204
  br i1 %420, label %423, label %384

; <label>:421:                                    ; preds = %345, %384, %338
  tail call void @_Z11pdqsort_recPmmmib(i64* %0, i64 %1, i64 %258, i32 %339, i1 zeroext %4)
  %422 = add nsw i64 %258, 1
  tail call void @_Z11pdqsort_recPmmmib(i64* %0, i64 %422, i64 %2, i32 %339, i1 zeroext false)
  br label %423

; <label>:423:                                    ; preds = %416, %334, %99, %450, %43, %437, %377, %263, %73, %72, %14, %13, %184, %421
  ret void

; <label>:424:                                    ; preds = %67
  br label %425

; <label>:425:                                    ; preds = %431, %424
  %426 = phi i64 [ %433, %431 ], [ %70, %424 ]
  %427 = phi i64* [ %429, %431 ], [ %68, %424 ]
  %428 = phi i64* [ %432, %431 ], [ %49, %424 ]
  %429 = getelementptr inbounds i64, i64* %427, i64 -1
  store i64 %426, i64* %427, align 8, !tbaa !2
  %430 = icmp eq i64* %429, %10
  br i1 %430, label %435, label %431

; <label>:431:                                    ; preds = %425
  %432 = getelementptr inbounds i64, i64* %428, i64 -1
  %433 = load i64, i64* %432, align 8, !tbaa !2
  %434 = icmp ult i64 %69, %433
  br i1 %434, label %425, label %435

; <label>:435:                                    ; preds = %431, %425
  %436 = phi i64* [ %10, %425 ], [ %429, %431 ]
  store i64 %69, i64* %436, align 8, !tbaa !2
  br label %437

; <label>:437:                                    ; preds = %435, %67
  %438 = getelementptr inbounds i64, i64* %49, i64 2
  %439 = icmp eq i64* %438, %11
  br i1 %439, label %423, label %48

; <label>:440:                                    ; preds = %120
  br label %441

; <label>:441:                                    ; preds = %441, %440
  %442 = phi i64 [ %447, %441 ], [ %123, %440 ]
  %443 = phi i64* [ %445, %441 ], [ %121, %440 ]
  %444 = phi i64* [ %446, %441 ], [ %105, %440 ]
  %445 = getelementptr inbounds i64, i64* %443, i64 -1
  store i64 %442, i64* %443, align 8, !tbaa !2
  %446 = getelementptr inbounds i64, i64* %444, i64 -1
  %447 = load i64, i64* %446, align 8, !tbaa !2
  %448 = icmp ult i64 %122, %447
  br i1 %448, label %441, label %449

; <label>:449:                                    ; preds = %441
  store i64 %122, i64* %445, align 8, !tbaa !2
  br label %450

; <label>:450:                                    ; preds = %449, %120
  %451 = getelementptr inbounds i64, i64* %105, i64 2
  %452 = icmp eq i64* %451, %11
  br i1 %452, label %423, label %104
}

; Function Attrs: inlinehint norecurse uwtable
define linkonce_odr void @_Z19move_pivot_to_frontPmmm(i64*, i64, i64) local_unnamed_addr #8 comdat {
  %4 = sub i64 %2, %1
  %5 = lshr i64 %4, 1
  %6 = icmp ugt i64 %4, 128
  %7 = add i64 %5, %1
  %8 = add i64 %2, -1
  br i1 %6, label %9, label %90

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds i64, i64* %0, i64 %7
  %11 = load i64, i64* %10, align 8, !tbaa !2
  %12 = getelementptr inbounds i64, i64* %0, i64 %1
  %13 = load i64, i64* %12, align 8, !tbaa !2
  %14 = icmp ult i64 %11, %13
  br i1 %14, label %15, label %16

; <label>:15:                                     ; preds = %9
  store i64 %11, i64* %12, align 8, !tbaa !2
  store i64 %13, i64* %10, align 8, !tbaa !2
  br label %16

; <label>:16:                                     ; preds = %15, %9
  %17 = phi i64 [ %11, %9 ], [ %13, %15 ]
  %18 = getelementptr inbounds i64, i64* %0, i64 %8
  %19 = load i64, i64* %18, align 8, !tbaa !2
  %20 = icmp ult i64 %19, %17
  br i1 %20, label %21, label %23

; <label>:21:                                     ; preds = %16
  store i64 %19, i64* %10, align 8, !tbaa !2
  store i64 %17, i64* %18, align 8, !tbaa !2
  %22 = load i64, i64* %10, align 8, !tbaa !2
  br label %23

; <label>:23:                                     ; preds = %21, %16
  %24 = phi i64 [ %17, %16 ], [ %22, %21 ]
  %25 = load i64, i64* %12, align 8, !tbaa !2
  %26 = icmp ult i64 %24, %25
  br i1 %26, label %27, label %28

; <label>:27:                                     ; preds = %23
  store i64 %24, i64* %12, align 8, !tbaa !2
  store i64 %25, i64* %10, align 8, !tbaa !2
  br label %28

; <label>:28:                                     ; preds = %23, %27
  %29 = add i64 %1, 1
  %30 = add i64 %7, -1
  %31 = add i64 %2, -2
  %32 = getelementptr inbounds i64, i64* %0, i64 %30
  %33 = load i64, i64* %32, align 8, !tbaa !2
  %34 = getelementptr inbounds i64, i64* %0, i64 %29
  %35 = load i64, i64* %34, align 8, !tbaa !2
  %36 = icmp ult i64 %33, %35
  br i1 %36, label %37, label %38

; <label>:37:                                     ; preds = %28
  store i64 %33, i64* %34, align 8, !tbaa !2
  store i64 %35, i64* %32, align 8, !tbaa !2
  br label %38

; <label>:38:                                     ; preds = %37, %28
  %39 = phi i64 [ %33, %28 ], [ %35, %37 ]
  %40 = getelementptr inbounds i64, i64* %0, i64 %31
  %41 = load i64, i64* %40, align 8, !tbaa !2
  %42 = icmp ult i64 %41, %39
  br i1 %42, label %43, label %45

; <label>:43:                                     ; preds = %38
  store i64 %41, i64* %32, align 8, !tbaa !2
  store i64 %39, i64* %40, align 8, !tbaa !2
  %44 = load i64, i64* %32, align 8, !tbaa !2
  br label %45

; <label>:45:                                     ; preds = %43, %38
  %46 = phi i64 [ %39, %38 ], [ %44, %43 ]
  %47 = load i64, i64* %34, align 8, !tbaa !2
  %48 = icmp ult i64 %46, %47
  br i1 %48, label %49, label %50

; <label>:49:                                     ; preds = %45
  store i64 %46, i64* %34, align 8, !tbaa !2
  store i64 %47, i64* %32, align 8, !tbaa !2
  br label %50

; <label>:50:                                     ; preds = %45, %49
  %51 = add i64 %1, 2
  %52 = add i64 %7, 1
  %53 = add i64 %2, -3
  %54 = getelementptr inbounds i64, i64* %0, i64 %52
  %55 = load i64, i64* %54, align 8, !tbaa !2
  %56 = getelementptr inbounds i64, i64* %0, i64 %51
  %57 = load i64, i64* %56, align 8, !tbaa !2
  %58 = icmp ult i64 %55, %57
  br i1 %58, label %59, label %60

; <label>:59:                                     ; preds = %50
  store i64 %55, i64* %56, align 8, !tbaa !2
  store i64 %57, i64* %54, align 8, !tbaa !2
  br label %60

; <label>:60:                                     ; preds = %59, %50
  %61 = phi i64 [ %55, %50 ], [ %57, %59 ]
  %62 = getelementptr inbounds i64, i64* %0, i64 %53
  %63 = load i64, i64* %62, align 8, !tbaa !2
  %64 = icmp ult i64 %63, %61
  br i1 %64, label %65, label %67

; <label>:65:                                     ; preds = %60
  store i64 %63, i64* %54, align 8, !tbaa !2
  store i64 %61, i64* %62, align 8, !tbaa !2
  %66 = load i64, i64* %54, align 8, !tbaa !2
  br label %67

; <label>:67:                                     ; preds = %65, %60
  %68 = phi i64 [ %61, %60 ], [ %66, %65 ]
  %69 = load i64, i64* %56, align 8, !tbaa !2
  %70 = icmp ult i64 %68, %69
  br i1 %70, label %71, label %72

; <label>:71:                                     ; preds = %67
  store i64 %68, i64* %56, align 8, !tbaa !2
  store i64 %69, i64* %54, align 8, !tbaa !2
  br label %72

; <label>:72:                                     ; preds = %67, %71
  %73 = phi i64 [ %68, %67 ], [ %69, %71 ]
  %74 = load i64, i64* %10, align 8, !tbaa !2
  %75 = load i64, i64* %32, align 8, !tbaa !2
  %76 = icmp ult i64 %74, %75
  br i1 %76, label %77, label %78

; <label>:77:                                     ; preds = %72
  store i64 %74, i64* %32, align 8, !tbaa !2
  store i64 %75, i64* %10, align 8, !tbaa !2
  br label %78

; <label>:78:                                     ; preds = %77, %72
  %79 = phi i64 [ %75, %72 ], [ %74, %77 ]
  %80 = phi i64 [ %74, %72 ], [ %75, %77 ]
  %81 = icmp ult i64 %73, %80
  br i1 %81, label %82, label %83

; <label>:82:                                     ; preds = %78
  store i64 %73, i64* %10, align 8, !tbaa !2
  store i64 %80, i64* %54, align 8, !tbaa !2
  br label %83

; <label>:83:                                     ; preds = %82, %78
  %84 = phi i64 [ %80, %78 ], [ %73, %82 ]
  %85 = icmp ult i64 %84, %79
  br i1 %85, label %86, label %87

; <label>:86:                                     ; preds = %83
  store i64 %84, i64* %32, align 8, !tbaa !2
  store i64 %79, i64* %10, align 8, !tbaa !2
  br label %87

; <label>:87:                                     ; preds = %83, %86
  %88 = phi i64 [ %84, %83 ], [ %79, %86 ]
  %89 = load i64, i64* %12, align 8, !tbaa !2
  store i64 %88, i64* %12, align 8, !tbaa !2
  store i64 %89, i64* %10, align 8, !tbaa !2
  br label %109

; <label>:90:                                     ; preds = %3
  %91 = getelementptr inbounds i64, i64* %0, i64 %1
  %92 = load i64, i64* %91, align 8, !tbaa !2
  %93 = getelementptr inbounds i64, i64* %0, i64 %7
  %94 = load i64, i64* %93, align 8, !tbaa !2
  %95 = icmp ult i64 %92, %94
  br i1 %95, label %96, label %97

; <label>:96:                                     ; preds = %90
  store i64 %92, i64* %93, align 8, !tbaa !2
  store i64 %94, i64* %91, align 8, !tbaa !2
  br label %97

; <label>:97:                                     ; preds = %96, %90
  %98 = phi i64 [ %92, %90 ], [ %94, %96 ]
  %99 = getelementptr inbounds i64, i64* %0, i64 %8
  %100 = load i64, i64* %99, align 8, !tbaa !2
  %101 = icmp ult i64 %100, %98
  br i1 %101, label %102, label %104

; <label>:102:                                    ; preds = %97
  store i64 %100, i64* %91, align 8, !tbaa !2
  store i64 %98, i64* %99, align 8, !tbaa !2
  %103 = load i64, i64* %91, align 8, !tbaa !2
  br label %104

; <label>:104:                                    ; preds = %102, %97
  %105 = phi i64 [ %98, %97 ], [ %103, %102 ]
  %106 = load i64, i64* %93, align 8, !tbaa !2
  %107 = icmp ult i64 %105, %106
  br i1 %107, label %108, label %109

; <label>:108:                                    ; preds = %104
  store i64 %105, i64* %93, align 8, !tbaa !2
  store i64 %106, i64* %91, align 8, !tbaa !2
  br label %109

; <label>:109:                                    ; preds = %108, %104, %87
  ret void
}

; Function Attrs: inlinehint norecurse nounwind uwtable
define linkonce_odr zeroext i1 @_Z7shufflePmmmm(i64*, i64, i64, i64) local_unnamed_addr #9 comdat {
  %5 = sub i64 %2, %1
  %6 = sub i64 %3, %1
  %7 = add i64 %3, 1
  %8 = sub i64 %2, %7
  %9 = lshr i64 %5, 3
  %10 = icmp ult i64 %6, %9
  %11 = icmp ult i64 %8, %9
  %12 = or i1 %10, %11
  br i1 %12, label %13, label %99

; <label>:13:                                     ; preds = %4
  %14 = icmp ugt i64 %6, 23
  br i1 %14, label %15, label %56

; <label>:15:                                     ; preds = %13
  %16 = getelementptr inbounds i64, i64* %0, i64 %1
  %17 = lshr i64 %6, 2
  %18 = add i64 %17, %1
  %19 = getelementptr inbounds i64, i64* %0, i64 %18
  %20 = load i64, i64* %16, align 8, !tbaa !2
  %21 = load i64, i64* %19, align 8, !tbaa !2
  store i64 %21, i64* %16, align 8, !tbaa !2
  store i64 %20, i64* %19, align 8, !tbaa !2
  %22 = add i64 %3, -1
  %23 = getelementptr inbounds i64, i64* %0, i64 %22
  %24 = sub i64 %3, %17
  %25 = getelementptr inbounds i64, i64* %0, i64 %24
  %26 = load i64, i64* %23, align 8, !tbaa !2
  %27 = load i64, i64* %25, align 8, !tbaa !2
  store i64 %27, i64* %23, align 8, !tbaa !2
  store i64 %26, i64* %25, align 8, !tbaa !2
  %28 = icmp ugt i64 %6, 128
  br i1 %28, label %29, label %56

; <label>:29:                                     ; preds = %15
  %30 = add i64 %1, 1
  %31 = getelementptr inbounds i64, i64* %0, i64 %30
  %32 = add nuw nsw i64 %17, 1
  %33 = add i64 %32, %1
  %34 = getelementptr inbounds i64, i64* %0, i64 %33
  %35 = load i64, i64* %31, align 8, !tbaa !2
  %36 = load i64, i64* %34, align 8, !tbaa !2
  store i64 %36, i64* %31, align 8, !tbaa !2
  store i64 %35, i64* %34, align 8, !tbaa !2
  %37 = add i64 %1, 2
  %38 = getelementptr inbounds i64, i64* %0, i64 %37
  %39 = add nuw nsw i64 %17, 2
  %40 = add i64 %39, %1
  %41 = getelementptr inbounds i64, i64* %0, i64 %40
  %42 = load i64, i64* %38, align 8, !tbaa !2
  %43 = load i64, i64* %41, align 8, !tbaa !2
  store i64 %43, i64* %38, align 8, !tbaa !2
  store i64 %42, i64* %41, align 8, !tbaa !2
  %44 = add i64 %3, -2
  %45 = getelementptr inbounds i64, i64* %0, i64 %44
  %46 = sub i64 %3, %32
  %47 = getelementptr inbounds i64, i64* %0, i64 %46
  %48 = load i64, i64* %45, align 8, !tbaa !2
  %49 = load i64, i64* %47, align 8, !tbaa !2
  store i64 %49, i64* %45, align 8, !tbaa !2
  store i64 %48, i64* %47, align 8, !tbaa !2
  %50 = add i64 %3, -3
  %51 = getelementptr inbounds i64, i64* %0, i64 %50
  %52 = sub i64 %3, %39
  %53 = getelementptr inbounds i64, i64* %0, i64 %52
  %54 = load i64, i64* %51, align 8, !tbaa !2
  %55 = load i64, i64* %53, align 8, !tbaa !2
  store i64 %55, i64* %51, align 8, !tbaa !2
  store i64 %54, i64* %53, align 8, !tbaa !2
  br label %56

; <label>:56:                                     ; preds = %15, %29, %13
  %57 = icmp ugt i64 %8, 23
  br i1 %57, label %58, label %99

; <label>:58:                                     ; preds = %56
  %59 = getelementptr inbounds i64, i64* %0, i64 %7
  %60 = lshr i64 %8, 2
  %61 = add nuw nsw i64 %60, 1
  %62 = add i64 %61, %3
  %63 = getelementptr inbounds i64, i64* %0, i64 %62
  %64 = load i64, i64* %59, align 8, !tbaa !2
  %65 = load i64, i64* %63, align 8, !tbaa !2
  store i64 %65, i64* %59, align 8, !tbaa !2
  store i64 %64, i64* %63, align 8, !tbaa !2
  %66 = add i64 %2, -1
  %67 = getelementptr inbounds i64, i64* %0, i64 %66
  %68 = sub i64 %2, %60
  %69 = getelementptr inbounds i64, i64* %0, i64 %68
  %70 = load i64, i64* %67, align 8, !tbaa !2
  %71 = load i64, i64* %69, align 8, !tbaa !2
  store i64 %71, i64* %67, align 8, !tbaa !2
  store i64 %70, i64* %69, align 8, !tbaa !2
  %72 = icmp ugt i64 %8, 128
  br i1 %72, label %73, label %99

; <label>:73:                                     ; preds = %58
  %74 = add i64 %3, 2
  %75 = getelementptr inbounds i64, i64* %0, i64 %74
  %76 = add nuw nsw i64 %60, 2
  %77 = add i64 %76, %3
  %78 = getelementptr inbounds i64, i64* %0, i64 %77
  %79 = load i64, i64* %75, align 8, !tbaa !2
  %80 = load i64, i64* %78, align 8, !tbaa !2
  store i64 %80, i64* %75, align 8, !tbaa !2
  store i64 %79, i64* %78, align 8, !tbaa !2
  %81 = add i64 %3, 3
  %82 = getelementptr inbounds i64, i64* %0, i64 %81
  %83 = add i64 %81, %60
  %84 = getelementptr inbounds i64, i64* %0, i64 %83
  %85 = load i64, i64* %82, align 8, !tbaa !2
  %86 = load i64, i64* %84, align 8, !tbaa !2
  store i64 %86, i64* %82, align 8, !tbaa !2
  store i64 %85, i64* %84, align 8, !tbaa !2
  %87 = add i64 %2, -2
  %88 = getelementptr inbounds i64, i64* %0, i64 %87
  %89 = sub i64 %2, %61
  %90 = getelementptr inbounds i64, i64* %0, i64 %89
  %91 = load i64, i64* %88, align 8, !tbaa !2
  %92 = load i64, i64* %90, align 8, !tbaa !2
  store i64 %92, i64* %88, align 8, !tbaa !2
  store i64 %91, i64* %90, align 8, !tbaa !2
  %93 = add i64 %2, -3
  %94 = getelementptr inbounds i64, i64* %0, i64 %93
  %95 = sub i64 %2, %76
  %96 = getelementptr inbounds i64, i64* %0, i64 %95
  %97 = load i64, i64* %94, align 8, !tbaa !2
  %98 = load i64, i64* %96, align 8, !tbaa !2
  store i64 %98, i64* %94, align 8, !tbaa !2
  store i64 %97, i64* %96, align 8, !tbaa !2
  br label %99

; <label>:99:                                     ; preds = %56, %73, %58, %4
  ret i1 %12
}

; Function Attrs: norecurse uwtable
define i32 @main(i32, i8** nocapture readnone) local_unnamed_addr #10 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %3 = alloca %"class.std::vector", align 8
  %4 = alloca %"class.std::vector", align 8
  %5 = alloca %"class.std::vector", align 8
  %6 = alloca %"class.std::vector", align 8
  %7 = alloca %"class.std::vector", align 8
  %8 = alloca %"class.std::vector", align 8
  %9 = alloca %"class.std::vector", align 8
  %10 = alloca %"class.std::vector", align 8
  %11 = alloca %"class.std::vector", align 8
  %12 = alloca %"class.std::vector", align 8
  %13 = alloca %"class.std::vector", align 8
  %14 = alloca %"class.std::vector", align 8
  %15 = alloca %"class.std::vector", align 8
  %16 = alloca %"class.std::vector", align 8
  %17 = alloca %"class.std::vector", align 8
  %18 = alloca %"class.std::vector", align 8
  %19 = alloca %"class.std::vector", align 8
  %20 = alloca %"class.std::vector", align 8
  %21 = alloca %"class.std::vector", align 8
  %22 = alloca %"class.std::__cxx11::basic_string", align 8
  %23 = alloca %"class.std::__cxx11::basic_string", align 8
  %24 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([6 x i8], [6 x i8]* @.str, i64 0, i64 0), i64 5)
  %25 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %26 = getelementptr i8, i8* %25, i64 -24
  %27 = bitcast i8* %26 to i64*
  %28 = load i64, i64* %27, align 8
  %29 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %28
  %30 = getelementptr inbounds i8, i8* %29, i64 240
  %31 = bitcast i8* %30 to %"class.std::ctype"**
  %32 = load %"class.std::ctype"*, %"class.std::ctype"** %31, align 8, !tbaa !8
  %33 = icmp eq %"class.std::ctype"* %32, null
  br i1 %33, label %34, label %35

; <label>:34:                                     ; preds = %2
  tail call void @_ZSt16__throw_bad_castv() #16
  unreachable

; <label>:35:                                     ; preds = %2
  %36 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %32, i64 0, i32 8
  %37 = load i8, i8* %36, align 8, !tbaa !12
  %38 = icmp eq i8 %37, 0
  br i1 %38, label %42, label %39

; <label>:39:                                     ; preds = %35
  %40 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %32, i64 0, i32 9, i64 10
  %41 = load i8, i8* %40, align 1, !tbaa !14
  br label %48

; <label>:42:                                     ; preds = %35
  tail call void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %32)
  %43 = bitcast %"class.std::ctype"* %32 to i8 (%"class.std::ctype"*, i8)***
  %44 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %43, align 8, !tbaa !6
  %45 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %44, i64 6
  %46 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %45, align 8
  %47 = tail call signext i8 %46(%"class.std::ctype"* nonnull %32, i8 signext 10)
  br label %48

; <label>:48:                                     ; preds = %39, %42
  %49 = phi i8 [ %41, %39 ], [ %47, %42 ]
  %50 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %49)
  %51 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %50)
  %52 = bitcast %"class.std::vector"* %21 to i8*
  %53 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %21, i64 0, i32 0, i32 0, i32 0
  %54 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %21, i64 0, i32 0, i32 0, i32 1
  %55 = bitcast i64** %54 to i64*
  br label %64

; <label>:56:                                     ; preds = %86
  %57 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %22, i64 0, i32 2
  %58 = bitcast %"class.std::__cxx11::basic_string"* %22 to %union.anon**
  store %union.anon* %57, %union.anon** %58, align 8, !tbaa !15
  %59 = bitcast %union.anon* %57 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %59, i8* nonnull getelementptr inbounds ([8 x i8], [8 x i8]* @.str.1, i64 0, i64 0), i64 7, i32 1, i1 false) #2
  %60 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %22, i64 0, i32 1
  store i64 7, i64* %60, align 8, !tbaa !17
  %61 = getelementptr inbounds i8, i8* %59, i64 7
  store i8 0, i8* %61, align 1, !tbaa !14
  %62 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %22, i64 0, i32 0, i32 0
  %63 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull %59, i64 7)
          to label %98 unwind label %1387

; <label>:64:                                     ; preds = %48, %86
  %65 = phi i64 [ 0, %48 ], [ %87, %86 ]
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %52) #2
  call void @_ZN13Int_Generator6randomEm(%"class.std::vector"* nonnull sret %21, i64 1000)
  %66 = load i64*, i64** %53, align 8, !tbaa !19
  %67 = load i64, i64* %55, align 8, !tbaa !22
  %68 = ptrtoint i64* %66 to i64
  %69 = sub i64 %67, %68
  %70 = ashr exact i64 %69, 3
  %71 = icmp eq i64 %69, 0
  br i1 %71, label %80, label %72

; <label>:72:                                     ; preds = %64
  br label %73

; <label>:73:                                     ; preds = %72, %73
  %74 = phi i64 [ %76, %73 ], [ %70, %72 ]
  %75 = phi i32 [ %78, %73 ], [ 0, %72 ]
  %76 = lshr i64 %74, 1
  %77 = icmp eq i64 %76, 0
  %78 = add nuw nsw i32 %75, 1
  br i1 %77, label %79, label %73

; <label>:79:                                     ; preds = %73
  invoke void @_Z11pdqsort_recPmmmib(i64* %66, i64 0, i64 %70, i32 %75, i1 zeroext true)
          to label %80 unwind label %89

; <label>:80:                                     ; preds = %64, %79
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %21)
          to label %81 unwind label %89

; <label>:81:                                     ; preds = %80
  %82 = load i64*, i64** %53, align 8, !tbaa !19
  %83 = icmp eq i64* %82, null
  br i1 %83, label %86, label %84

; <label>:84:                                     ; preds = %81
  %85 = bitcast i64* %82 to i8*
  call void @_ZdlPv(i8* %85) #2
  br label %86

; <label>:86:                                     ; preds = %81, %84
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %52) #2
  %87 = add nuw nsw i64 %65, 1
  %88 = icmp ult i64 %87, 100
  br i1 %88, label %64, label %56

; <label>:89:                                     ; preds = %79, %80
  %90 = landingpad { i8*, i32 }
          cleanup
  %91 = extractvalue { i8*, i32 } %90, 0
  %92 = extractvalue { i8*, i32 } %90, 1
  %93 = load i64*, i64** %53, align 8, !tbaa !19
  %94 = icmp eq i64* %93, null
  br i1 %94, label %97, label %95

; <label>:95:                                     ; preds = %89
  %96 = bitcast i64* %93 to i8*
  call void @_ZdlPv(i8* %96) #2
  br label %97

; <label>:97:                                     ; preds = %89, %95
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %52) #2
  br label %1405

; <label>:98:                                     ; preds = %56
  %99 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) %63, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i64 1)
          to label %100 unwind label %1387

; <label>:100:                                    ; preds = %98
  %101 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %102 unwind label %1387

; <label>:102:                                    ; preds = %100
  %103 = bitcast %"class.std::vector"* %12 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %103) #2
  invoke void @_ZN13Int_Generator6randomEm(%"class.std::vector"* nonnull sret %12, i64 10000000)
          to label %104 unwind label %1387

; <label>:104:                                    ; preds = %102
  %105 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %106 unwind label %624

; <label>:106:                                    ; preds = %104
  %107 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %108 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %12, i64 0, i32 0, i32 0, i32 0
  %109 = load i64*, i64** %108, align 8, !tbaa !23
  %110 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %12, i64 0, i32 0, i32 0, i32 1
  %111 = load i64*, i64** %110, align 8, !tbaa !23
  %112 = icmp eq i64* %109, %111
  br i1 %112, label %121, label %113

; <label>:113:                                    ; preds = %106
  %114 = ptrtoint i64* %111 to i64
  %115 = ptrtoint i64* %109 to i64
  %116 = sub i64 %114, %115
  %117 = ashr i64 %116, 4
  %118 = call i64 @llvm.ctlz.i64(i64 %117, i1 false) #2, !range !24
  %119 = trunc i64 %118 to i32
  %120 = sub nsw i32 64, %119
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %109, i64* %111, i32 %120, i1 zeroext true)
          to label %121 unwind label %624

; <label>:121:                                    ; preds = %113, %106
  %122 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %123 = sub nsw i64 %122, %107
  %124 = sitofp i64 %123 to double
  %125 = fdiv double %124, 1.000000e+09
  %126 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %125)
          to label %127 unwind label %624

; <label>:127:                                    ; preds = %121
  %128 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %129 unwind label %624

; <label>:129:                                    ; preds = %127
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %12)
          to label %130 unwind label %624

; <label>:130:                                    ; preds = %129
  %131 = load i64*, i64** %108, align 8, !tbaa !19
  %132 = icmp eq i64* %131, null
  br i1 %132, label %135, label %133

; <label>:133:                                    ; preds = %130
  %134 = bitcast i64* %131 to i8*
  call void @_ZdlPv(i8* %134) #2
  br label %135

; <label>:135:                                    ; preds = %133, %130
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %103) #2
  %136 = bitcast %"class.std::vector"* %13 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %136) #2
  invoke void @_ZN13Int_Generator10random_dupEmm(%"class.std::vector"* nonnull sret %13, i64 10000000, i64 10000)
          to label %137 unwind label %1387

; <label>:137:                                    ; preds = %135
  %138 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %139 unwind label %634

; <label>:139:                                    ; preds = %137
  %140 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %141 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %13, i64 0, i32 0, i32 0, i32 0
  %142 = load i64*, i64** %141, align 8, !tbaa !23
  %143 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %13, i64 0, i32 0, i32 0, i32 1
  %144 = load i64*, i64** %143, align 8, !tbaa !23
  %145 = icmp eq i64* %142, %144
  br i1 %145, label %154, label %146

; <label>:146:                                    ; preds = %139
  %147 = ptrtoint i64* %144 to i64
  %148 = ptrtoint i64* %142 to i64
  %149 = sub i64 %147, %148
  %150 = ashr i64 %149, 4
  %151 = call i64 @llvm.ctlz.i64(i64 %150, i1 false) #2, !range !24
  %152 = trunc i64 %151 to i32
  %153 = sub nsw i32 64, %152
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %142, i64* %144, i32 %153, i1 zeroext true)
          to label %154 unwind label %634

; <label>:154:                                    ; preds = %146, %139
  %155 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %156 = sub nsw i64 %155, %140
  %157 = sitofp i64 %156 to double
  %158 = fdiv double %157, 1.000000e+09
  %159 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %158)
          to label %160 unwind label %634

; <label>:160:                                    ; preds = %154
  %161 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %162 unwind label %634

; <label>:162:                                    ; preds = %160
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %13)
          to label %163 unwind label %634

; <label>:163:                                    ; preds = %162
  %164 = load i64*, i64** %141, align 8, !tbaa !19
  %165 = icmp eq i64* %164, null
  br i1 %165, label %168, label %166

; <label>:166:                                    ; preds = %163
  %167 = bitcast i64* %164 to i8*
  call void @_ZdlPv(i8* %167) #2
  br label %168

; <label>:168:                                    ; preds = %166, %163
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %136) #2
  %169 = bitcast %"class.std::vector"* %14 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %169) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %169, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !25
  %170 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %14, i64 0, i32 0, i32 0, i32 2
  %171 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %14, i64 0, i32 0, i32 0, i32 1
  %172 = invoke i8* @_Znwm(i64 800000000)
          to label %173 unwind label %182, !noalias !25

; <label>:173:                                    ; preds = %168
  %174 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %14, i64 0, i32 0, i32 0, i32 0
  %175 = bitcast %"class.std::vector"* %14 to i8**
  store i8* %172, i8** %175, align 8, !tbaa !19, !alias.scope !25
  %176 = getelementptr inbounds i8, i8* %172, i64 800000000
  %177 = bitcast i64** %170 to i8**
  store i8* %176, i8** %177, align 8, !tbaa !28, !alias.scope !25
  %178 = ptrtoint i8* %172 to i64
  %179 = bitcast i64** %171 to i64*
  store i64 %178, i64* %179, align 8, !tbaa !22, !alias.scope !25
  %180 = bitcast i8* %172 to i64*
  %181 = bitcast i8* %176 to i64*
  br label %186

; <label>:182:                                    ; preds = %168
  %183 = landingpad { i8*, i32 }
          cleanup
  %184 = extractvalue { i8*, i32 } %183, 0
  %185 = extractvalue { i8*, i32 } %183, 1
  br label %264

; <label>:186:                                    ; preds = %246, %173
  %187 = phi i64 [ %178, %173 ], [ %247, %246 ]
  %188 = phi i64* [ %181, %173 ], [ %248, %246 ]
  %189 = phi i64* [ %180, %173 ], [ %249, %246 ]
  %190 = phi i64 [ 0, %173 ], [ %250, %246 ]
  %191 = icmp eq i64* %189, %188
  %192 = ptrtoint i64* %189 to i64
  br i1 %191, label %195, label %193

; <label>:193:                                    ; preds = %186
  store i64 %190, i64* %189, align 8, !tbaa !2
  %194 = getelementptr inbounds i64, i64* %189, i64 1
  store i64* %194, i64** %171, align 8, !tbaa !22
  br label %246

; <label>:195:                                    ; preds = %186
  %196 = sub i64 %192, %187
  %197 = ashr exact i64 %196, 3
  %198 = icmp eq i64 %196, 0
  %199 = select i1 %198, i64 1, i64 %197
  %200 = add nsw i64 %199, %197
  %201 = icmp ult i64 %200, %197
  %202 = icmp ugt i64 %200, 2305843009213693951
  %203 = or i1 %201, %202
  %204 = select i1 %203, i64 2305843009213693951, i64 %200
  %205 = icmp eq i64 %204, 0
  %206 = inttoptr i64 %187 to i64*
  br i1 %205, label %217, label %207

; <label>:207:                                    ; preds = %195
  %208 = icmp ugt i64 %204, 2305843009213693951
  br i1 %208, label %209, label %211

; <label>:209:                                    ; preds = %207
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %210 unwind label %254

; <label>:210:                                    ; preds = %209
  unreachable

; <label>:211:                                    ; preds = %207
  %212 = shl i64 %204, 3
  %213 = invoke i8* @_Znwm(i64 %212)
          to label %214 unwind label %252

; <label>:214:                                    ; preds = %211
  %215 = bitcast i8* %213 to i64*
  %216 = load i64*, i64** %174, align 8, !tbaa !19
  br label %217

; <label>:217:                                    ; preds = %214, %195
  %218 = phi i64* [ %216, %214 ], [ %206, %195 ]
  %219 = phi i8* [ %213, %214 ], [ null, %195 ]
  %220 = phi i64* [ %215, %214 ], [ null, %195 ]
  %221 = getelementptr inbounds i64, i64* %220, i64 %197
  store i64 %190, i64* %221, align 8, !tbaa !2
  %222 = ptrtoint i64* %218 to i64
  %223 = sub i64 %192, %222
  %224 = ashr exact i64 %223, 3
  %225 = icmp eq i64 %223, 0
  br i1 %225, label %228, label %226

; <label>:226:                                    ; preds = %217
  %227 = bitcast i64* %218 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %219, i8* %227, i64 %223, i32 8, i1 false) #2
  br label %228

; <label>:228:                                    ; preds = %226, %217
  %229 = getelementptr inbounds i64, i64* %220, i64 %224
  %230 = getelementptr inbounds i64, i64* %229, i64 1
  %231 = load i64, i64* %179, align 8, !tbaa !22
  %232 = sub i64 %231, %192
  %233 = ashr exact i64 %232, 3
  %234 = icmp eq i64 %232, 0
  br i1 %234, label %238, label %235

; <label>:235:                                    ; preds = %228
  %236 = bitcast i64* %230 to i8*
  %237 = bitcast i64* %188 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %236, i8* %237, i64 %232, i32 8, i1 false) #2
  br label %238

; <label>:238:                                    ; preds = %235, %228
  %239 = getelementptr inbounds i64, i64* %230, i64 %233
  %240 = icmp eq i64* %218, null
  br i1 %240, label %243, label %241

; <label>:241:                                    ; preds = %238
  %242 = bitcast i64* %218 to i8*
  call void @_ZdlPv(i8* %242) #2
  br label %243

; <label>:243:                                    ; preds = %241, %238
  store i8* %219, i8** %175, align 8, !tbaa !19
  store i64* %239, i64** %171, align 8, !tbaa !22
  %244 = getelementptr inbounds i64, i64* %220, i64 %204
  store i64* %244, i64** %170, align 8, !tbaa !28
  %245 = ptrtoint i8* %219 to i64
  br label %246

; <label>:246:                                    ; preds = %243, %193
  %247 = phi i64 [ %245, %243 ], [ %187, %193 ]
  %248 = phi i64* [ %244, %243 ], [ %188, %193 ]
  %249 = phi i64* [ %239, %243 ], [ %194, %193 ]
  %250 = add nuw nsw i64 %190, 1
  %251 = icmp ult i64 %250, 100000000
  br i1 %251, label %186, label %269

; <label>:252:                                    ; preds = %211
  %253 = landingpad { i8*, i32 }
          cleanup
  br label %256

; <label>:254:                                    ; preds = %209
  %255 = landingpad { i8*, i32 }
          cleanup
  br label %256

; <label>:256:                                    ; preds = %254, %252
  %257 = phi { i8*, i32 } [ %253, %252 ], [ %255, %254 ]
  %258 = extractvalue { i8*, i32 } %257, 0
  %259 = extractvalue { i8*, i32 } %257, 1
  %260 = load i64*, i64** %174, align 8, !tbaa !19, !alias.scope !25
  %261 = icmp eq i64* %260, null
  br i1 %261, label %264, label %262

; <label>:262:                                    ; preds = %256
  %263 = bitcast i64* %260 to i8*
  call void @_ZdlPv(i8* %263) #2
  br label %264

; <label>:264:                                    ; preds = %262, %256, %182
  %265 = phi i32 [ %185, %182 ], [ %259, %262 ], [ %259, %256 ]
  %266 = phi i8* [ %184, %182 ], [ %258, %262 ], [ %258, %256 ]
  %267 = insertvalue { i8*, i32 } undef, i8* %266, 0
  %268 = insertvalue { i8*, i32 } %267, i32 %265, 1
  br label %1389

; <label>:269:                                    ; preds = %246
  %270 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %271 unwind label %644

; <label>:271:                                    ; preds = %269
  %272 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %273 = load i64*, i64** %174, align 8, !tbaa !23
  %274 = load i64*, i64** %171, align 8, !tbaa !23
  %275 = icmp eq i64* %273, %274
  br i1 %275, label %284, label %276

; <label>:276:                                    ; preds = %271
  %277 = ptrtoint i64* %274 to i64
  %278 = ptrtoint i64* %273 to i64
  %279 = sub i64 %277, %278
  %280 = ashr i64 %279, 4
  %281 = call i64 @llvm.ctlz.i64(i64 %280, i1 false) #2, !range !24
  %282 = trunc i64 %281 to i32
  %283 = sub nsw i32 64, %282
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %273, i64* %274, i32 %283, i1 zeroext true)
          to label %284 unwind label %644

; <label>:284:                                    ; preds = %276, %271
  %285 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %286 = sub nsw i64 %285, %272
  %287 = sitofp i64 %286 to double
  %288 = fdiv double %287, 1.000000e+09
  %289 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %288)
          to label %290 unwind label %644

; <label>:290:                                    ; preds = %284
  %291 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %292 unwind label %644

; <label>:292:                                    ; preds = %290
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %14)
          to label %293 unwind label %644

; <label>:293:                                    ; preds = %292
  %294 = load i64*, i64** %174, align 8, !tbaa !19
  %295 = icmp eq i64* %294, null
  br i1 %295, label %298, label %296

; <label>:296:                                    ; preds = %293
  %297 = bitcast i64* %294 to i8*
  call void @_ZdlPv(i8* %297) #2
  br label %298

; <label>:298:                                    ; preds = %296, %293
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %169) #2
  %299 = bitcast %"class.std::vector"* %15 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %299) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %15, i64 10000000, i64 100000)
          to label %300 unwind label %1387

; <label>:300:                                    ; preds = %298
  %301 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %302 unwind label %653

; <label>:302:                                    ; preds = %300
  %303 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %304 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %15, i64 0, i32 0, i32 0, i32 0
  %305 = load i64*, i64** %304, align 8, !tbaa !23
  %306 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %15, i64 0, i32 0, i32 0, i32 1
  %307 = load i64*, i64** %306, align 8, !tbaa !23
  %308 = icmp eq i64* %305, %307
  br i1 %308, label %317, label %309

; <label>:309:                                    ; preds = %302
  %310 = ptrtoint i64* %307 to i64
  %311 = ptrtoint i64* %305 to i64
  %312 = sub i64 %310, %311
  %313 = ashr i64 %312, 4
  %314 = call i64 @llvm.ctlz.i64(i64 %313, i1 false) #2, !range !24
  %315 = trunc i64 %314 to i32
  %316 = sub nsw i32 64, %315
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %305, i64* %307, i32 %316, i1 zeroext true)
          to label %317 unwind label %653

; <label>:317:                                    ; preds = %309, %302
  %318 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %319 = sub nsw i64 %318, %303
  %320 = sitofp i64 %319 to double
  %321 = fdiv double %320, 1.000000e+09
  %322 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %321)
          to label %323 unwind label %653

; <label>:323:                                    ; preds = %317
  %324 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %325 unwind label %653

; <label>:325:                                    ; preds = %323
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %15)
          to label %326 unwind label %653

; <label>:326:                                    ; preds = %325
  %327 = load i64*, i64** %304, align 8, !tbaa !19
  %328 = icmp eq i64* %327, null
  br i1 %328, label %331, label %329

; <label>:329:                                    ; preds = %326
  %330 = bitcast i64* %327 to i8*
  call void @_ZdlPv(i8* %330) #2
  br label %331

; <label>:331:                                    ; preds = %329, %326
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %299) #2
  %332 = bitcast %"class.std::vector"* %16 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %332) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %16, i64 10000000, i64 1000000)
          to label %333 unwind label %1387

; <label>:333:                                    ; preds = %331
  %334 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %335 unwind label %663

; <label>:335:                                    ; preds = %333
  %336 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %337 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %16, i64 0, i32 0, i32 0, i32 0
  %338 = load i64*, i64** %337, align 8, !tbaa !23
  %339 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %16, i64 0, i32 0, i32 0, i32 1
  %340 = load i64*, i64** %339, align 8, !tbaa !23
  %341 = icmp eq i64* %338, %340
  br i1 %341, label %350, label %342

; <label>:342:                                    ; preds = %335
  %343 = ptrtoint i64* %340 to i64
  %344 = ptrtoint i64* %338 to i64
  %345 = sub i64 %343, %344
  %346 = ashr i64 %345, 4
  %347 = call i64 @llvm.ctlz.i64(i64 %346, i1 false) #2, !range !24
  %348 = trunc i64 %347 to i32
  %349 = sub nsw i32 64, %348
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %338, i64* %340, i32 %349, i1 zeroext true)
          to label %350 unwind label %663

; <label>:350:                                    ; preds = %342, %335
  %351 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %352 = sub nsw i64 %351, %336
  %353 = sitofp i64 %352 to double
  %354 = fdiv double %353, 1.000000e+09
  %355 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %354)
          to label %356 unwind label %663

; <label>:356:                                    ; preds = %350
  %357 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %358 unwind label %663

; <label>:358:                                    ; preds = %356
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %16)
          to label %359 unwind label %663

; <label>:359:                                    ; preds = %358
  %360 = load i64*, i64** %337, align 8, !tbaa !19
  %361 = icmp eq i64* %360, null
  br i1 %361, label %364, label %362

; <label>:362:                                    ; preds = %359
  %363 = bitcast i64* %360 to i8*
  call void @_ZdlPv(i8* %363) #2
  br label %364

; <label>:364:                                    ; preds = %362, %359
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %332) #2
  %365 = bitcast %"class.std::vector"* %17 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %365) #2
  invoke void @_ZN13Int_Generator13sorted_middleEmm(%"class.std::vector"* nonnull sret %17, i64 10000000, i64 1000000)
          to label %366 unwind label %1387

; <label>:366:                                    ; preds = %364
  %367 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %368 unwind label %673

; <label>:368:                                    ; preds = %366
  %369 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %370 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %17, i64 0, i32 0, i32 0, i32 0
  %371 = load i64*, i64** %370, align 8, !tbaa !23
  %372 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %17, i64 0, i32 0, i32 0, i32 1
  %373 = load i64*, i64** %372, align 8, !tbaa !23
  %374 = icmp eq i64* %371, %373
  br i1 %374, label %383, label %375

; <label>:375:                                    ; preds = %368
  %376 = ptrtoint i64* %373 to i64
  %377 = ptrtoint i64* %371 to i64
  %378 = sub i64 %376, %377
  %379 = ashr i64 %378, 4
  %380 = call i64 @llvm.ctlz.i64(i64 %379, i1 false) #2, !range !24
  %381 = trunc i64 %380 to i32
  %382 = sub nsw i32 64, %381
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %371, i64* %373, i32 %382, i1 zeroext true)
          to label %383 unwind label %673

; <label>:383:                                    ; preds = %375, %368
  %384 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %385 = sub nsw i64 %384, %369
  %386 = sitofp i64 %385 to double
  %387 = fdiv double %386, 1.000000e+09
  %388 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %387)
          to label %389 unwind label %673

; <label>:389:                                    ; preds = %383
  %390 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %391 unwind label %673

; <label>:391:                                    ; preds = %389
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %17)
          to label %392 unwind label %673

; <label>:392:                                    ; preds = %391
  %393 = load i64*, i64** %370, align 8, !tbaa !19
  %394 = icmp eq i64* %393, null
  br i1 %394, label %397, label %395

; <label>:395:                                    ; preds = %392
  %396 = bitcast i64* %393 to i8*
  call void @_ZdlPv(i8* %396) #2
  br label %397

; <label>:397:                                    ; preds = %395, %392
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %365) #2
  %398 = bitcast %"class.std::vector"* %18 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %398) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %398, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !29
  %399 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %18, i64 0, i32 0, i32 0, i32 2
  %400 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %18, i64 0, i32 0, i32 0, i32 1
  %401 = invoke i8* @_Znwm(i64 800000000)
          to label %402 unwind label %411, !noalias !29

; <label>:402:                                    ; preds = %397
  %403 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %18, i64 0, i32 0, i32 0, i32 0
  %404 = bitcast %"class.std::vector"* %18 to i8**
  store i8* %401, i8** %404, align 8, !tbaa !19, !alias.scope !29
  %405 = getelementptr inbounds i8, i8* %401, i64 800000000
  %406 = bitcast i64** %399 to i8**
  store i8* %405, i8** %406, align 8, !tbaa !28, !alias.scope !29
  %407 = ptrtoint i8* %401 to i64
  %408 = bitcast i64** %400 to i64*
  store i64 %407, i64* %408, align 8, !tbaa !22, !alias.scope !29
  %409 = bitcast i8* %401 to i64*
  %410 = bitcast i8* %405 to i64*
  br label %415

; <label>:411:                                    ; preds = %397
  %412 = landingpad { i8*, i32 }
          cleanup
  %413 = extractvalue { i8*, i32 } %412, 0
  %414 = extractvalue { i8*, i32 } %412, 1
  br label %493

; <label>:415:                                    ; preds = %475, %402
  %416 = phi i64 [ %407, %402 ], [ %476, %475 ]
  %417 = phi i64* [ %410, %402 ], [ %477, %475 ]
  %418 = phi i64* [ %409, %402 ], [ %478, %475 ]
  %419 = phi i64 [ 100000000, %402 ], [ %479, %475 ]
  %420 = icmp eq i64* %418, %417
  %421 = ptrtoint i64* %418 to i64
  br i1 %420, label %424, label %422

; <label>:422:                                    ; preds = %415
  store i64 %419, i64* %418, align 8, !tbaa !2
  %423 = getelementptr inbounds i64, i64* %418, i64 1
  store i64* %423, i64** %400, align 8, !tbaa !22
  br label %475

; <label>:424:                                    ; preds = %415
  %425 = sub i64 %421, %416
  %426 = ashr exact i64 %425, 3
  %427 = icmp eq i64 %425, 0
  %428 = select i1 %427, i64 1, i64 %426
  %429 = add nsw i64 %428, %426
  %430 = icmp ult i64 %429, %426
  %431 = icmp ugt i64 %429, 2305843009213693951
  %432 = or i1 %430, %431
  %433 = select i1 %432, i64 2305843009213693951, i64 %429
  %434 = icmp eq i64 %433, 0
  %435 = inttoptr i64 %416 to i64*
  br i1 %434, label %446, label %436

; <label>:436:                                    ; preds = %424
  %437 = icmp ugt i64 %433, 2305843009213693951
  br i1 %437, label %438, label %440

; <label>:438:                                    ; preds = %436
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %439 unwind label %483

; <label>:439:                                    ; preds = %438
  unreachable

; <label>:440:                                    ; preds = %436
  %441 = shl i64 %433, 3
  %442 = invoke i8* @_Znwm(i64 %441)
          to label %443 unwind label %481

; <label>:443:                                    ; preds = %440
  %444 = bitcast i8* %442 to i64*
  %445 = load i64*, i64** %403, align 8, !tbaa !19
  br label %446

; <label>:446:                                    ; preds = %443, %424
  %447 = phi i64* [ %445, %443 ], [ %435, %424 ]
  %448 = phi i8* [ %442, %443 ], [ null, %424 ]
  %449 = phi i64* [ %444, %443 ], [ null, %424 ]
  %450 = getelementptr inbounds i64, i64* %449, i64 %426
  store i64 %419, i64* %450, align 8, !tbaa !2
  %451 = ptrtoint i64* %447 to i64
  %452 = sub i64 %421, %451
  %453 = ashr exact i64 %452, 3
  %454 = icmp eq i64 %452, 0
  br i1 %454, label %457, label %455

; <label>:455:                                    ; preds = %446
  %456 = bitcast i64* %447 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %448, i8* %456, i64 %452, i32 8, i1 false) #2
  br label %457

; <label>:457:                                    ; preds = %455, %446
  %458 = getelementptr inbounds i64, i64* %449, i64 %453
  %459 = getelementptr inbounds i64, i64* %458, i64 1
  %460 = load i64, i64* %408, align 8, !tbaa !22
  %461 = sub i64 %460, %421
  %462 = ashr exact i64 %461, 3
  %463 = icmp eq i64 %461, 0
  br i1 %463, label %467, label %464

; <label>:464:                                    ; preds = %457
  %465 = bitcast i64* %459 to i8*
  %466 = bitcast i64* %417 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %465, i8* %466, i64 %461, i32 8, i1 false) #2
  br label %467

; <label>:467:                                    ; preds = %464, %457
  %468 = getelementptr inbounds i64, i64* %459, i64 %462
  %469 = icmp eq i64* %447, null
  br i1 %469, label %472, label %470

; <label>:470:                                    ; preds = %467
  %471 = bitcast i64* %447 to i8*
  call void @_ZdlPv(i8* %471) #2
  br label %472

; <label>:472:                                    ; preds = %470, %467
  store i8* %448, i8** %404, align 8, !tbaa !19
  store i64* %468, i64** %400, align 8, !tbaa !22
  %473 = getelementptr inbounds i64, i64* %449, i64 %433
  store i64* %473, i64** %399, align 8, !tbaa !28
  %474 = ptrtoint i8* %448 to i64
  br label %475

; <label>:475:                                    ; preds = %472, %422
  %476 = phi i64 [ %474, %472 ], [ %416, %422 ]
  %477 = phi i64* [ %473, %472 ], [ %417, %422 ]
  %478 = phi i64* [ %468, %472 ], [ %423, %422 ]
  %479 = add nsw i64 %419, -1
  %480 = icmp eq i64 %479, 0
  br i1 %480, label %498, label %415

; <label>:481:                                    ; preds = %440
  %482 = landingpad { i8*, i32 }
          cleanup
  br label %485

; <label>:483:                                    ; preds = %438
  %484 = landingpad { i8*, i32 }
          cleanup
  br label %485

; <label>:485:                                    ; preds = %483, %481
  %486 = phi { i8*, i32 } [ %482, %481 ], [ %484, %483 ]
  %487 = extractvalue { i8*, i32 } %486, 0
  %488 = extractvalue { i8*, i32 } %486, 1
  %489 = load i64*, i64** %403, align 8, !tbaa !19, !alias.scope !29
  %490 = icmp eq i64* %489, null
  br i1 %490, label %493, label %491

; <label>:491:                                    ; preds = %485
  %492 = bitcast i64* %489 to i8*
  call void @_ZdlPv(i8* %492) #2
  br label %493

; <label>:493:                                    ; preds = %491, %485, %411
  %494 = phi i32 [ %414, %411 ], [ %488, %491 ], [ %488, %485 ]
  %495 = phi i8* [ %413, %411 ], [ %487, %491 ], [ %487, %485 ]
  %496 = insertvalue { i8*, i32 } undef, i8* %495, 0
  %497 = insertvalue { i8*, i32 } %496, i32 %494, 1
  br label %1389

; <label>:498:                                    ; preds = %475
  %499 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %500 unwind label %683

; <label>:500:                                    ; preds = %498
  %501 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %502 = load i64*, i64** %403, align 8, !tbaa !23
  %503 = load i64*, i64** %400, align 8, !tbaa !23
  %504 = icmp eq i64* %502, %503
  br i1 %504, label %513, label %505

; <label>:505:                                    ; preds = %500
  %506 = ptrtoint i64* %503 to i64
  %507 = ptrtoint i64* %502 to i64
  %508 = sub i64 %506, %507
  %509 = ashr i64 %508, 4
  %510 = call i64 @llvm.ctlz.i64(i64 %509, i1 false) #2, !range !24
  %511 = trunc i64 %510 to i32
  %512 = sub nsw i32 64, %511
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %502, i64* %503, i32 %512, i1 zeroext true)
          to label %513 unwind label %683

; <label>:513:                                    ; preds = %505, %500
  %514 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %515 = sub nsw i64 %514, %501
  %516 = sitofp i64 %515 to double
  %517 = fdiv double %516, 1.000000e+09
  %518 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %517)
          to label %519 unwind label %683

; <label>:519:                                    ; preds = %513
  %520 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %521 unwind label %683

; <label>:521:                                    ; preds = %519
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %18)
          to label %522 unwind label %683

; <label>:522:                                    ; preds = %521
  %523 = load i64*, i64** %403, align 8, !tbaa !19
  %524 = icmp eq i64* %523, null
  br i1 %524, label %527, label %525

; <label>:525:                                    ; preds = %522
  %526 = bitcast i64* %523 to i8*
  call void @_ZdlPv(i8* %526) #2
  br label %527

; <label>:527:                                    ; preds = %525, %522
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %398) #2
  %528 = bitcast %"class.std::vector"* %19 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %528) #2
  invoke void @_ZN13Int_Generator18reverse_sorted_endEmm(%"class.std::vector"* nonnull sret %19, i64 10000000, i64 1000000)
          to label %529 unwind label %1387

; <label>:529:                                    ; preds = %527
  %530 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %531 unwind label %692

; <label>:531:                                    ; preds = %529
  %532 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %533 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %19, i64 0, i32 0, i32 0, i32 0
  %534 = load i64*, i64** %533, align 8, !tbaa !23
  %535 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %19, i64 0, i32 0, i32 0, i32 1
  %536 = load i64*, i64** %535, align 8, !tbaa !23
  %537 = icmp eq i64* %534, %536
  br i1 %537, label %546, label %538

; <label>:538:                                    ; preds = %531
  %539 = ptrtoint i64* %536 to i64
  %540 = ptrtoint i64* %534 to i64
  %541 = sub i64 %539, %540
  %542 = ashr i64 %541, 4
  %543 = call i64 @llvm.ctlz.i64(i64 %542, i1 false) #2, !range !24
  %544 = trunc i64 %543 to i32
  %545 = sub nsw i32 64, %544
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %534, i64* %536, i32 %545, i1 zeroext true)
          to label %546 unwind label %692

; <label>:546:                                    ; preds = %538, %531
  %547 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %548 = sub nsw i64 %547, %532
  %549 = sitofp i64 %548 to double
  %550 = fdiv double %549, 1.000000e+09
  %551 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %550)
          to label %552 unwind label %692

; <label>:552:                                    ; preds = %546
  %553 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %554 unwind label %692

; <label>:554:                                    ; preds = %552
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %19)
          to label %555 unwind label %692

; <label>:555:                                    ; preds = %554
  %556 = load i64*, i64** %533, align 8, !tbaa !19
  %557 = icmp eq i64* %556, null
  br i1 %557, label %560, label %558

; <label>:558:                                    ; preds = %555
  %559 = bitcast i64* %556 to i8*
  call void @_ZdlPv(i8* %559) #2
  br label %560

; <label>:560:                                    ; preds = %558, %555
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %528) #2
  %561 = bitcast %"class.std::vector"* %20 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %561) #2
  invoke void @_ZN13Int_Generator21reverse_sorted_middleEmm(%"class.std::vector"* nonnull sret %20, i64 10000000, i64 1000000)
          to label %562 unwind label %1387

; <label>:562:                                    ; preds = %560
  %563 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %564 unwind label %702

; <label>:564:                                    ; preds = %562
  %565 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %566 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %20, i64 0, i32 0, i32 0, i32 0
  %567 = load i64*, i64** %566, align 8, !tbaa !23
  %568 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %20, i64 0, i32 0, i32 0, i32 1
  %569 = load i64*, i64** %568, align 8, !tbaa !23
  %570 = icmp eq i64* %567, %569
  br i1 %570, label %579, label %571

; <label>:571:                                    ; preds = %564
  %572 = ptrtoint i64* %569 to i64
  %573 = ptrtoint i64* %567 to i64
  %574 = sub i64 %572, %573
  %575 = ashr i64 %574, 4
  %576 = call i64 @llvm.ctlz.i64(i64 %575, i1 false) #2, !range !24
  %577 = trunc i64 %576 to i32
  %578 = sub nsw i32 64, %577
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %567, i64* %569, i32 %578, i1 zeroext true)
          to label %579 unwind label %702

; <label>:579:                                    ; preds = %571, %564
  %580 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %581 = sub nsw i64 %580, %565
  %582 = sitofp i64 %581 to double
  %583 = fdiv double %582, 1.000000e+09
  %584 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %583)
          to label %585 unwind label %702

; <label>:585:                                    ; preds = %579
  %586 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %587 unwind label %702

; <label>:587:                                    ; preds = %585
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %20)
          to label %588 unwind label %702

; <label>:588:                                    ; preds = %587
  %589 = load i64*, i64** %566, align 8, !tbaa !19
  %590 = icmp eq i64* %589, null
  br i1 %590, label %593, label %591

; <label>:591:                                    ; preds = %588
  %592 = bitcast i64* %589 to i8*
  call void @_ZdlPv(i8* %592) #2
  br label %593

; <label>:593:                                    ; preds = %591, %588
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %561) #2
  %594 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %595 = getelementptr i8, i8* %594, i64 -24
  %596 = bitcast i8* %595 to i64*
  %597 = load i64, i64* %596, align 8
  %598 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %597
  %599 = getelementptr inbounds i8, i8* %598, i64 240
  %600 = bitcast i8* %599 to %"class.std::ctype"**
  %601 = load %"class.std::ctype"*, %"class.std::ctype"** %600, align 8, !tbaa !8
  %602 = icmp eq %"class.std::ctype"* %601, null
  br i1 %602, label %603, label %605

; <label>:603:                                    ; preds = %593
  invoke void @_ZSt16__throw_bad_castv() #16
          to label %604 unwind label %1387

; <label>:604:                                    ; preds = %603
  unreachable

; <label>:605:                                    ; preds = %593
  %606 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %601, i64 0, i32 8
  %607 = load i8, i8* %606, align 8, !tbaa !12
  %608 = icmp eq i8 %607, 0
  br i1 %608, label %612, label %609

; <label>:609:                                    ; preds = %605
  %610 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %601, i64 0, i32 9, i64 10
  %611 = load i8, i8* %610, align 1, !tbaa !14
  br label %619

; <label>:612:                                    ; preds = %605
  invoke void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %601)
          to label %613 unwind label %1387

; <label>:613:                                    ; preds = %612
  %614 = bitcast %"class.std::ctype"* %601 to i8 (%"class.std::ctype"*, i8)***
  %615 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %614, align 8, !tbaa !6
  %616 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %615, i64 6
  %617 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %616, align 8
  %618 = invoke signext i8 %617(%"class.std::ctype"* nonnull %601, i8 signext 10)
          to label %619 unwind label %1387

; <label>:619:                                    ; preds = %613, %609
  %620 = phi i8 [ %611, %609 ], [ %618, %613 ]
  %621 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %620)
          to label %622 unwind label %1387

; <label>:622:                                    ; preds = %619
  %623 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %621)
          to label %717 unwind label %1387

; <label>:624:                                    ; preds = %129, %127, %121, %113, %104
  %625 = landingpad { i8*, i32 }
          cleanup
  %626 = extractvalue { i8*, i32 } %625, 0
  %627 = extractvalue { i8*, i32 } %625, 1
  %628 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %12, i64 0, i32 0, i32 0, i32 0
  %629 = load i64*, i64** %628, align 8, !tbaa !19
  %630 = icmp eq i64* %629, null
  br i1 %630, label %633, label %631

; <label>:631:                                    ; preds = %624
  %632 = bitcast i64* %629 to i8*
  call void @_ZdlPv(i8* %632) #2
  br label %633

; <label>:633:                                    ; preds = %631, %624
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %103) #2
  br label %712

; <label>:634:                                    ; preds = %162, %160, %154, %146, %137
  %635 = landingpad { i8*, i32 }
          cleanup
  %636 = extractvalue { i8*, i32 } %635, 0
  %637 = extractvalue { i8*, i32 } %635, 1
  %638 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %13, i64 0, i32 0, i32 0, i32 0
  %639 = load i64*, i64** %638, align 8, !tbaa !19
  %640 = icmp eq i64* %639, null
  br i1 %640, label %643, label %641

; <label>:641:                                    ; preds = %634
  %642 = bitcast i64* %639 to i8*
  call void @_ZdlPv(i8* %642) #2
  br label %643

; <label>:643:                                    ; preds = %641, %634
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %136) #2
  br label %712

; <label>:644:                                    ; preds = %292, %290, %284, %276, %269
  %645 = landingpad { i8*, i32 }
          cleanup
  %646 = extractvalue { i8*, i32 } %645, 0
  %647 = extractvalue { i8*, i32 } %645, 1
  %648 = load i64*, i64** %174, align 8, !tbaa !19
  %649 = icmp eq i64* %648, null
  br i1 %649, label %652, label %650

; <label>:650:                                    ; preds = %644
  %651 = bitcast i64* %648 to i8*
  call void @_ZdlPv(i8* %651) #2
  br label %652

; <label>:652:                                    ; preds = %650, %644
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %169) #2
  br label %712

; <label>:653:                                    ; preds = %325, %323, %317, %309, %300
  %654 = landingpad { i8*, i32 }
          cleanup
  %655 = extractvalue { i8*, i32 } %654, 0
  %656 = extractvalue { i8*, i32 } %654, 1
  %657 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %15, i64 0, i32 0, i32 0, i32 0
  %658 = load i64*, i64** %657, align 8, !tbaa !19
  %659 = icmp eq i64* %658, null
  br i1 %659, label %662, label %660

; <label>:660:                                    ; preds = %653
  %661 = bitcast i64* %658 to i8*
  call void @_ZdlPv(i8* %661) #2
  br label %662

; <label>:662:                                    ; preds = %660, %653
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %299) #2
  br label %712

; <label>:663:                                    ; preds = %358, %356, %350, %342, %333
  %664 = landingpad { i8*, i32 }
          cleanup
  %665 = extractvalue { i8*, i32 } %664, 0
  %666 = extractvalue { i8*, i32 } %664, 1
  %667 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %16, i64 0, i32 0, i32 0, i32 0
  %668 = load i64*, i64** %667, align 8, !tbaa !19
  %669 = icmp eq i64* %668, null
  br i1 %669, label %672, label %670

; <label>:670:                                    ; preds = %663
  %671 = bitcast i64* %668 to i8*
  call void @_ZdlPv(i8* %671) #2
  br label %672

; <label>:672:                                    ; preds = %670, %663
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %332) #2
  br label %712

; <label>:673:                                    ; preds = %391, %389, %383, %375, %366
  %674 = landingpad { i8*, i32 }
          cleanup
  %675 = extractvalue { i8*, i32 } %674, 0
  %676 = extractvalue { i8*, i32 } %674, 1
  %677 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %17, i64 0, i32 0, i32 0, i32 0
  %678 = load i64*, i64** %677, align 8, !tbaa !19
  %679 = icmp eq i64* %678, null
  br i1 %679, label %682, label %680

; <label>:680:                                    ; preds = %673
  %681 = bitcast i64* %678 to i8*
  call void @_ZdlPv(i8* %681) #2
  br label %682

; <label>:682:                                    ; preds = %680, %673
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %365) #2
  br label %712

; <label>:683:                                    ; preds = %521, %519, %513, %505, %498
  %684 = landingpad { i8*, i32 }
          cleanup
  %685 = extractvalue { i8*, i32 } %684, 0
  %686 = extractvalue { i8*, i32 } %684, 1
  %687 = load i64*, i64** %403, align 8, !tbaa !19
  %688 = icmp eq i64* %687, null
  br i1 %688, label %691, label %689

; <label>:689:                                    ; preds = %683
  %690 = bitcast i64* %687 to i8*
  call void @_ZdlPv(i8* %690) #2
  br label %691

; <label>:691:                                    ; preds = %689, %683
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %398) #2
  br label %712

; <label>:692:                                    ; preds = %554, %552, %546, %538, %529
  %693 = landingpad { i8*, i32 }
          cleanup
  %694 = extractvalue { i8*, i32 } %693, 0
  %695 = extractvalue { i8*, i32 } %693, 1
  %696 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %19, i64 0, i32 0, i32 0, i32 0
  %697 = load i64*, i64** %696, align 8, !tbaa !19
  %698 = icmp eq i64* %697, null
  br i1 %698, label %701, label %699

; <label>:699:                                    ; preds = %692
  %700 = bitcast i64* %697 to i8*
  call void @_ZdlPv(i8* %700) #2
  br label %701

; <label>:701:                                    ; preds = %699, %692
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %528) #2
  br label %712

; <label>:702:                                    ; preds = %587, %585, %579, %571, %562
  %703 = landingpad { i8*, i32 }
          cleanup
  %704 = extractvalue { i8*, i32 } %703, 0
  %705 = extractvalue { i8*, i32 } %703, 1
  %706 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %20, i64 0, i32 0, i32 0, i32 0
  %707 = load i64*, i64** %706, align 8, !tbaa !19
  %708 = icmp eq i64* %707, null
  br i1 %708, label %711, label %709

; <label>:709:                                    ; preds = %702
  %710 = bitcast i64* %707 to i8*
  call void @_ZdlPv(i8* %710) #2
  br label %711

; <label>:711:                                    ; preds = %709, %702
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %561) #2
  br label %712

; <label>:712:                                    ; preds = %711, %701, %691, %682, %672, %662, %652, %643, %633
  %713 = phi i32 [ %705, %711 ], [ %695, %701 ], [ %686, %691 ], [ %676, %682 ], [ %666, %672 ], [ %656, %662 ], [ %647, %652 ], [ %637, %643 ], [ %627, %633 ]
  %714 = phi i8* [ %704, %711 ], [ %694, %701 ], [ %685, %691 ], [ %675, %682 ], [ %665, %672 ], [ %655, %662 ], [ %646, %652 ], [ %636, %643 ], [ %626, %633 ]
  %715 = insertvalue { i8*, i32 } undef, i8* %714, 0
  %716 = insertvalue { i8*, i32 } %715, i32 %713, 1
  br label %1389

; <label>:717:                                    ; preds = %622
  %718 = load i8*, i8** %62, align 8, !tbaa !32
  %719 = icmp eq i8* %718, %59
  br i1 %719, label %721, label %720

; <label>:720:                                    ; preds = %717
  call void @_ZdlPv(i8* %718) #2
  br label %721

; <label>:721:                                    ; preds = %717, %720
  %722 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %23, i64 0, i32 2
  %723 = bitcast %"class.std::__cxx11::basic_string"* %23 to %union.anon**
  store %union.anon* %722, %union.anon** %723, align 8, !tbaa !15
  %724 = bitcast %union.anon* %722 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %724, i8* nonnull getelementptr inbounds ([8 x i8], [8 x i8]* @.str.2, i64 0, i64 0), i64 7, i32 1, i1 false) #2
  %725 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %23, i64 0, i32 1
  store i64 7, i64* %725, align 8, !tbaa !17
  %726 = getelementptr inbounds i8, i8* %724, i64 7
  store i8 0, i8* %726, align 1, !tbaa !14
  %727 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %23, i64 0, i32 0, i32 0
  %728 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull %724, i64 7)
          to label %729 unwind label %1396

; <label>:729:                                    ; preds = %721
  %730 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) %728, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i64 1)
          to label %731 unwind label %1396

; <label>:731:                                    ; preds = %729
  %732 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %733 unwind label %1396

; <label>:733:                                    ; preds = %731
  %734 = bitcast %"class.std::vector"* %3 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %734) #2
  invoke void @_ZN13Int_Generator6randomEm(%"class.std::vector"* nonnull sret %3, i64 10000000)
          to label %735 unwind label %1396

; <label>:735:                                    ; preds = %733
  %736 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %737 unwind label %1289

; <label>:737:                                    ; preds = %735
  %738 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %739 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %3, i64 0, i32 0, i32 0, i32 0
  %740 = load i64*, i64** %739, align 8, !tbaa !19
  %741 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %3, i64 0, i32 0, i32 0, i32 1
  %742 = bitcast i64** %741 to i64*
  %743 = load i64, i64* %742, align 8, !tbaa !22
  %744 = ptrtoint i64* %740 to i64
  %745 = sub i64 %743, %744
  %746 = ashr exact i64 %745, 3
  %747 = icmp eq i64 %745, 0
  br i1 %747, label %756, label %748

; <label>:748:                                    ; preds = %737
  br label %749

; <label>:749:                                    ; preds = %748, %749
  %750 = phi i64 [ %752, %749 ], [ %746, %748 ]
  %751 = phi i32 [ %754, %749 ], [ 0, %748 ]
  %752 = lshr i64 %750, 1
  %753 = icmp eq i64 %752, 0
  %754 = add nuw nsw i32 %751, 1
  br i1 %753, label %755, label %749

; <label>:755:                                    ; preds = %749
  invoke void @_Z11pdqsort_recPmmmib(i64* %740, i64 0, i64 %746, i32 %751, i1 zeroext true)
          to label %756 unwind label %1289

; <label>:756:                                    ; preds = %755, %737
  %757 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %758 = sub nsw i64 %757, %738
  %759 = sitofp i64 %758 to double
  %760 = fdiv double %759, 1.000000e+09
  %761 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %760)
          to label %762 unwind label %1289

; <label>:762:                                    ; preds = %756
  %763 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %764 unwind label %1289

; <label>:764:                                    ; preds = %762
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %3)
          to label %765 unwind label %1289

; <label>:765:                                    ; preds = %764
  %766 = load i64*, i64** %739, align 8, !tbaa !19
  %767 = icmp eq i64* %766, null
  br i1 %767, label %770, label %768

; <label>:768:                                    ; preds = %765
  %769 = bitcast i64* %766 to i8*
  call void @_ZdlPv(i8* %769) #2
  br label %770

; <label>:770:                                    ; preds = %768, %765
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %734) #2
  %771 = bitcast %"class.std::vector"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %771) #2
  invoke void @_ZN13Int_Generator10random_dupEmm(%"class.std::vector"* nonnull sret %4, i64 10000000, i64 10000)
          to label %772 unwind label %1396

; <label>:772:                                    ; preds = %770
  %773 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %774 unwind label %1299

; <label>:774:                                    ; preds = %772
  %775 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %776 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %777 = load i64*, i64** %776, align 8, !tbaa !19
  %778 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %779 = bitcast i64** %778 to i64*
  %780 = load i64, i64* %779, align 8, !tbaa !22
  %781 = ptrtoint i64* %777 to i64
  %782 = sub i64 %780, %781
  %783 = ashr exact i64 %782, 3
  %784 = icmp eq i64 %782, 0
  br i1 %784, label %793, label %785

; <label>:785:                                    ; preds = %774
  br label %786

; <label>:786:                                    ; preds = %785, %786
  %787 = phi i64 [ %789, %786 ], [ %783, %785 ]
  %788 = phi i32 [ %791, %786 ], [ 0, %785 ]
  %789 = lshr i64 %787, 1
  %790 = icmp eq i64 %789, 0
  %791 = add nuw nsw i32 %788, 1
  br i1 %790, label %792, label %786

; <label>:792:                                    ; preds = %786
  invoke void @_Z11pdqsort_recPmmmib(i64* %777, i64 0, i64 %783, i32 %788, i1 zeroext true)
          to label %793 unwind label %1299

; <label>:793:                                    ; preds = %792, %774
  %794 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %795 = sub nsw i64 %794, %775
  %796 = sitofp i64 %795 to double
  %797 = fdiv double %796, 1.000000e+09
  %798 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %797)
          to label %799 unwind label %1299

; <label>:799:                                    ; preds = %793
  %800 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %801 unwind label %1299

; <label>:801:                                    ; preds = %799
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %4)
          to label %802 unwind label %1299

; <label>:802:                                    ; preds = %801
  %803 = load i64*, i64** %776, align 8, !tbaa !19
  %804 = icmp eq i64* %803, null
  br i1 %804, label %807, label %805

; <label>:805:                                    ; preds = %802
  %806 = bitcast i64* %803 to i8*
  call void @_ZdlPv(i8* %806) #2
  br label %807

; <label>:807:                                    ; preds = %805, %802
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %771) #2
  %808 = bitcast %"class.std::vector"* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %808) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %808, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !33
  %809 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %5, i64 0, i32 0, i32 0, i32 2
  %810 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %5, i64 0, i32 0, i32 0, i32 1
  %811 = invoke i8* @_Znwm(i64 800000000)
          to label %812 unwind label %821, !noalias !33

; <label>:812:                                    ; preds = %807
  %813 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %5, i64 0, i32 0, i32 0, i32 0
  %814 = bitcast %"class.std::vector"* %5 to i8**
  store i8* %811, i8** %814, align 8, !tbaa !19, !alias.scope !33
  %815 = getelementptr inbounds i8, i8* %811, i64 800000000
  %816 = bitcast i64** %809 to i8**
  store i8* %815, i8** %816, align 8, !tbaa !28, !alias.scope !33
  %817 = ptrtoint i8* %811 to i64
  %818 = bitcast i64** %810 to i64*
  store i64 %817, i64* %818, align 8, !tbaa !22, !alias.scope !33
  %819 = bitcast i8* %811 to i64*
  %820 = bitcast i8* %815 to i64*
  br label %825

; <label>:821:                                    ; preds = %807
  %822 = landingpad { i8*, i32 }
          cleanup
  %823 = extractvalue { i8*, i32 } %822, 0
  %824 = extractvalue { i8*, i32 } %822, 1
  br label %903

; <label>:825:                                    ; preds = %885, %812
  %826 = phi i64 [ %817, %812 ], [ %886, %885 ]
  %827 = phi i64* [ %820, %812 ], [ %887, %885 ]
  %828 = phi i64* [ %819, %812 ], [ %888, %885 ]
  %829 = phi i64 [ 0, %812 ], [ %889, %885 ]
  %830 = icmp eq i64* %828, %827
  %831 = ptrtoint i64* %828 to i64
  br i1 %830, label %834, label %832

; <label>:832:                                    ; preds = %825
  store i64 %829, i64* %828, align 8, !tbaa !2
  %833 = getelementptr inbounds i64, i64* %828, i64 1
  store i64* %833, i64** %810, align 8, !tbaa !22
  br label %885

; <label>:834:                                    ; preds = %825
  %835 = sub i64 %831, %826
  %836 = ashr exact i64 %835, 3
  %837 = icmp eq i64 %835, 0
  %838 = select i1 %837, i64 1, i64 %836
  %839 = add nsw i64 %838, %836
  %840 = icmp ult i64 %839, %836
  %841 = icmp ugt i64 %839, 2305843009213693951
  %842 = or i1 %840, %841
  %843 = select i1 %842, i64 2305843009213693951, i64 %839
  %844 = icmp eq i64 %843, 0
  %845 = inttoptr i64 %826 to i64*
  br i1 %844, label %856, label %846

; <label>:846:                                    ; preds = %834
  %847 = icmp ugt i64 %843, 2305843009213693951
  br i1 %847, label %848, label %850

; <label>:848:                                    ; preds = %846
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %849 unwind label %893

; <label>:849:                                    ; preds = %848
  unreachable

; <label>:850:                                    ; preds = %846
  %851 = shl i64 %843, 3
  %852 = invoke i8* @_Znwm(i64 %851)
          to label %853 unwind label %891

; <label>:853:                                    ; preds = %850
  %854 = bitcast i8* %852 to i64*
  %855 = load i64*, i64** %813, align 8, !tbaa !19
  br label %856

; <label>:856:                                    ; preds = %853, %834
  %857 = phi i64* [ %855, %853 ], [ %845, %834 ]
  %858 = phi i8* [ %852, %853 ], [ null, %834 ]
  %859 = phi i64* [ %854, %853 ], [ null, %834 ]
  %860 = getelementptr inbounds i64, i64* %859, i64 %836
  store i64 %829, i64* %860, align 8, !tbaa !2
  %861 = ptrtoint i64* %857 to i64
  %862 = sub i64 %831, %861
  %863 = ashr exact i64 %862, 3
  %864 = icmp eq i64 %862, 0
  br i1 %864, label %867, label %865

; <label>:865:                                    ; preds = %856
  %866 = bitcast i64* %857 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %858, i8* %866, i64 %862, i32 8, i1 false) #2
  br label %867

; <label>:867:                                    ; preds = %865, %856
  %868 = getelementptr inbounds i64, i64* %859, i64 %863
  %869 = getelementptr inbounds i64, i64* %868, i64 1
  %870 = load i64, i64* %818, align 8, !tbaa !22
  %871 = sub i64 %870, %831
  %872 = ashr exact i64 %871, 3
  %873 = icmp eq i64 %871, 0
  br i1 %873, label %877, label %874

; <label>:874:                                    ; preds = %867
  %875 = bitcast i64* %869 to i8*
  %876 = bitcast i64* %827 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %875, i8* %876, i64 %871, i32 8, i1 false) #2
  br label %877

; <label>:877:                                    ; preds = %874, %867
  %878 = getelementptr inbounds i64, i64* %869, i64 %872
  %879 = icmp eq i64* %857, null
  br i1 %879, label %882, label %880

; <label>:880:                                    ; preds = %877
  %881 = bitcast i64* %857 to i8*
  call void @_ZdlPv(i8* %881) #2
  br label %882

; <label>:882:                                    ; preds = %880, %877
  store i8* %858, i8** %814, align 8, !tbaa !19
  store i64* %878, i64** %810, align 8, !tbaa !22
  %883 = getelementptr inbounds i64, i64* %859, i64 %843
  store i64* %883, i64** %809, align 8, !tbaa !28
  %884 = ptrtoint i8* %858 to i64
  br label %885

; <label>:885:                                    ; preds = %882, %832
  %886 = phi i64 [ %884, %882 ], [ %826, %832 ]
  %887 = phi i64* [ %883, %882 ], [ %827, %832 ]
  %888 = phi i64* [ %878, %882 ], [ %833, %832 ]
  %889 = add nuw nsw i64 %829, 1
  %890 = icmp ult i64 %889, 100000000
  br i1 %890, label %825, label %908

; <label>:891:                                    ; preds = %850
  %892 = landingpad { i8*, i32 }
          cleanup
  br label %895

; <label>:893:                                    ; preds = %848
  %894 = landingpad { i8*, i32 }
          cleanup
  br label %895

; <label>:895:                                    ; preds = %893, %891
  %896 = phi { i8*, i32 } [ %892, %891 ], [ %894, %893 ]
  %897 = extractvalue { i8*, i32 } %896, 0
  %898 = extractvalue { i8*, i32 } %896, 1
  %899 = load i64*, i64** %813, align 8, !tbaa !19, !alias.scope !33
  %900 = icmp eq i64* %899, null
  br i1 %900, label %903, label %901

; <label>:901:                                    ; preds = %895
  %902 = bitcast i64* %899 to i8*
  call void @_ZdlPv(i8* %902) #2
  br label %903

; <label>:903:                                    ; preds = %901, %895, %821
  %904 = phi i32 [ %824, %821 ], [ %898, %901 ], [ %898, %895 ]
  %905 = phi i8* [ %823, %821 ], [ %897, %901 ], [ %897, %895 ]
  %906 = insertvalue { i8*, i32 } undef, i8* %905, 0
  %907 = insertvalue { i8*, i32 } %906, i32 %904, 1
  br label %1398

; <label>:908:                                    ; preds = %885
  %909 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %910 unwind label %1309

; <label>:910:                                    ; preds = %908
  %911 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %912 = load i64*, i64** %813, align 8, !tbaa !19
  %913 = load i64, i64* %818, align 8, !tbaa !22
  %914 = ptrtoint i64* %912 to i64
  %915 = sub i64 %913, %914
  %916 = ashr exact i64 %915, 3
  %917 = icmp eq i64 %915, 0
  br i1 %917, label %926, label %918

; <label>:918:                                    ; preds = %910
  br label %919

; <label>:919:                                    ; preds = %918, %919
  %920 = phi i64 [ %922, %919 ], [ %916, %918 ]
  %921 = phi i32 [ %924, %919 ], [ 0, %918 ]
  %922 = lshr i64 %920, 1
  %923 = icmp eq i64 %922, 0
  %924 = add nuw nsw i32 %921, 1
  br i1 %923, label %925, label %919

; <label>:925:                                    ; preds = %919
  invoke void @_Z11pdqsort_recPmmmib(i64* %912, i64 0, i64 %916, i32 %921, i1 zeroext true)
          to label %926 unwind label %1309

; <label>:926:                                    ; preds = %925, %910
  %927 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %928 = sub nsw i64 %927, %911
  %929 = sitofp i64 %928 to double
  %930 = fdiv double %929, 1.000000e+09
  %931 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %930)
          to label %932 unwind label %1309

; <label>:932:                                    ; preds = %926
  %933 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %934 unwind label %1309

; <label>:934:                                    ; preds = %932
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %5)
          to label %935 unwind label %1309

; <label>:935:                                    ; preds = %934
  %936 = load i64*, i64** %813, align 8, !tbaa !19
  %937 = icmp eq i64* %936, null
  br i1 %937, label %940, label %938

; <label>:938:                                    ; preds = %935
  %939 = bitcast i64* %936 to i8*
  call void @_ZdlPv(i8* %939) #2
  br label %940

; <label>:940:                                    ; preds = %938, %935
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %808) #2
  %941 = bitcast %"class.std::vector"* %6 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %941) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %6, i64 10000000, i64 100000)
          to label %942 unwind label %1396

; <label>:942:                                    ; preds = %940
  %943 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %944 unwind label %1318

; <label>:944:                                    ; preds = %942
  %945 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %946 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %6, i64 0, i32 0, i32 0, i32 0
  %947 = load i64*, i64** %946, align 8, !tbaa !19
  %948 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %6, i64 0, i32 0, i32 0, i32 1
  %949 = bitcast i64** %948 to i64*
  %950 = load i64, i64* %949, align 8, !tbaa !22
  %951 = ptrtoint i64* %947 to i64
  %952 = sub i64 %950, %951
  %953 = ashr exact i64 %952, 3
  %954 = icmp eq i64 %952, 0
  br i1 %954, label %963, label %955

; <label>:955:                                    ; preds = %944
  br label %956

; <label>:956:                                    ; preds = %955, %956
  %957 = phi i64 [ %959, %956 ], [ %953, %955 ]
  %958 = phi i32 [ %961, %956 ], [ 0, %955 ]
  %959 = lshr i64 %957, 1
  %960 = icmp eq i64 %959, 0
  %961 = add nuw nsw i32 %958, 1
  br i1 %960, label %962, label %956

; <label>:962:                                    ; preds = %956
  invoke void @_Z11pdqsort_recPmmmib(i64* %947, i64 0, i64 %953, i32 %958, i1 zeroext true)
          to label %963 unwind label %1318

; <label>:963:                                    ; preds = %962, %944
  %964 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %965 = sub nsw i64 %964, %945
  %966 = sitofp i64 %965 to double
  %967 = fdiv double %966, 1.000000e+09
  %968 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %967)
          to label %969 unwind label %1318

; <label>:969:                                    ; preds = %963
  %970 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %971 unwind label %1318

; <label>:971:                                    ; preds = %969
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %6)
          to label %972 unwind label %1318

; <label>:972:                                    ; preds = %971
  %973 = load i64*, i64** %946, align 8, !tbaa !19
  %974 = icmp eq i64* %973, null
  br i1 %974, label %977, label %975

; <label>:975:                                    ; preds = %972
  %976 = bitcast i64* %973 to i8*
  call void @_ZdlPv(i8* %976) #2
  br label %977

; <label>:977:                                    ; preds = %975, %972
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %941) #2
  %978 = bitcast %"class.std::vector"* %7 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %978) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %7, i64 10000000, i64 1000000)
          to label %979 unwind label %1396

; <label>:979:                                    ; preds = %977
  %980 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %981 unwind label %1328

; <label>:981:                                    ; preds = %979
  %982 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %983 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %7, i64 0, i32 0, i32 0, i32 0
  %984 = load i64*, i64** %983, align 8, !tbaa !19
  %985 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %7, i64 0, i32 0, i32 0, i32 1
  %986 = bitcast i64** %985 to i64*
  %987 = load i64, i64* %986, align 8, !tbaa !22
  %988 = ptrtoint i64* %984 to i64
  %989 = sub i64 %987, %988
  %990 = ashr exact i64 %989, 3
  %991 = icmp eq i64 %989, 0
  br i1 %991, label %1000, label %992

; <label>:992:                                    ; preds = %981
  br label %993

; <label>:993:                                    ; preds = %992, %993
  %994 = phi i64 [ %996, %993 ], [ %990, %992 ]
  %995 = phi i32 [ %998, %993 ], [ 0, %992 ]
  %996 = lshr i64 %994, 1
  %997 = icmp eq i64 %996, 0
  %998 = add nuw nsw i32 %995, 1
  br i1 %997, label %999, label %993

; <label>:999:                                    ; preds = %993
  invoke void @_Z11pdqsort_recPmmmib(i64* %984, i64 0, i64 %990, i32 %995, i1 zeroext true)
          to label %1000 unwind label %1328

; <label>:1000:                                   ; preds = %999, %981
  %1001 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1002 = sub nsw i64 %1001, %982
  %1003 = sitofp i64 %1002 to double
  %1004 = fdiv double %1003, 1.000000e+09
  %1005 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1004)
          to label %1006 unwind label %1328

; <label>:1006:                                   ; preds = %1000
  %1007 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1008 unwind label %1328

; <label>:1008:                                   ; preds = %1006
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %7)
          to label %1009 unwind label %1328

; <label>:1009:                                   ; preds = %1008
  %1010 = load i64*, i64** %983, align 8, !tbaa !19
  %1011 = icmp eq i64* %1010, null
  br i1 %1011, label %1014, label %1012

; <label>:1012:                                   ; preds = %1009
  %1013 = bitcast i64* %1010 to i8*
  call void @_ZdlPv(i8* %1013) #2
  br label %1014

; <label>:1014:                                   ; preds = %1012, %1009
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %978) #2
  %1015 = bitcast %"class.std::vector"* %8 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1015) #2
  invoke void @_ZN13Int_Generator13sorted_middleEmm(%"class.std::vector"* nonnull sret %8, i64 10000000, i64 1000000)
          to label %1016 unwind label %1396

; <label>:1016:                                   ; preds = %1014
  %1017 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1018 unwind label %1338

; <label>:1018:                                   ; preds = %1016
  %1019 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1020 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %8, i64 0, i32 0, i32 0, i32 0
  %1021 = load i64*, i64** %1020, align 8, !tbaa !19
  %1022 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %8, i64 0, i32 0, i32 0, i32 1
  %1023 = bitcast i64** %1022 to i64*
  %1024 = load i64, i64* %1023, align 8, !tbaa !22
  %1025 = ptrtoint i64* %1021 to i64
  %1026 = sub i64 %1024, %1025
  %1027 = ashr exact i64 %1026, 3
  %1028 = icmp eq i64 %1026, 0
  br i1 %1028, label %1037, label %1029

; <label>:1029:                                   ; preds = %1018
  br label %1030

; <label>:1030:                                   ; preds = %1029, %1030
  %1031 = phi i64 [ %1033, %1030 ], [ %1027, %1029 ]
  %1032 = phi i32 [ %1035, %1030 ], [ 0, %1029 ]
  %1033 = lshr i64 %1031, 1
  %1034 = icmp eq i64 %1033, 0
  %1035 = add nuw nsw i32 %1032, 1
  br i1 %1034, label %1036, label %1030

; <label>:1036:                                   ; preds = %1030
  invoke void @_Z11pdqsort_recPmmmib(i64* %1021, i64 0, i64 %1027, i32 %1032, i1 zeroext true)
          to label %1037 unwind label %1338

; <label>:1037:                                   ; preds = %1036, %1018
  %1038 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1039 = sub nsw i64 %1038, %1019
  %1040 = sitofp i64 %1039 to double
  %1041 = fdiv double %1040, 1.000000e+09
  %1042 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1041)
          to label %1043 unwind label %1338

; <label>:1043:                                   ; preds = %1037
  %1044 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1045 unwind label %1338

; <label>:1045:                                   ; preds = %1043
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %8)
          to label %1046 unwind label %1338

; <label>:1046:                                   ; preds = %1045
  %1047 = load i64*, i64** %1020, align 8, !tbaa !19
  %1048 = icmp eq i64* %1047, null
  br i1 %1048, label %1051, label %1049

; <label>:1049:                                   ; preds = %1046
  %1050 = bitcast i64* %1047 to i8*
  call void @_ZdlPv(i8* %1050) #2
  br label %1051

; <label>:1051:                                   ; preds = %1049, %1046
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1015) #2
  %1052 = bitcast %"class.std::vector"* %9 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1052) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %1052, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !36
  %1053 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %9, i64 0, i32 0, i32 0, i32 2
  %1054 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %9, i64 0, i32 0, i32 0, i32 1
  %1055 = invoke i8* @_Znwm(i64 800000000)
          to label %1056 unwind label %1065, !noalias !36

; <label>:1056:                                   ; preds = %1051
  %1057 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %9, i64 0, i32 0, i32 0, i32 0
  %1058 = bitcast %"class.std::vector"* %9 to i8**
  store i8* %1055, i8** %1058, align 8, !tbaa !19, !alias.scope !36
  %1059 = getelementptr inbounds i8, i8* %1055, i64 800000000
  %1060 = bitcast i64** %1053 to i8**
  store i8* %1059, i8** %1060, align 8, !tbaa !28, !alias.scope !36
  %1061 = ptrtoint i8* %1055 to i64
  %1062 = bitcast i64** %1054 to i64*
  store i64 %1061, i64* %1062, align 8, !tbaa !22, !alias.scope !36
  %1063 = bitcast i8* %1055 to i64*
  %1064 = bitcast i8* %1059 to i64*
  br label %1069

; <label>:1065:                                   ; preds = %1051
  %1066 = landingpad { i8*, i32 }
          cleanup
  %1067 = extractvalue { i8*, i32 } %1066, 0
  %1068 = extractvalue { i8*, i32 } %1066, 1
  br label %1147

; <label>:1069:                                   ; preds = %1129, %1056
  %1070 = phi i64 [ %1061, %1056 ], [ %1130, %1129 ]
  %1071 = phi i64* [ %1064, %1056 ], [ %1131, %1129 ]
  %1072 = phi i64* [ %1063, %1056 ], [ %1132, %1129 ]
  %1073 = phi i64 [ 100000000, %1056 ], [ %1133, %1129 ]
  %1074 = icmp eq i64* %1072, %1071
  %1075 = ptrtoint i64* %1072 to i64
  br i1 %1074, label %1078, label %1076

; <label>:1076:                                   ; preds = %1069
  store i64 %1073, i64* %1072, align 8, !tbaa !2
  %1077 = getelementptr inbounds i64, i64* %1072, i64 1
  store i64* %1077, i64** %1054, align 8, !tbaa !22
  br label %1129

; <label>:1078:                                   ; preds = %1069
  %1079 = sub i64 %1075, %1070
  %1080 = ashr exact i64 %1079, 3
  %1081 = icmp eq i64 %1079, 0
  %1082 = select i1 %1081, i64 1, i64 %1080
  %1083 = add nsw i64 %1082, %1080
  %1084 = icmp ult i64 %1083, %1080
  %1085 = icmp ugt i64 %1083, 2305843009213693951
  %1086 = or i1 %1084, %1085
  %1087 = select i1 %1086, i64 2305843009213693951, i64 %1083
  %1088 = icmp eq i64 %1087, 0
  %1089 = inttoptr i64 %1070 to i64*
  br i1 %1088, label %1100, label %1090

; <label>:1090:                                   ; preds = %1078
  %1091 = icmp ugt i64 %1087, 2305843009213693951
  br i1 %1091, label %1092, label %1094

; <label>:1092:                                   ; preds = %1090
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %1093 unwind label %1137

; <label>:1093:                                   ; preds = %1092
  unreachable

; <label>:1094:                                   ; preds = %1090
  %1095 = shl i64 %1087, 3
  %1096 = invoke i8* @_Znwm(i64 %1095)
          to label %1097 unwind label %1135

; <label>:1097:                                   ; preds = %1094
  %1098 = bitcast i8* %1096 to i64*
  %1099 = load i64*, i64** %1057, align 8, !tbaa !19
  br label %1100

; <label>:1100:                                   ; preds = %1097, %1078
  %1101 = phi i64* [ %1099, %1097 ], [ %1089, %1078 ]
  %1102 = phi i8* [ %1096, %1097 ], [ null, %1078 ]
  %1103 = phi i64* [ %1098, %1097 ], [ null, %1078 ]
  %1104 = getelementptr inbounds i64, i64* %1103, i64 %1080
  store i64 %1073, i64* %1104, align 8, !tbaa !2
  %1105 = ptrtoint i64* %1101 to i64
  %1106 = sub i64 %1075, %1105
  %1107 = ashr exact i64 %1106, 3
  %1108 = icmp eq i64 %1106, 0
  br i1 %1108, label %1111, label %1109

; <label>:1109:                                   ; preds = %1100
  %1110 = bitcast i64* %1101 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %1102, i8* %1110, i64 %1106, i32 8, i1 false) #2
  br label %1111

; <label>:1111:                                   ; preds = %1109, %1100
  %1112 = getelementptr inbounds i64, i64* %1103, i64 %1107
  %1113 = getelementptr inbounds i64, i64* %1112, i64 1
  %1114 = load i64, i64* %1062, align 8, !tbaa !22
  %1115 = sub i64 %1114, %1075
  %1116 = ashr exact i64 %1115, 3
  %1117 = icmp eq i64 %1115, 0
  br i1 %1117, label %1121, label %1118

; <label>:1118:                                   ; preds = %1111
  %1119 = bitcast i64* %1113 to i8*
  %1120 = bitcast i64* %1071 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %1119, i8* %1120, i64 %1115, i32 8, i1 false) #2
  br label %1121

; <label>:1121:                                   ; preds = %1118, %1111
  %1122 = getelementptr inbounds i64, i64* %1113, i64 %1116
  %1123 = icmp eq i64* %1101, null
  br i1 %1123, label %1126, label %1124

; <label>:1124:                                   ; preds = %1121
  %1125 = bitcast i64* %1101 to i8*
  call void @_ZdlPv(i8* %1125) #2
  br label %1126

; <label>:1126:                                   ; preds = %1124, %1121
  store i8* %1102, i8** %1058, align 8, !tbaa !19
  store i64* %1122, i64** %1054, align 8, !tbaa !22
  %1127 = getelementptr inbounds i64, i64* %1103, i64 %1087
  store i64* %1127, i64** %1053, align 8, !tbaa !28
  %1128 = ptrtoint i8* %1102 to i64
  br label %1129

; <label>:1129:                                   ; preds = %1126, %1076
  %1130 = phi i64 [ %1128, %1126 ], [ %1070, %1076 ]
  %1131 = phi i64* [ %1127, %1126 ], [ %1071, %1076 ]
  %1132 = phi i64* [ %1122, %1126 ], [ %1077, %1076 ]
  %1133 = add nsw i64 %1073, -1
  %1134 = icmp eq i64 %1133, 0
  br i1 %1134, label %1152, label %1069

; <label>:1135:                                   ; preds = %1094
  %1136 = landingpad { i8*, i32 }
          cleanup
  br label %1139

; <label>:1137:                                   ; preds = %1092
  %1138 = landingpad { i8*, i32 }
          cleanup
  br label %1139

; <label>:1139:                                   ; preds = %1137, %1135
  %1140 = phi { i8*, i32 } [ %1136, %1135 ], [ %1138, %1137 ]
  %1141 = extractvalue { i8*, i32 } %1140, 0
  %1142 = extractvalue { i8*, i32 } %1140, 1
  %1143 = load i64*, i64** %1057, align 8, !tbaa !19, !alias.scope !36
  %1144 = icmp eq i64* %1143, null
  br i1 %1144, label %1147, label %1145

; <label>:1145:                                   ; preds = %1139
  %1146 = bitcast i64* %1143 to i8*
  call void @_ZdlPv(i8* %1146) #2
  br label %1147

; <label>:1147:                                   ; preds = %1145, %1139, %1065
  %1148 = phi i32 [ %1068, %1065 ], [ %1142, %1145 ], [ %1142, %1139 ]
  %1149 = phi i8* [ %1067, %1065 ], [ %1141, %1145 ], [ %1141, %1139 ]
  %1150 = insertvalue { i8*, i32 } undef, i8* %1149, 0
  %1151 = insertvalue { i8*, i32 } %1150, i32 %1148, 1
  br label %1398

; <label>:1152:                                   ; preds = %1129
  %1153 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1154 unwind label %1348

; <label>:1154:                                   ; preds = %1152
  %1155 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1156 = load i64*, i64** %1057, align 8, !tbaa !19
  %1157 = load i64, i64* %1062, align 8, !tbaa !22
  %1158 = ptrtoint i64* %1156 to i64
  %1159 = sub i64 %1157, %1158
  %1160 = ashr exact i64 %1159, 3
  %1161 = icmp eq i64 %1159, 0
  br i1 %1161, label %1170, label %1162

; <label>:1162:                                   ; preds = %1154
  br label %1163

; <label>:1163:                                   ; preds = %1162, %1163
  %1164 = phi i64 [ %1166, %1163 ], [ %1160, %1162 ]
  %1165 = phi i32 [ %1168, %1163 ], [ 0, %1162 ]
  %1166 = lshr i64 %1164, 1
  %1167 = icmp eq i64 %1166, 0
  %1168 = add nuw nsw i32 %1165, 1
  br i1 %1167, label %1169, label %1163

; <label>:1169:                                   ; preds = %1163
  invoke void @_Z11pdqsort_recPmmmib(i64* %1156, i64 0, i64 %1160, i32 %1165, i1 zeroext true)
          to label %1170 unwind label %1348

; <label>:1170:                                   ; preds = %1169, %1154
  %1171 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1172 = sub nsw i64 %1171, %1155
  %1173 = sitofp i64 %1172 to double
  %1174 = fdiv double %1173, 1.000000e+09
  %1175 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1174)
          to label %1176 unwind label %1348

; <label>:1176:                                   ; preds = %1170
  %1177 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1178 unwind label %1348

; <label>:1178:                                   ; preds = %1176
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %9)
          to label %1179 unwind label %1348

; <label>:1179:                                   ; preds = %1178
  %1180 = load i64*, i64** %1057, align 8, !tbaa !19
  %1181 = icmp eq i64* %1180, null
  br i1 %1181, label %1184, label %1182

; <label>:1182:                                   ; preds = %1179
  %1183 = bitcast i64* %1180 to i8*
  call void @_ZdlPv(i8* %1183) #2
  br label %1184

; <label>:1184:                                   ; preds = %1182, %1179
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1052) #2
  %1185 = bitcast %"class.std::vector"* %10 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1185) #2
  invoke void @_ZN13Int_Generator18reverse_sorted_endEmm(%"class.std::vector"* nonnull sret %10, i64 10000000, i64 1000000)
          to label %1186 unwind label %1396

; <label>:1186:                                   ; preds = %1184
  %1187 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1188 unwind label %1357

; <label>:1188:                                   ; preds = %1186
  %1189 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1190 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %10, i64 0, i32 0, i32 0, i32 0
  %1191 = load i64*, i64** %1190, align 8, !tbaa !19
  %1192 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %10, i64 0, i32 0, i32 0, i32 1
  %1193 = bitcast i64** %1192 to i64*
  %1194 = load i64, i64* %1193, align 8, !tbaa !22
  %1195 = ptrtoint i64* %1191 to i64
  %1196 = sub i64 %1194, %1195
  %1197 = ashr exact i64 %1196, 3
  %1198 = icmp eq i64 %1196, 0
  br i1 %1198, label %1207, label %1199

; <label>:1199:                                   ; preds = %1188
  br label %1200

; <label>:1200:                                   ; preds = %1199, %1200
  %1201 = phi i64 [ %1203, %1200 ], [ %1197, %1199 ]
  %1202 = phi i32 [ %1205, %1200 ], [ 0, %1199 ]
  %1203 = lshr i64 %1201, 1
  %1204 = icmp eq i64 %1203, 0
  %1205 = add nuw nsw i32 %1202, 1
  br i1 %1204, label %1206, label %1200

; <label>:1206:                                   ; preds = %1200
  invoke void @_Z11pdqsort_recPmmmib(i64* %1191, i64 0, i64 %1197, i32 %1202, i1 zeroext true)
          to label %1207 unwind label %1357

; <label>:1207:                                   ; preds = %1206, %1188
  %1208 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1209 = sub nsw i64 %1208, %1189
  %1210 = sitofp i64 %1209 to double
  %1211 = fdiv double %1210, 1.000000e+09
  %1212 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1211)
          to label %1213 unwind label %1357

; <label>:1213:                                   ; preds = %1207
  %1214 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1215 unwind label %1357

; <label>:1215:                                   ; preds = %1213
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %10)
          to label %1216 unwind label %1357

; <label>:1216:                                   ; preds = %1215
  %1217 = load i64*, i64** %1190, align 8, !tbaa !19
  %1218 = icmp eq i64* %1217, null
  br i1 %1218, label %1221, label %1219

; <label>:1219:                                   ; preds = %1216
  %1220 = bitcast i64* %1217 to i8*
  call void @_ZdlPv(i8* %1220) #2
  br label %1221

; <label>:1221:                                   ; preds = %1219, %1216
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1185) #2
  %1222 = bitcast %"class.std::vector"* %11 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1222) #2
  invoke void @_ZN13Int_Generator21reverse_sorted_middleEmm(%"class.std::vector"* nonnull sret %11, i64 10000000, i64 1000000)
          to label %1223 unwind label %1396

; <label>:1223:                                   ; preds = %1221
  %1224 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1225 unwind label %1367

; <label>:1225:                                   ; preds = %1223
  %1226 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1227 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %11, i64 0, i32 0, i32 0, i32 0
  %1228 = load i64*, i64** %1227, align 8, !tbaa !19
  %1229 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %11, i64 0, i32 0, i32 0, i32 1
  %1230 = bitcast i64** %1229 to i64*
  %1231 = load i64, i64* %1230, align 8, !tbaa !22
  %1232 = ptrtoint i64* %1228 to i64
  %1233 = sub i64 %1231, %1232
  %1234 = ashr exact i64 %1233, 3
  %1235 = icmp eq i64 %1233, 0
  br i1 %1235, label %1244, label %1236

; <label>:1236:                                   ; preds = %1225
  br label %1237

; <label>:1237:                                   ; preds = %1236, %1237
  %1238 = phi i64 [ %1240, %1237 ], [ %1234, %1236 ]
  %1239 = phi i32 [ %1242, %1237 ], [ 0, %1236 ]
  %1240 = lshr i64 %1238, 1
  %1241 = icmp eq i64 %1240, 0
  %1242 = add nuw nsw i32 %1239, 1
  br i1 %1241, label %1243, label %1237

; <label>:1243:                                   ; preds = %1237
  invoke void @_Z11pdqsort_recPmmmib(i64* %1228, i64 0, i64 %1234, i32 %1239, i1 zeroext true)
          to label %1244 unwind label %1367

; <label>:1244:                                   ; preds = %1243, %1225
  %1245 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1246 = sub nsw i64 %1245, %1226
  %1247 = sitofp i64 %1246 to double
  %1248 = fdiv double %1247, 1.000000e+09
  %1249 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1248)
          to label %1250 unwind label %1367

; <label>:1250:                                   ; preds = %1244
  %1251 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1252 unwind label %1367

; <label>:1252:                                   ; preds = %1250
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %11)
          to label %1253 unwind label %1367

; <label>:1253:                                   ; preds = %1252
  %1254 = load i64*, i64** %1227, align 8, !tbaa !19
  %1255 = icmp eq i64* %1254, null
  br i1 %1255, label %1258, label %1256

; <label>:1256:                                   ; preds = %1253
  %1257 = bitcast i64* %1254 to i8*
  call void @_ZdlPv(i8* %1257) #2
  br label %1258

; <label>:1258:                                   ; preds = %1256, %1253
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1222) #2
  %1259 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %1260 = getelementptr i8, i8* %1259, i64 -24
  %1261 = bitcast i8* %1260 to i64*
  %1262 = load i64, i64* %1261, align 8
  %1263 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %1262
  %1264 = getelementptr inbounds i8, i8* %1263, i64 240
  %1265 = bitcast i8* %1264 to %"class.std::ctype"**
  %1266 = load %"class.std::ctype"*, %"class.std::ctype"** %1265, align 8, !tbaa !8
  %1267 = icmp eq %"class.std::ctype"* %1266, null
  br i1 %1267, label %1268, label %1270

; <label>:1268:                                   ; preds = %1258
  invoke void @_ZSt16__throw_bad_castv() #16
          to label %1269 unwind label %1396

; <label>:1269:                                   ; preds = %1268
  unreachable

; <label>:1270:                                   ; preds = %1258
  %1271 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %1266, i64 0, i32 8
  %1272 = load i8, i8* %1271, align 8, !tbaa !12
  %1273 = icmp eq i8 %1272, 0
  br i1 %1273, label %1277, label %1274

; <label>:1274:                                   ; preds = %1270
  %1275 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %1266, i64 0, i32 9, i64 10
  %1276 = load i8, i8* %1275, align 1, !tbaa !14
  br label %1284

; <label>:1277:                                   ; preds = %1270
  invoke void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %1266)
          to label %1278 unwind label %1396

; <label>:1278:                                   ; preds = %1277
  %1279 = bitcast %"class.std::ctype"* %1266 to i8 (%"class.std::ctype"*, i8)***
  %1280 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %1279, align 8, !tbaa !6
  %1281 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %1280, i64 6
  %1282 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %1281, align 8
  %1283 = invoke signext i8 %1282(%"class.std::ctype"* nonnull %1266, i8 signext 10)
          to label %1284 unwind label %1396

; <label>:1284:                                   ; preds = %1278, %1274
  %1285 = phi i8 [ %1276, %1274 ], [ %1283, %1278 ]
  %1286 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %1285)
          to label %1287 unwind label %1396

; <label>:1287:                                   ; preds = %1284
  %1288 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %1286)
          to label %1382 unwind label %1396

; <label>:1289:                                   ; preds = %764, %762, %756, %755, %735
  %1290 = landingpad { i8*, i32 }
          cleanup
  %1291 = extractvalue { i8*, i32 } %1290, 0
  %1292 = extractvalue { i8*, i32 } %1290, 1
  %1293 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %3, i64 0, i32 0, i32 0, i32 0
  %1294 = load i64*, i64** %1293, align 8, !tbaa !19
  %1295 = icmp eq i64* %1294, null
  br i1 %1295, label %1298, label %1296

; <label>:1296:                                   ; preds = %1289
  %1297 = bitcast i64* %1294 to i8*
  call void @_ZdlPv(i8* %1297) #2
  br label %1298

; <label>:1298:                                   ; preds = %1296, %1289
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %734) #2
  br label %1377

; <label>:1299:                                   ; preds = %801, %799, %793, %792, %772
  %1300 = landingpad { i8*, i32 }
          cleanup
  %1301 = extractvalue { i8*, i32 } %1300, 0
  %1302 = extractvalue { i8*, i32 } %1300, 1
  %1303 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %1304 = load i64*, i64** %1303, align 8, !tbaa !19
  %1305 = icmp eq i64* %1304, null
  br i1 %1305, label %1308, label %1306

; <label>:1306:                                   ; preds = %1299
  %1307 = bitcast i64* %1304 to i8*
  call void @_ZdlPv(i8* %1307) #2
  br label %1308

; <label>:1308:                                   ; preds = %1306, %1299
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %771) #2
  br label %1377

; <label>:1309:                                   ; preds = %934, %932, %926, %925, %908
  %1310 = landingpad { i8*, i32 }
          cleanup
  %1311 = extractvalue { i8*, i32 } %1310, 0
  %1312 = extractvalue { i8*, i32 } %1310, 1
  %1313 = load i64*, i64** %813, align 8, !tbaa !19
  %1314 = icmp eq i64* %1313, null
  br i1 %1314, label %1317, label %1315

; <label>:1315:                                   ; preds = %1309
  %1316 = bitcast i64* %1313 to i8*
  call void @_ZdlPv(i8* %1316) #2
  br label %1317

; <label>:1317:                                   ; preds = %1315, %1309
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %808) #2
  br label %1377

; <label>:1318:                                   ; preds = %971, %969, %963, %962, %942
  %1319 = landingpad { i8*, i32 }
          cleanup
  %1320 = extractvalue { i8*, i32 } %1319, 0
  %1321 = extractvalue { i8*, i32 } %1319, 1
  %1322 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %6, i64 0, i32 0, i32 0, i32 0
  %1323 = load i64*, i64** %1322, align 8, !tbaa !19
  %1324 = icmp eq i64* %1323, null
  br i1 %1324, label %1327, label %1325

; <label>:1325:                                   ; preds = %1318
  %1326 = bitcast i64* %1323 to i8*
  call void @_ZdlPv(i8* %1326) #2
  br label %1327

; <label>:1327:                                   ; preds = %1325, %1318
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %941) #2
  br label %1377

; <label>:1328:                                   ; preds = %1008, %1006, %1000, %999, %979
  %1329 = landingpad { i8*, i32 }
          cleanup
  %1330 = extractvalue { i8*, i32 } %1329, 0
  %1331 = extractvalue { i8*, i32 } %1329, 1
  %1332 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %7, i64 0, i32 0, i32 0, i32 0
  %1333 = load i64*, i64** %1332, align 8, !tbaa !19
  %1334 = icmp eq i64* %1333, null
  br i1 %1334, label %1337, label %1335

; <label>:1335:                                   ; preds = %1328
  %1336 = bitcast i64* %1333 to i8*
  call void @_ZdlPv(i8* %1336) #2
  br label %1337

; <label>:1337:                                   ; preds = %1335, %1328
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %978) #2
  br label %1377

; <label>:1338:                                   ; preds = %1045, %1043, %1037, %1036, %1016
  %1339 = landingpad { i8*, i32 }
          cleanup
  %1340 = extractvalue { i8*, i32 } %1339, 0
  %1341 = extractvalue { i8*, i32 } %1339, 1
  %1342 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %8, i64 0, i32 0, i32 0, i32 0
  %1343 = load i64*, i64** %1342, align 8, !tbaa !19
  %1344 = icmp eq i64* %1343, null
  br i1 %1344, label %1347, label %1345

; <label>:1345:                                   ; preds = %1338
  %1346 = bitcast i64* %1343 to i8*
  call void @_ZdlPv(i8* %1346) #2
  br label %1347

; <label>:1347:                                   ; preds = %1345, %1338
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1015) #2
  br label %1377

; <label>:1348:                                   ; preds = %1178, %1176, %1170, %1169, %1152
  %1349 = landingpad { i8*, i32 }
          cleanup
  %1350 = extractvalue { i8*, i32 } %1349, 0
  %1351 = extractvalue { i8*, i32 } %1349, 1
  %1352 = load i64*, i64** %1057, align 8, !tbaa !19
  %1353 = icmp eq i64* %1352, null
  br i1 %1353, label %1356, label %1354

; <label>:1354:                                   ; preds = %1348
  %1355 = bitcast i64* %1352 to i8*
  call void @_ZdlPv(i8* %1355) #2
  br label %1356

; <label>:1356:                                   ; preds = %1354, %1348
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1052) #2
  br label %1377

; <label>:1357:                                   ; preds = %1215, %1213, %1207, %1206, %1186
  %1358 = landingpad { i8*, i32 }
          cleanup
  %1359 = extractvalue { i8*, i32 } %1358, 0
  %1360 = extractvalue { i8*, i32 } %1358, 1
  %1361 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %10, i64 0, i32 0, i32 0, i32 0
  %1362 = load i64*, i64** %1361, align 8, !tbaa !19
  %1363 = icmp eq i64* %1362, null
  br i1 %1363, label %1366, label %1364

; <label>:1364:                                   ; preds = %1357
  %1365 = bitcast i64* %1362 to i8*
  call void @_ZdlPv(i8* %1365) #2
  br label %1366

; <label>:1366:                                   ; preds = %1364, %1357
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1185) #2
  br label %1377

; <label>:1367:                                   ; preds = %1252, %1250, %1244, %1243, %1223
  %1368 = landingpad { i8*, i32 }
          cleanup
  %1369 = extractvalue { i8*, i32 } %1368, 0
  %1370 = extractvalue { i8*, i32 } %1368, 1
  %1371 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %11, i64 0, i32 0, i32 0, i32 0
  %1372 = load i64*, i64** %1371, align 8, !tbaa !19
  %1373 = icmp eq i64* %1372, null
  br i1 %1373, label %1376, label %1374

; <label>:1374:                                   ; preds = %1367
  %1375 = bitcast i64* %1372 to i8*
  call void @_ZdlPv(i8* %1375) #2
  br label %1376

; <label>:1376:                                   ; preds = %1374, %1367
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1222) #2
  br label %1377

; <label>:1377:                                   ; preds = %1376, %1366, %1356, %1347, %1337, %1327, %1317, %1308, %1298
  %1378 = phi i32 [ %1370, %1376 ], [ %1360, %1366 ], [ %1351, %1356 ], [ %1341, %1347 ], [ %1331, %1337 ], [ %1321, %1327 ], [ %1312, %1317 ], [ %1302, %1308 ], [ %1292, %1298 ]
  %1379 = phi i8* [ %1369, %1376 ], [ %1359, %1366 ], [ %1350, %1356 ], [ %1340, %1347 ], [ %1330, %1337 ], [ %1320, %1327 ], [ %1311, %1317 ], [ %1301, %1308 ], [ %1291, %1298 ]
  %1380 = insertvalue { i8*, i32 } undef, i8* %1379, 0
  %1381 = insertvalue { i8*, i32 } %1380, i32 %1378, 1
  br label %1398

; <label>:1382:                                   ; preds = %1287
  %1383 = load i8*, i8** %727, align 8, !tbaa !32
  %1384 = icmp eq i8* %1383, %724
  br i1 %1384, label %1386, label %1385

; <label>:1385:                                   ; preds = %1382
  call void @_ZdlPv(i8* %1383) #2
  br label %1386

; <label>:1386:                                   ; preds = %1382, %1385
  ret i32 0

; <label>:1387:                                   ; preds = %622, %619, %613, %612, %603, %560, %527, %364, %331, %298, %135, %102, %100, %98, %56
  %1388 = landingpad { i8*, i32 }
          cleanup
  br label %1389

; <label>:1389:                                   ; preds = %712, %493, %264, %1387
  %1390 = phi { i8*, i32 } [ %1388, %1387 ], [ %268, %264 ], [ %497, %493 ], [ %716, %712 ]
  %1391 = extractvalue { i8*, i32 } %1390, 0
  %1392 = extractvalue { i8*, i32 } %1390, 1
  %1393 = load i8*, i8** %62, align 8, !tbaa !32
  %1394 = icmp eq i8* %1393, %59
  br i1 %1394, label %1405, label %1395

; <label>:1395:                                   ; preds = %1389
  call void @_ZdlPv(i8* %1393) #2
  br label %1405

; <label>:1396:                                   ; preds = %1287, %1284, %1278, %1277, %1268, %1221, %1184, %1014, %977, %940, %770, %733, %731, %729, %721
  %1397 = landingpad { i8*, i32 }
          cleanup
  br label %1398

; <label>:1398:                                   ; preds = %1377, %1147, %903, %1396
  %1399 = phi { i8*, i32 } [ %1397, %1396 ], [ %907, %903 ], [ %1151, %1147 ], [ %1381, %1377 ]
  %1400 = extractvalue { i8*, i32 } %1399, 0
  %1401 = extractvalue { i8*, i32 } %1399, 1
  %1402 = load i8*, i8** %727, align 8, !tbaa !32
  %1403 = icmp eq i8* %1402, %724
  br i1 %1403, label %1405, label %1404

; <label>:1404:                                   ; preds = %1398
  call void @_ZdlPv(i8* %1402) #2
  br label %1405

; <label>:1405:                                   ; preds = %1398, %1404, %1389, %1395, %97
  %1406 = phi i8* [ %91, %97 ], [ %1391, %1389 ], [ %1391, %1395 ], [ %1400, %1398 ], [ %1400, %1404 ]
  %1407 = phi i32 [ %92, %97 ], [ %1392, %1389 ], [ %1392, %1395 ], [ %1401, %1398 ], [ %1401, %1404 ]
  %1408 = insertvalue { i8*, i32 } undef, i8* %1406, 0
  %1409 = insertvalue { i8*, i32 } %1408, i32 %1407, 1
  resume { i8*, i32 } %1409
}

; Function Attrs: uwtable
define linkonce_odr void @_ZN13Int_Generator6randomEm(%"class.std::vector"* noalias sret, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %3 = alloca %"class.std::__cxx11::basic_string", align 8
  %4 = bitcast %"class.std::vector"* %0 to i8*
  tail call void @llvm.memset.p0i8.i64(i8* %4, i8 0, i64 24, i32 8, i1 false) #2
  %5 = icmp ugt i64 %1, 2305843009213693951
  br i1 %5, label %6, label %8

; <label>:6:                                      ; preds = %2
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %7 unwind label %42

; <label>:7:                                      ; preds = %6
  unreachable

; <label>:8:                                      ; preds = %2
  %9 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %10 = icmp eq i64 %1, 0
  %11 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br i1 %10, label %27, label %12

; <label>:12:                                     ; preds = %8
  %13 = shl i64 %1, 3
  %14 = invoke i8* @_Znwm(i64 %13)
          to label %15 unwind label %42

; <label>:15:                                     ; preds = %12
  %16 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %17 = bitcast i8* %14 to i64*
  %18 = load i64*, i64** %16, align 8, !tbaa !19
  %19 = icmp eq i64* %18, null
  br i1 %19, label %22, label %20

; <label>:20:                                     ; preds = %15
  %21 = bitcast i64* %18 to i8*
  tail call void @_ZdlPv(i8* %21) #2
  br label %22

; <label>:22:                                     ; preds = %20, %15
  %23 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %14, i8** %23, align 8, !tbaa !19
  %24 = bitcast i64** %11 to i8**
  store i8* %14, i8** %24, align 8, !tbaa !22
  %25 = getelementptr inbounds i64, i64* %17, i64 %1
  store i64* %25, i64** %9, align 8, !tbaa !28
  %26 = ptrtoint i8* %14 to i64
  br label %27

; <label>:27:                                     ; preds = %8, %22
  %28 = phi i64 [ %26, %22 ], [ 0, %8 ]
  %29 = bitcast i64** %11 to i64*
  store i64 %28, i64* %29, align 8, !tbaa !22
  %30 = bitcast %"class.std::__cxx11::basic_string"* %3 to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* nonnull %30) #2
  %31 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %3, i64 0, i32 2
  %32 = bitcast %"class.std::__cxx11::basic_string"* %3 to %union.anon**
  store %union.anon* %31, %union.anon** %32, align 8, !tbaa !15
  %33 = bitcast %union.anon* %31 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %33, i8* nonnull getelementptr inbounds ([10 x i8], [10 x i8]* @.str.3, i64 0, i64 0), i64 9, i32 1, i1 false) #2
  %34 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %3, i64 0, i32 1
  store i64 9, i64* %34, align 8, !tbaa !17
  %35 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %3, i64 0, i32 2, i32 1, i64 1
  store i8 0, i8* %35, align 1, !tbaa !14
  invoke fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %3, %"class.std::vector"* nonnull dereferenceable(24) %0, i64 %1)
          to label %36 unwind label %46

; <label>:36:                                     ; preds = %27
  %37 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %3, i64 0, i32 0, i32 0
  %38 = load i8*, i8** %37, align 8, !tbaa !32
  %39 = icmp eq i8* %38, %33
  br i1 %39, label %41, label %40

; <label>:40:                                     ; preds = %36
  call void @_ZdlPv(i8* %38) #2
  br label %41

; <label>:41:                                     ; preds = %36, %40
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %30) #2
  ret void

; <label>:42:                                     ; preds = %12, %6
  %43 = landingpad { i8*, i32 }
          cleanup
  %44 = extractvalue { i8*, i32 } %43, 0
  %45 = extractvalue { i8*, i32 } %43, 1
  br label %55

; <label>:46:                                     ; preds = %27
  %47 = landingpad { i8*, i32 }
          cleanup
  %48 = extractvalue { i8*, i32 } %47, 0
  %49 = extractvalue { i8*, i32 } %47, 1
  %50 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %3, i64 0, i32 0, i32 0
  %51 = load i8*, i8** %50, align 8, !tbaa !32
  %52 = icmp eq i8* %51, %33
  br i1 %52, label %54, label %53

; <label>:53:                                     ; preds = %46
  call void @_ZdlPv(i8* %51) #2
  br label %54

; <label>:54:                                     ; preds = %53, %46
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %30) #2
  br label %55

; <label>:55:                                     ; preds = %54, %42
  %56 = phi i8* [ %44, %42 ], [ %48, %54 ]
  %57 = phi i32 [ %45, %42 ], [ %49, %54 ]
  %58 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %59 = load i64*, i64** %58, align 8, !tbaa !19
  %60 = icmp eq i64* %59, null
  br i1 %60, label %63, label %61

; <label>:61:                                     ; preds = %55
  %62 = bitcast i64* %59 to i8*
  call void @_ZdlPv(i8* %62) #2
  br label %63

; <label>:63:                                     ; preds = %55, %61
  %64 = insertvalue { i8*, i32 } undef, i8* %56, 0
  %65 = insertvalue { i8*, i32 } %64, i32 %57, 1
  resume { i8*, i32 } %65
}

declare i32 @__gxx_personality_v0(...)

; Function Attrs: uwtable
define linkonce_odr void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* dereferenceable(24)) local_unnamed_addr #7 comdat {
  %2 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %3 = load i64*, i64** %2, align 8, !tbaa !23
  %4 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  %5 = load i64*, i64** %4, align 8, !tbaa !23
  %6 = icmp eq i64* %3, %5
  br i1 %6, label %20, label %7

; <label>:7:                                      ; preds = %1
  %8 = getelementptr inbounds i64, i64* %3, i64 1
  %9 = icmp eq i64* %8, %5
  br i1 %9, label %52, label %10

; <label>:10:                                     ; preds = %7
  %11 = load i64, i64* %3, align 8, !tbaa !2
  br label %15

; <label>:12:                                     ; preds = %15
  %13 = getelementptr inbounds i64, i64* %17, i64 1
  %14 = icmp eq i64* %13, %5
  br i1 %14, label %52, label %15

; <label>:15:                                     ; preds = %12, %10
  %16 = phi i64 [ %11, %10 ], [ %18, %12 ]
  %17 = phi i64* [ %8, %10 ], [ %13, %12 ]
  %18 = load i64, i64* %17, align 8, !tbaa !2
  %19 = icmp ult i64 %18, %16
  br i1 %19, label %20, label %12

; <label>:20:                                     ; preds = %15, %1
  %21 = phi i64* [ %3, %1 ], [ %17, %15 ]
  %22 = icmp eq i64* %21, %5
  br i1 %22, label %52, label %23

; <label>:23:                                     ; preds = %20
  %24 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([20 x i8], [20 x i8]* @.str.10, i64 0, i64 0), i64 19)
  %25 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %26 = getelementptr i8, i8* %25, i64 -24
  %27 = bitcast i8* %26 to i64*
  %28 = load i64, i64* %27, align 8
  %29 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %28
  %30 = getelementptr inbounds i8, i8* %29, i64 240
  %31 = bitcast i8* %30 to %"class.std::ctype"**
  %32 = load %"class.std::ctype"*, %"class.std::ctype"** %31, align 8, !tbaa !8
  %33 = icmp eq %"class.std::ctype"* %32, null
  br i1 %33, label %34, label %35

; <label>:34:                                     ; preds = %23
  tail call void @_ZSt16__throw_bad_castv() #16
  unreachable

; <label>:35:                                     ; preds = %23
  %36 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %32, i64 0, i32 8
  %37 = load i8, i8* %36, align 8, !tbaa !12
  %38 = icmp eq i8 %37, 0
  br i1 %38, label %42, label %39

; <label>:39:                                     ; preds = %35
  %40 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %32, i64 0, i32 9, i64 10
  %41 = load i8, i8* %40, align 1, !tbaa !14
  br label %48

; <label>:42:                                     ; preds = %35
  tail call void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %32)
  %43 = bitcast %"class.std::ctype"* %32 to i8 (%"class.std::ctype"*, i8)***
  %44 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %43, align 8, !tbaa !6
  %45 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %44, i64 6
  %46 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %45, align 8
  %47 = tail call signext i8 %46(%"class.std::ctype"* nonnull %32, i8 signext 10)
  br label %48

; <label>:48:                                     ; preds = %39, %42
  %49 = phi i8 [ %41, %39 ], [ %47, %42 ]
  %50 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %49)
  %51 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %50)
  br label %52

; <label>:52:                                     ; preds = %12, %7, %20, %48
  ret void
}

; Function Attrs: uwtable
define internal fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* dereferenceable(32), %"class.std::vector"* dereferenceable(24), i64) unnamed_addr #7 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %4 = alloca %"class.std::basic_ifstream", align 8
  %5 = alloca %"struct.std::error_code", align 8
  %6 = alloca %"struct.std::error_code", align 8
  %7 = alloca i64, align 8
  %8 = bitcast %"class.std::basic_ifstream"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 520, i8* nonnull %8) #2
  call void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEEC1ERKNSt7__cxx1112basic_stringIcS1_SaIcEEESt13_Ios_Openmode(%"class.std::basic_ifstream"* nonnull %4, %"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %0, i32 12)
  %9 = bitcast %"class.std::basic_ifstream"* %4 to i8**
  %10 = load i8*, i8** %9, align 8, !tbaa !6
  %11 = getelementptr i8, i8* %10, i64 -24
  %12 = bitcast i8* %11 to i64*
  %13 = load i64, i64* %12, align 8
  %14 = getelementptr inbounds i8, i8* %8, i64 %13
  %15 = getelementptr inbounds i8, i8* %14, i64 32
  %16 = bitcast i8* %15 to i32*
  %17 = load i32, i32* %16, align 8, !tbaa !39
  %18 = and i32 %17, 5
  %19 = icmp eq i32 %18, 0
  br i1 %19, label %40, label %20

; <label>:20:                                     ; preds = %3
  %21 = call i8* @__cxa_allocate_exception(i64 32) #2
  %22 = bitcast i8* %21 to %"class.std::ios_base::failure"*
  %23 = bitcast %"struct.std::error_code"* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 16, i8* nonnull %23) #2
  %24 = call dereferenceable(8) %"class.std::_V2::error_category"* @_ZSt17iostream_categoryv() #2
  %25 = getelementptr inbounds %"struct.std::error_code", %"struct.std::error_code"* %5, i64 0, i32 0
  store i32 1, i32* %25, align 8
  %26 = getelementptr inbounds %"struct.std::error_code", %"struct.std::error_code"* %5, i64 0, i32 1
  store %"class.std::_V2::error_category"* %24, %"class.std::_V2::error_category"** %26, align 8
  invoke void @_ZNSt8ios_base7failureB5cxx11C1EPKcRKSt10error_code(%"class.std::ios_base::failure"* %22, i8* getelementptr inbounds ([22 x i8], [22 x i8]* @.str.6, i64 0, i64 0), %"struct.std::error_code"* nonnull dereferenceable(16) %5)
          to label %27 unwind label %36

; <label>:27:                                     ; preds = %20
  invoke void @__cxa_throw(i8* %21, i8* bitcast (i8** @_ZTINSt8ios_base7failureB5cxx11E to i8*), i8* bitcast (void (%"class.std::ios_base::failure"*)* @_ZNSt8ios_base7failureB5cxx11D1Ev to i8*)) #16
          to label %145 unwind label %32

; <label>:28:                                     ; preds = %40
  %29 = landingpad { i8*, i32 }
          cleanup
  %30 = extractvalue { i8*, i32 } %29, 0
  %31 = extractvalue { i8*, i32 } %29, 1
  br label %140

; <label>:32:                                     ; preds = %27
  %33 = landingpad { i8*, i32 }
          cleanup
  %34 = extractvalue { i8*, i32 } %33, 0
  %35 = extractvalue { i8*, i32 } %33, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %23) #2
  br label %140

; <label>:36:                                     ; preds = %20
  %37 = landingpad { i8*, i32 }
          cleanup
  %38 = extractvalue { i8*, i32 } %37, 0
  %39 = extractvalue { i8*, i32 } %37, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %23) #2
  call void @__cxa_free_exception(i8* %21) #2
  br label %140

; <label>:40:                                     ; preds = %3
  %41 = bitcast %"class.std::basic_ifstream"* %4 to %"class.std::basic_istream"*
  %42 = invoke dereferenceable(280) %"class.std::basic_istream"* @_ZNSi5seekgElSt12_Ios_Seekdir(%"class.std::basic_istream"* nonnull %41, i64 0, i32 2)
          to label %43 unwind label %28

; <label>:43:                                     ; preds = %40
  %44 = invoke { i64, i64 } @_ZNSi5tellgEv(%"class.std::basic_istream"* nonnull %41)
          to label %45 unwind label %57

; <label>:45:                                     ; preds = %43
  %46 = extractvalue { i64, i64 } %44, 0
  %47 = lshr i64 %46, 3
  %48 = icmp ult i64 %47, %2
  br i1 %48, label %49, label %69

; <label>:49:                                     ; preds = %45
  %50 = call i8* @__cxa_allocate_exception(i64 32) #2
  %51 = bitcast i8* %50 to %"class.std::ios_base::failure"*
  %52 = bitcast %"struct.std::error_code"* %6 to i8*
  call void @llvm.lifetime.start.p0i8(i64 16, i8* nonnull %52) #2
  %53 = call dereferenceable(8) %"class.std::_V2::error_category"* @_ZSt17iostream_categoryv() #2
  %54 = getelementptr inbounds %"struct.std::error_code", %"struct.std::error_code"* %6, i64 0, i32 0
  store i32 1, i32* %54, align 8
  %55 = getelementptr inbounds %"struct.std::error_code", %"struct.std::error_code"* %6, i64 0, i32 1
  store %"class.std::_V2::error_category"* %53, %"class.std::_V2::error_category"** %55, align 8
  invoke void @_ZNSt8ios_base7failureB5cxx11C1EPKcRKSt10error_code(%"class.std::ios_base::failure"* %51, i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str.7, i64 0, i64 0), %"struct.std::error_code"* nonnull dereferenceable(16) %6)
          to label %56 unwind label %65

; <label>:56:                                     ; preds = %49
  invoke void @__cxa_throw(i8* %50, i8* bitcast (i8** @_ZTINSt8ios_base7failureB5cxx11E to i8*), i8* bitcast (void (%"class.std::ios_base::failure"*)* @_ZNSt8ios_base7failureB5cxx11D1Ev to i8*)) #16
          to label %145 unwind label %61

; <label>:57:                                     ; preds = %43
  %58 = landingpad { i8*, i32 }
          cleanup
  %59 = extractvalue { i8*, i32 } %58, 0
  %60 = extractvalue { i8*, i32 } %58, 1
  br label %140

; <label>:61:                                     ; preds = %56
  %62 = landingpad { i8*, i32 }
          cleanup
  %63 = extractvalue { i8*, i32 } %62, 0
  %64 = extractvalue { i8*, i32 } %62, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %52) #2
  br label %140

; <label>:65:                                     ; preds = %49
  %66 = landingpad { i8*, i32 }
          cleanup
  %67 = extractvalue { i8*, i32 } %66, 0
  %68 = extractvalue { i8*, i32 } %66, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %52) #2
  call void @__cxa_free_exception(i8* %50) #2
  br label %140

; <label>:69:                                     ; preds = %45
  %70 = bitcast %"class.std::vector"* %1 to i64*
  %71 = load i64, i64* %70, align 8, !tbaa !19
  %72 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %1, i64 0, i32 0, i32 0, i32 1
  %73 = bitcast i64** %72 to i64*
  store i64 %71, i64* %73, align 8, !tbaa !22
  %74 = icmp ugt i64 %2, 2305843009213693951
  br i1 %74, label %75, label %77

; <label>:75:                                     ; preds = %69
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %76 unwind label %120

; <label>:76:                                     ; preds = %75
  unreachable

; <label>:77:                                     ; preds = %69
  %78 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %1, i64 0, i32 0, i32 0, i32 2
  %79 = bitcast i64** %78 to i64*
  %80 = load i64, i64* %79, align 8, !tbaa !28
  %81 = sub i64 %80, %71
  %82 = ashr exact i64 %81, 3
  %83 = icmp ult i64 %82, %2
  br i1 %83, label %84, label %98

; <label>:84:                                     ; preds = %77
  %85 = shl i64 %2, 3
  %86 = invoke i8* @_Znwm(i64 %85)
          to label %87 unwind label %120

; <label>:87:                                     ; preds = %84
  %88 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %1, i64 0, i32 0, i32 0, i32 0
  %89 = bitcast i8* %86 to i64*
  %90 = load i64*, i64** %88, align 8, !tbaa !19
  %91 = icmp eq i64* %90, null
  br i1 %91, label %94, label %92

; <label>:92:                                     ; preds = %87
  %93 = bitcast i64* %90 to i8*
  call void @_ZdlPv(i8* %93) #2
  br label %94

; <label>:94:                                     ; preds = %92, %87
  %95 = bitcast %"class.std::vector"* %1 to i8**
  store i8* %86, i8** %95, align 8, !tbaa !19
  %96 = bitcast i64** %72 to i8**
  store i8* %86, i8** %96, align 8, !tbaa !22
  %97 = getelementptr inbounds i64, i64* %89, i64 %2
  store i64* %97, i64** %78, align 8, !tbaa !28
  br label %98

; <label>:98:                                     ; preds = %94, %77
  %99 = bitcast i64* %7 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %99) #2
  store i64 0, i64* %7, align 8, !tbaa !2
  %100 = invoke dereferenceable(280) %"class.std::basic_istream"* @_ZNSi5seekgElSt12_Ios_Seekdir(%"class.std::basic_istream"* nonnull %41, i64 0, i32 0)
          to label %101 unwind label %124

; <label>:101:                                    ; preds = %98
  %102 = icmp eq i64 %2, 0
  br i1 %102, label %104, label %103

; <label>:103:                                    ; preds = %101
  br label %126

; <label>:104:                                    ; preds = %130, %101
  %105 = getelementptr inbounds %"class.std::basic_ifstream", %"class.std::basic_ifstream"* %4, i64 0, i32 1
  %106 = invoke %"class.std::basic_filebuf"* @_ZNSt13basic_filebufIcSt11char_traitsIcEE5closeEv(%"class.std::basic_filebuf"* nonnull %105)
          to label %107 unwind label %124

; <label>:107:                                    ; preds = %104
  %108 = icmp eq %"class.std::basic_filebuf"* %106, null
  br i1 %108, label %109, label %135

; <label>:109:                                    ; preds = %107
  %110 = load i8*, i8** %9, align 8, !tbaa !6
  %111 = getelementptr i8, i8* %110, i64 -24
  %112 = bitcast i8* %111 to i64*
  %113 = load i64, i64* %112, align 8
  %114 = getelementptr inbounds i8, i8* %8, i64 %113
  %115 = bitcast i8* %114 to %"class.std::basic_ios"*
  %116 = getelementptr inbounds i8, i8* %114, i64 32
  %117 = bitcast i8* %116 to i32*
  %118 = load i32, i32* %117, align 8, !tbaa !39
  %119 = or i32 %118, 4
  invoke void @_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate(%"class.std::basic_ios"* %115, i32 %119)
          to label %135 unwind label %124

; <label>:120:                                    ; preds = %84, %75
  %121 = landingpad { i8*, i32 }
          cleanup
  %122 = extractvalue { i8*, i32 } %121, 0
  %123 = extractvalue { i8*, i32 } %121, 1
  br label %140

; <label>:124:                                    ; preds = %109, %104, %98
  %125 = landingpad { i8*, i32 }
          cleanup
  br label %136

; <label>:126:                                    ; preds = %103, %130
  %127 = phi i64 [ %131, %130 ], [ 0, %103 ]
  %128 = invoke dereferenceable(280) %"class.std::basic_istream"* @_ZNSi4readEPcl(%"class.std::basic_istream"* nonnull %41, i8* nonnull %99, i64 8)
          to label %129 unwind label %133

; <label>:129:                                    ; preds = %126
  invoke void @_ZNSt6vectorImSaImEE9push_backERKm(%"class.std::vector"* nonnull %1, i64* nonnull dereferenceable(8) %7)
          to label %130 unwind label %133

; <label>:130:                                    ; preds = %129
  %131 = add nuw i64 %127, 1
  %132 = icmp ult i64 %131, %2
  br i1 %132, label %126, label %104

; <label>:133:                                    ; preds = %129, %126
  %134 = landingpad { i8*, i32 }
          cleanup
  br label %136

; <label>:135:                                    ; preds = %107, %109
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %99) #2
  call void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEED1Ev(%"class.std::basic_ifstream"* nonnull %4) #2
  call void @llvm.lifetime.end.p0i8(i64 520, i8* nonnull %8) #2
  ret void

; <label>:136:                                    ; preds = %133, %124
  %137 = phi { i8*, i32 } [ %134, %133 ], [ %125, %124 ]
  %138 = extractvalue { i8*, i32 } %137, 0
  %139 = extractvalue { i8*, i32 } %137, 1
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %99) #2
  br label %140

; <label>:140:                                    ; preds = %61, %32, %57, %65, %136, %120, %36, %28
  %141 = phi i32 [ %39, %36 ], [ %35, %32 ], [ %31, %28 ], [ %60, %57 ], [ %68, %65 ], [ %64, %61 ], [ %139, %136 ], [ %123, %120 ]
  %142 = phi i8* [ %38, %36 ], [ %34, %32 ], [ %30, %28 ], [ %59, %57 ], [ %67, %65 ], [ %63, %61 ], [ %138, %136 ], [ %122, %120 ]
  call void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEED1Ev(%"class.std::basic_ifstream"* nonnull %4) #2
  call void @llvm.lifetime.end.p0i8(i64 520, i8* nonnull %8) #2
  %143 = insertvalue { i8*, i32 } undef, i8* %142, 0
  %144 = insertvalue { i8*, i32 } %143, i32 %141, 1
  resume { i8*, i32 } %144

; <label>:145:                                    ; preds = %56, %27
  unreachable
}

; Function Attrs: noreturn
declare void @_ZSt20__throw_length_errorPKc(i8*) local_unnamed_addr #11

; Function Attrs: noreturn
declare void @_ZSt17__throw_bad_allocv() local_unnamed_addr #11

; Function Attrs: nobuiltin
declare noalias nonnull i8* @_Znwm(i64) local_unnamed_addr #12

; Function Attrs: argmemonly nounwind
declare void @llvm.memmove.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #5

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPv(i8*) local_unnamed_addr #13

; Function Attrs: uwtable
declare void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEEC1ERKNSt7__cxx1112basic_stringIcS1_SaIcEEESt13_Ios_Openmode(%"class.std::basic_ifstream"*, %"class.std::__cxx11::basic_string"* dereferenceable(32), i32) unnamed_addr #7 align 2

declare i8* @__cxa_allocate_exception(i64) local_unnamed_addr

declare void @_ZNSt8ios_base7failureB5cxx11C1EPKcRKSt10error_code(%"class.std::ios_base::failure"*, i8*, %"struct.std::error_code"* dereferenceable(16)) unnamed_addr #0

; Function Attrs: nounwind
declare void @_ZNSt8ios_base7failureB5cxx11D1Ev(%"class.std::ios_base::failure"*) unnamed_addr #1

declare void @__cxa_throw(i8*, i8*, i8*) local_unnamed_addr

declare void @__cxa_free_exception(i8*) local_unnamed_addr

declare dereferenceable(280) %"class.std::basic_istream"* @_ZNSi5seekgElSt12_Ios_Seekdir(%"class.std::basic_istream"*, i64, i32) local_unnamed_addr #0

declare { i64, i64 } @_ZNSi5tellgEv(%"class.std::basic_istream"*) local_unnamed_addr #0

declare dereferenceable(280) %"class.std::basic_istream"* @_ZNSi4readEPcl(%"class.std::basic_istream"*, i8*, i64) local_unnamed_addr #0

; Function Attrs: uwtable
define linkonce_odr void @_ZNSt6vectorImSaImEE9push_backERKm(%"class.std::vector"*, i64* dereferenceable(8)) local_unnamed_addr #7 comdat align 2 personality i32 (...)* @__gxx_personality_v0 {
  %3 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  %4 = load i64*, i64** %3, align 8, !tbaa !22
  %5 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %6 = load i64*, i64** %5, align 8, !tbaa !28
  %7 = icmp eq i64* %4, %6
  %8 = ptrtoint i64* %4 to i64
  br i1 %7, label %12, label %9

; <label>:9:                                      ; preds = %2
  %10 = load i64, i64* %1, align 8, !tbaa !2
  store i64 %10, i64* %4, align 8, !tbaa !2
  %11 = getelementptr inbounds i64, i64* %4, i64 1
  br label %66

; <label>:12:                                     ; preds = %2
  %13 = bitcast i64** %3 to i64*
  %14 = bitcast %"class.std::vector"* %0 to i64*
  %15 = load i64, i64* %14, align 8, !tbaa !23
  %16 = sub i64 %8, %15
  %17 = ashr exact i64 %16, 3
  %18 = icmp eq i64 %16, 0
  %19 = select i1 %18, i64 1, i64 %17
  %20 = add nsw i64 %19, %17
  %21 = icmp ult i64 %20, %17
  %22 = icmp ugt i64 %20, 2305843009213693951
  %23 = or i1 %21, %22
  %24 = select i1 %23, i64 2305843009213693951, i64 %20
  %25 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %26 = icmp eq i64 %24, 0
  %27 = inttoptr i64 %15 to i64*
  br i1 %26, label %36, label %28

; <label>:28:                                     ; preds = %12
  %29 = icmp ugt i64 %24, 2305843009213693951
  br i1 %29, label %30, label %31

; <label>:30:                                     ; preds = %28
  tail call void @_ZSt17__throw_bad_allocv() #16
  unreachable

; <label>:31:                                     ; preds = %28
  %32 = shl i64 %24, 3
  %33 = tail call i8* @_Znwm(i64 %32)
  %34 = bitcast i8* %33 to i64*
  %35 = load i64*, i64** %25, align 8, !tbaa !19
  br label %36

; <label>:36:                                     ; preds = %31, %12
  %37 = phi i64* [ %35, %31 ], [ %27, %12 ]
  %38 = phi i8* [ %33, %31 ], [ null, %12 ]
  %39 = phi i64* [ %34, %31 ], [ null, %12 ]
  %40 = getelementptr inbounds i64, i64* %39, i64 %17
  %41 = load i64, i64* %1, align 8, !tbaa !2
  store i64 %41, i64* %40, align 8, !tbaa !2
  %42 = ptrtoint i64* %37 to i64
  %43 = sub i64 %8, %42
  %44 = ashr exact i64 %43, 3
  %45 = icmp eq i64 %43, 0
  br i1 %45, label %48, label %46

; <label>:46:                                     ; preds = %36
  %47 = bitcast i64* %37 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* %38, i8* %47, i64 %43, i32 8, i1 false) #2
  br label %48

; <label>:48:                                     ; preds = %46, %36
  %49 = getelementptr inbounds i64, i64* %39, i64 %44
  %50 = getelementptr inbounds i64, i64* %49, i64 1
  %51 = load i64, i64* %13, align 8, !tbaa !22
  %52 = sub i64 %51, %8
  %53 = ashr exact i64 %52, 3
  %54 = icmp eq i64 %52, 0
  br i1 %54, label %58, label %55

; <label>:55:                                     ; preds = %48
  %56 = bitcast i64* %50 to i8*
  %57 = bitcast i64* %4 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %56, i8* %57, i64 %52, i32 8, i1 false) #2
  br label %58

; <label>:58:                                     ; preds = %55, %48
  %59 = getelementptr inbounds i64, i64* %50, i64 %53
  %60 = icmp eq i64* %37, null
  br i1 %60, label %63, label %61

; <label>:61:                                     ; preds = %58
  %62 = bitcast i64* %37 to i8*
  tail call void @_ZdlPv(i8* %62) #2
  br label %63

; <label>:63:                                     ; preds = %58, %61
  %64 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %38, i8** %64, align 8, !tbaa !19
  store i64* %59, i64** %3, align 8, !tbaa !22
  %65 = getelementptr inbounds i64, i64* %39, i64 %24
  br label %66

; <label>:66:                                     ; preds = %63, %9
  %67 = phi i64** [ %5, %63 ], [ %3, %9 ]
  %68 = phi i64* [ %65, %63 ], [ %11, %9 ]
  store i64* %68, i64** %67, align 8, !tbaa !23
  ret void
}

; Function Attrs: nounwind uwtable
declare void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEED1Ev(%"class.std::basic_ifstream"*) unnamed_addr #3 align 2

declare void @_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate(%"class.std::basic_ios"*, i32) local_unnamed_addr #0

declare %"class.std::basic_filebuf"* @_ZNSt13basic_filebufIcSt11char_traitsIcEE5closeEv(%"class.std::basic_filebuf"*) local_unnamed_addr #0

; Function Attrs: nounwind
declare dereferenceable(8) %"class.std::_V2::error_category"* @_ZSt17iostream_categoryv() local_unnamed_addr #1

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* dereferenceable(272), i8*, i64) local_unnamed_addr #0

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"*, i8 signext) local_unnamed_addr #0

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"*) local_unnamed_addr #0

; Function Attrs: noreturn
declare void @_ZSt16__throw_bad_castv() local_unnamed_addr #11

declare void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"*) local_unnamed_addr #0

; Function Attrs: uwtable
define linkonce_odr void @_ZSt11__make_heapIPmN9__gnu_cxx5__ops15_Iter_comp_iterISt4lessImEEEEvT_S7_RT0_(i64*, i64*, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* dereferenceable(1)) local_unnamed_addr #7 comdat {
  %4 = ptrtoint i64* %1 to i64
  %5 = ptrtoint i64* %0 to i64
  %6 = sub i64 %4, %5
  %7 = ashr exact i64 %6, 3
  %8 = icmp slt i64 %6, 16
  br i1 %8, label %106, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 8
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %17, label %16

; <label>:16:                                     ; preds = %9
  br label %67

; <label>:17:                                     ; preds = %9
  %18 = shl nsw i64 %11, 1
  %19 = or i64 %18, 1
  %20 = getelementptr inbounds i64, i64* %0, i64 %19
  %21 = getelementptr inbounds i64, i64* %0, i64 %11
  br label %22

; <label>:22:                                     ; preds = %62, %17
  %23 = phi i64 [ %11, %17 ], [ %66, %62 ]
  %24 = getelementptr inbounds i64, i64* %0, i64 %23
  %25 = load i64, i64* %24, align 8, !tbaa !2
  %26 = icmp sgt i64 %13, %23
  br i1 %26, label %27, label %43

; <label>:27:                                     ; preds = %22
  br label %28

; <label>:28:                                     ; preds = %27, %28
  %29 = phi i64 [ %38, %28 ], [ %23, %27 ]
  %30 = shl i64 %29, 1
  %31 = add i64 %30, 2
  %32 = getelementptr inbounds i64, i64* %0, i64 %31
  %33 = or i64 %30, 1
  %34 = getelementptr inbounds i64, i64* %0, i64 %33
  %35 = load i64, i64* %32, align 8, !tbaa !2
  %36 = load i64, i64* %34, align 8, !tbaa !2
  %37 = icmp ult i64 %35, %36
  %38 = select i1 %37, i64 %33, i64 %31
  %39 = getelementptr inbounds i64, i64* %0, i64 %38
  %40 = load i64, i64* %39, align 8, !tbaa !2
  %41 = getelementptr inbounds i64, i64* %0, i64 %29
  store i64 %40, i64* %41, align 8, !tbaa !2
  %42 = icmp slt i64 %38, %13
  br i1 %42, label %28, label %43

; <label>:43:                                     ; preds = %28, %22
  %44 = phi i64 [ %23, %22 ], [ %38, %28 ]
  %45 = icmp eq i64 %44, %11
  br i1 %45, label %46, label %48

; <label>:46:                                     ; preds = %43
  %47 = load i64, i64* %20, align 8, !tbaa !2
  store i64 %47, i64* %21, align 8, !tbaa !2
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
  %56 = getelementptr inbounds i64, i64* %0, i64 %55
  %57 = load i64, i64* %56, align 8, !tbaa !2
  %58 = icmp ult i64 %57, %25
  br i1 %58, label %59, label %62

; <label>:59:                                     ; preds = %52
  %60 = getelementptr inbounds i64, i64* %0, i64 %53
  store i64 %57, i64* %60, align 8, !tbaa !2
  %61 = icmp sgt i64 %55, %23
  br i1 %61, label %52, label %62

; <label>:62:                                     ; preds = %52, %59, %48
  %63 = phi i64 [ %49, %48 ], [ %55, %59 ], [ %53, %52 ]
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  store i64 %25, i64* %64, align 8, !tbaa !2
  %65 = icmp eq i64 %23, 0
  %66 = add nsw i64 %23, -1
  br i1 %65, label %106, label %22

; <label>:67:                                     ; preds = %16, %101
  %68 = phi i64 [ %105, %101 ], [ %11, %16 ]
  %69 = getelementptr inbounds i64, i64* %0, i64 %68
  %70 = load i64, i64* %69, align 8, !tbaa !2
  %71 = icmp sgt i64 %13, %68
  br i1 %71, label %72, label %101

; <label>:72:                                     ; preds = %67
  br label %73

; <label>:73:                                     ; preds = %72, %73
  %74 = phi i64 [ %83, %73 ], [ %68, %72 ]
  %75 = shl i64 %74, 1
  %76 = add i64 %75, 2
  %77 = getelementptr inbounds i64, i64* %0, i64 %76
  %78 = or i64 %75, 1
  %79 = getelementptr inbounds i64, i64* %0, i64 %78
  %80 = load i64, i64* %77, align 8, !tbaa !2
  %81 = load i64, i64* %79, align 8, !tbaa !2
  %82 = icmp ult i64 %80, %81
  %83 = select i1 %82, i64 %78, i64 %76
  %84 = getelementptr inbounds i64, i64* %0, i64 %83
  %85 = load i64, i64* %84, align 8, !tbaa !2
  %86 = getelementptr inbounds i64, i64* %0, i64 %74
  store i64 %85, i64* %86, align 8, !tbaa !2
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
  %95 = getelementptr inbounds i64, i64* %0, i64 %94
  %96 = load i64, i64* %95, align 8, !tbaa !2
  %97 = icmp ult i64 %96, %70
  br i1 %97, label %98, label %101

; <label>:98:                                     ; preds = %91
  %99 = getelementptr inbounds i64, i64* %0, i64 %92
  store i64 %96, i64* %99, align 8, !tbaa !2
  %100 = icmp sgt i64 %94, %68
  br i1 %100, label %91, label %101

; <label>:101:                                    ; preds = %91, %98, %67, %88
  %102 = phi i64 [ %83, %88 ], [ %68, %67 ], [ %94, %98 ], [ %92, %91 ]
  %103 = getelementptr inbounds i64, i64* %0, i64 %102
  store i64 %70, i64* %103, align 8, !tbaa !2
  %104 = icmp eq i64 %68, 0
  %105 = add nsw i64 %68, -1
  br i1 %104, label %106, label %67

; <label>:106:                                    ; preds = %101, %62, %3
  ret void
}

; Function Attrs: uwtable
define linkonce_odr void @_ZN13Int_Generator10random_dupEmm(%"class.std::vector"* noalias sret, i64, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %4 = alloca %"class.std::__cxx11::basic_string", align 8
  %5 = bitcast %"class.std::vector"* %0 to i8*
  tail call void @llvm.memset.p0i8.i64(i8* %5, i8 0, i64 24, i32 8, i1 false) #2
  %6 = icmp ugt i64 %1, 2305843009213693951
  br i1 %6, label %7, label %9

; <label>:7:                                      ; preds = %3
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %8 unwind label %51

; <label>:8:                                      ; preds = %7
  unreachable

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %11 = bitcast %"class.std::vector"* %0 to i64*
  %12 = icmp eq i64 %1, 0
  %13 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br i1 %12, label %29, label %14

; <label>:14:                                     ; preds = %9
  %15 = shl i64 %1, 3
  %16 = invoke i8* @_Znwm(i64 %15)
          to label %17 unwind label %51

; <label>:17:                                     ; preds = %14
  %18 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %19 = bitcast i8* %16 to i64*
  %20 = load i64*, i64** %18, align 8, !tbaa !19
  %21 = icmp eq i64* %20, null
  br i1 %21, label %24, label %22

; <label>:22:                                     ; preds = %17
  %23 = bitcast i64* %20 to i8*
  tail call void @_ZdlPv(i8* %23) #2
  br label %24

; <label>:24:                                     ; preds = %22, %17
  %25 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %16, i8** %25, align 8, !tbaa !19
  %26 = bitcast i64** %13 to i8**
  store i8* %16, i8** %26, align 8, !tbaa !22
  %27 = getelementptr inbounds i64, i64* %19, i64 %1
  store i64* %27, i64** %10, align 8, !tbaa !28
  %28 = ptrtoint i8* %16 to i64
  br label %29

; <label>:29:                                     ; preds = %9, %24
  %30 = phi i64 [ %28, %24 ], [ 0, %9 ]
  %31 = bitcast i64** %13 to i64*
  store i64 %30, i64* %31, align 8, !tbaa !22
  %32 = bitcast %"class.std::__cxx11::basic_string"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* nonnull %32) #2
  %33 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 2
  %34 = bitcast %"class.std::__cxx11::basic_string"* %4 to %union.anon**
  store %union.anon* %33, %union.anon** %34, align 8, !tbaa !15
  %35 = bitcast %union.anon* %33 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %35, i8* nonnull getelementptr inbounds ([10 x i8], [10 x i8]* @.str.3, i64 0, i64 0), i64 9, i32 1, i1 false) #2
  %36 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 1
  store i64 9, i64* %36, align 8, !tbaa !17
  %37 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 2, i32 1, i64 1
  store i8 0, i8* %37, align 1, !tbaa !14
  invoke fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %4, %"class.std::vector"* nonnull dereferenceable(24) %0, i64 %1)
          to label %38 unwind label %55

; <label>:38:                                     ; preds = %29
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %40 = load i8*, i8** %39, align 8, !tbaa !32
  %41 = icmp eq i8* %40, %35
  br i1 %41, label %43, label %42

; <label>:42:                                     ; preds = %38
  call void @_ZdlPv(i8* %40) #2
  br label %43

; <label>:43:                                     ; preds = %38, %42
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %32) #2
  %44 = load i64, i64* %31, align 8, !tbaa !22
  %45 = load i64, i64* %11, align 8, !tbaa !19
  %46 = icmp eq i64 %44, %45
  %47 = inttoptr i64 %45 to i64*
  br i1 %46, label %71, label %48

; <label>:48:                                     ; preds = %43
  %49 = sub i64 %44, %45
  %50 = ashr exact i64 %49, 3
  br label %64

; <label>:51:                                     ; preds = %14, %7
  %52 = landingpad { i8*, i32 }
          cleanup
  %53 = extractvalue { i8*, i32 } %52, 0
  %54 = extractvalue { i8*, i32 } %52, 1
  br label %72

; <label>:55:                                     ; preds = %29
  %56 = landingpad { i8*, i32 }
          cleanup
  %57 = extractvalue { i8*, i32 } %56, 0
  %58 = extractvalue { i8*, i32 } %56, 1
  %59 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %60 = load i8*, i8** %59, align 8, !tbaa !32
  %61 = icmp eq i8* %60, %35
  br i1 %61, label %63, label %62

; <label>:62:                                     ; preds = %55
  call void @_ZdlPv(i8* %60) #2
  br label %63

; <label>:63:                                     ; preds = %62, %55
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %32) #2
  br label %72

; <label>:64:                                     ; preds = %48, %64
  %65 = phi i64 [ 0, %48 ], [ %69, %64 ]
  %66 = getelementptr inbounds i64, i64* %47, i64 %65
  %67 = load i64, i64* %66, align 8, !tbaa !2
  %68 = urem i64 %67, %2
  store i64 %68, i64* %66, align 8, !tbaa !2
  %69 = add nuw i64 %65, 1
  %70 = icmp ult i64 %69, %50
  br i1 %70, label %64, label %71

; <label>:71:                                     ; preds = %64, %43
  ret void

; <label>:72:                                     ; preds = %63, %51
  %73 = phi i8* [ %53, %51 ], [ %57, %63 ]
  %74 = phi i32 [ %54, %51 ], [ %58, %63 ]
  %75 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %76 = load i64*, i64** %75, align 8, !tbaa !19
  %77 = icmp eq i64* %76, null
  br i1 %77, label %80, label %78

; <label>:78:                                     ; preds = %72
  %79 = bitcast i64* %76 to i8*
  call void @_ZdlPv(i8* %79) #2
  br label %80

; <label>:80:                                     ; preds = %72, %78
  %81 = insertvalue { i8*, i32 } undef, i8* %73, 0
  %82 = insertvalue { i8*, i32 } %81, i32 %74, 1
  resume { i8*, i32 } %82
}

; Function Attrs: uwtable
define linkonce_odr void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* noalias sret, i64, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %4 = alloca %"class.std::__cxx11::basic_string", align 8
  %5 = bitcast %"class.std::vector"* %0 to i8*
  tail call void @llvm.memset.p0i8.i64(i8* %5, i8 0, i64 24, i32 8, i1 false) #2
  %6 = icmp ugt i64 %1, 2305843009213693951
  br i1 %6, label %7, label %9

; <label>:7:                                      ; preds = %3
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %8 unwind label %55

; <label>:8:                                      ; preds = %7
  unreachable

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %11 = icmp eq i64 %1, 0
  %12 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br i1 %11, label %28, label %13

; <label>:13:                                     ; preds = %9
  %14 = shl i64 %1, 3
  %15 = invoke i8* @_Znwm(i64 %14)
          to label %16 unwind label %55

; <label>:16:                                     ; preds = %13
  %17 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %18 = bitcast i8* %15 to i64*
  %19 = load i64*, i64** %17, align 8, !tbaa !19
  %20 = icmp eq i64* %19, null
  br i1 %20, label %23, label %21

; <label>:21:                                     ; preds = %16
  %22 = bitcast i64* %19 to i8*
  tail call void @_ZdlPv(i8* %22) #2
  br label %23

; <label>:23:                                     ; preds = %21, %16
  %24 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %15, i8** %24, align 8, !tbaa !19
  %25 = bitcast i64** %12 to i8**
  store i8* %15, i8** %25, align 8, !tbaa !22
  %26 = getelementptr inbounds i64, i64* %18, i64 %1
  store i64* %26, i64** %10, align 8, !tbaa !28
  %27 = ptrtoint i8* %15 to i64
  br label %28

; <label>:28:                                     ; preds = %9, %23
  %29 = phi i64 [ %27, %23 ], [ 0, %9 ]
  %30 = bitcast i64** %12 to i64*
  store i64 %29, i64* %30, align 8, !tbaa !22
  %31 = bitcast %"class.std::__cxx11::basic_string"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* nonnull %31) #2
  %32 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 2
  %33 = bitcast %"class.std::__cxx11::basic_string"* %4 to %union.anon**
  store %union.anon* %32, %union.anon** %33, align 8, !tbaa !15
  %34 = bitcast %union.anon* %32 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %34, i8* nonnull getelementptr inbounds ([10 x i8], [10 x i8]* @.str.3, i64 0, i64 0), i64 9, i32 1, i1 false) #2
  %35 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 1
  store i64 9, i64* %35, align 8, !tbaa !17
  %36 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 2, i32 1, i64 1
  store i8 0, i8* %36, align 1, !tbaa !14
  %37 = add i64 %2, %1
  invoke fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %4, %"class.std::vector"* nonnull dereferenceable(24) %0, i64 %37)
          to label %38 unwind label %59

; <label>:38:                                     ; preds = %28
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %40 = load i8*, i8** %39, align 8, !tbaa !32
  %41 = icmp eq i8* %40, %34
  br i1 %41, label %43, label %42

; <label>:42:                                     ; preds = %38
  call void @_ZdlPv(i8* %40) #2
  br label %43

; <label>:43:                                     ; preds = %38, %42
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  %44 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %45 = load i64*, i64** %44, align 8, !tbaa !23
  %46 = getelementptr inbounds i64, i64* %45, i64 %1
  %47 = icmp eq i64 %1, 0
  br i1 %47, label %68, label %48

; <label>:48:                                     ; preds = %43
  %49 = shl nuw i64 %1, 3
  %50 = ashr exact i64 %49, 3
  %51 = call i64 @llvm.ctlz.i64(i64 %50, i1 true) #2, !range !24
  %52 = shl nuw nsw i64 %51, 1
  %53 = xor i64 %52, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %45, i64* %46, i64 %53)
          to label %54 unwind label %55

; <label>:54:                                     ; preds = %48
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %45, i64* %46)
          to label %68 unwind label %55

; <label>:55:                                     ; preds = %54, %48, %13, %7
  %56 = landingpad { i8*, i32 }
          cleanup
  %57 = extractvalue { i8*, i32 } %56, 0
  %58 = extractvalue { i8*, i32 } %56, 1
  br label %69

; <label>:59:                                     ; preds = %28
  %60 = landingpad { i8*, i32 }
          cleanup
  %61 = extractvalue { i8*, i32 } %60, 0
  %62 = extractvalue { i8*, i32 } %60, 1
  %63 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %64 = load i8*, i8** %63, align 8, !tbaa !32
  %65 = icmp eq i8* %64, %34
  br i1 %65, label %67, label %66

; <label>:66:                                     ; preds = %59
  call void @_ZdlPv(i8* %64) #2
  br label %67

; <label>:67:                                     ; preds = %66, %59
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  br label %69

; <label>:68:                                     ; preds = %43, %54
  ret void

; <label>:69:                                     ; preds = %67, %55
  %70 = phi i32 [ %58, %55 ], [ %62, %67 ]
  %71 = phi i8* [ %57, %55 ], [ %61, %67 ]
  %72 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %73 = load i64*, i64** %72, align 8, !tbaa !19
  %74 = icmp eq i64* %73, null
  br i1 %74, label %77, label %75

; <label>:75:                                     ; preds = %69
  %76 = bitcast i64* %73 to i8*
  call void @_ZdlPv(i8* %76) #2
  br label %77

; <label>:77:                                     ; preds = %69, %75
  %78 = insertvalue { i8*, i32 } undef, i8* %71, 0
  %79 = insertvalue { i8*, i32 } %78, i32 %70, 1
  resume { i8*, i32 } %79
}

; Function Attrs: uwtable
define linkonce_odr void @_ZN13Int_Generator13sorted_middleEmm(%"class.std::vector"* noalias sret, i64, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %4 = alloca %"class.std::vector", align 8
  %5 = alloca %"class.std::__cxx11::basic_string", align 8
  %6 = bitcast %"class.std::vector"* %0 to i8*
  tail call void @llvm.memset.p0i8.i64(i8* %6, i8 0, i64 24, i32 8, i1 false) #2
  %7 = bitcast %"class.std::vector"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %7) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %7, i8 0, i64 24, i32 8, i1 false) #2
  %8 = icmp ugt i64 %1, 2305843009213693951
  br i1 %8, label %9, label %11

; <label>:9:                                      ; preds = %3
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %10 unwind label %54

; <label>:10:                                     ; preds = %9
  unreachable

; <label>:11:                                     ; preds = %3
  %12 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %13 = bitcast %"class.std::vector"* %0 to i64*
  %14 = icmp eq i64 %1, 0
  %15 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br i1 %14, label %31, label %16

; <label>:16:                                     ; preds = %11
  %17 = shl i64 %1, 3
  %18 = invoke i8* @_Znwm(i64 %17)
          to label %19 unwind label %54

; <label>:19:                                     ; preds = %16
  %20 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %21 = bitcast i8* %18 to i64*
  %22 = load i64*, i64** %20, align 8, !tbaa !19
  %23 = icmp eq i64* %22, null
  br i1 %23, label %26, label %24

; <label>:24:                                     ; preds = %19
  %25 = bitcast i64* %22 to i8*
  tail call void @_ZdlPv(i8* %25) #2
  br label %26

; <label>:26:                                     ; preds = %24, %19
  %27 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %18, i8** %27, align 8, !tbaa !19
  %28 = bitcast i64** %15 to i8**
  store i8* %18, i8** %28, align 8, !tbaa !22
  %29 = getelementptr inbounds i64, i64* %21, i64 %1
  store i64* %29, i64** %12, align 8, !tbaa !28
  %30 = ptrtoint i8* %18 to i64
  br label %31

; <label>:31:                                     ; preds = %11, %26
  %32 = phi i64 [ %30, %26 ], [ 0, %11 ]
  %33 = bitcast i64** %15 to i64*
  store i64 %32, i64* %33, align 8, !tbaa !22
  %34 = bitcast %"class.std::__cxx11::basic_string"* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* nonnull %34) #2
  %35 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 2
  %36 = bitcast %"class.std::__cxx11::basic_string"* %5 to %union.anon**
  store %union.anon* %35, %union.anon** %36, align 8, !tbaa !15
  %37 = bitcast %union.anon* %35 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %37, i8* nonnull getelementptr inbounds ([10 x i8], [10 x i8]* @.str.3, i64 0, i64 0), i64 9, i32 1, i1 false) #2
  %38 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 1
  store i64 9, i64* %38, align 8, !tbaa !17
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 2, i32 1, i64 1
  store i8 0, i8* %39, align 1, !tbaa !14
  %40 = add i64 %2, %1
  invoke fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %5, %"class.std::vector"* nonnull dereferenceable(24) %0, i64 %40)
          to label %41 unwind label %59

; <label>:41:                                     ; preds = %31
  %42 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %43 = load i8*, i8** %42, align 8, !tbaa !32
  %44 = icmp eq i8* %43, %37
  br i1 %44, label %46, label %45

; <label>:45:                                     ; preds = %41
  call void @_ZdlPv(i8* %43) #2
  br label %46

; <label>:46:                                     ; preds = %41, %45
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  %47 = load i64, i64* %33, align 8, !tbaa !22
  %48 = load i64, i64* %13, align 8, !tbaa !19
  %49 = sub i64 %47, %48
  %50 = ashr exact i64 %49, 3
  %51 = icmp ugt i64 %50, %1
  %52 = inttoptr i64 %48 to i64*
  br i1 %51, label %53, label %70

; <label>:53:                                     ; preds = %46
  br label %87

; <label>:54:                                     ; preds = %188, %180, %78, %16, %9
  %55 = phi i64 [ 0, %9 ], [ %75, %188 ], [ %75, %180 ], [ %75, %78 ], [ 0, %16 ]
  %56 = landingpad { i8*, i32 }
          cleanup
  %57 = extractvalue { i8*, i32 } %56, 0
  %58 = extractvalue { i8*, i32 } %56, 1
  br label %482

; <label>:59:                                     ; preds = %31
  %60 = landingpad { i8*, i32 }
          cleanup
  %61 = extractvalue { i8*, i32 } %60, 0
  %62 = extractvalue { i8*, i32 } %60, 1
  %63 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %64 = load i8*, i8** %63, align 8, !tbaa !32
  %65 = icmp eq i8* %64, %37
  br i1 %65, label %67, label %66

; <label>:66:                                     ; preds = %59
  call void @_ZdlPv(i8* %64) #2
  br label %67

; <label>:67:                                     ; preds = %66, %59
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  br label %482

; <label>:68:                                     ; preds = %140
  %69 = ptrtoint i64* %149 to i64
  br label %70

; <label>:70:                                     ; preds = %68, %46
  %71 = phi i64* [ %52, %46 ], [ %141, %68 ]
  %72 = phi i64* [ %52, %46 ], [ %142, %68 ]
  %73 = phi i64* [ %52, %46 ], [ %143, %68 ]
  %74 = phi i64 [ 0, %46 ], [ %69, %68 ]
  %75 = phi i64 [ 0, %46 ], [ %147, %68 ]
  %76 = phi i64 [ %50, %46 ], [ %153, %68 ]
  %77 = icmp ult i64 %76, %1
  br i1 %77, label %78, label %83

; <label>:78:                                     ; preds = %70
  %79 = sub i64 %1, %76
  invoke void @_ZNSt6vectorImSaImEE17_M_default_appendEm(%"class.std::vector"* nonnull %0, i64 %79)
          to label %80 unwind label %54

; <label>:80:                                     ; preds = %78
  %81 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %82 = load i64*, i64** %81, align 8, !tbaa !23
  br label %163

; <label>:83:                                     ; preds = %70
  %84 = icmp ugt i64 %76, %1
  br i1 %84, label %85, label %163

; <label>:85:                                     ; preds = %83
  %86 = getelementptr inbounds i64, i64* %71, i64 %1
  store i64* %86, i64** %15, align 8, !tbaa !22
  br label %163

; <label>:87:                                     ; preds = %53, %140
  %88 = phi i64* [ %142, %140 ], [ %52, %53 ]
  %89 = phi i64* [ %143, %140 ], [ %52, %53 ]
  %90 = phi i64 [ %144, %140 ], [ %48, %53 ]
  %91 = phi i64 [ %145, %140 ], [ %47, %53 ]
  %92 = phi i64* [ %141, %140 ], [ %52, %53 ]
  %93 = phi i64 [ %151, %140 ], [ %1, %53 ]
  %94 = phi i64* [ %148, %140 ], [ null, %53 ]
  %95 = phi i64 [ %147, %140 ], [ 0, %53 ]
  %96 = phi i64 [ %150, %140 ], [ 0, %53 ]
  %97 = getelementptr inbounds i64, i64* %92, i64 %93
  %98 = inttoptr i64 %96 to i64*
  %99 = icmp eq i64* %94, %98
  br i1 %99, label %103, label %100

; <label>:100:                                    ; preds = %87
  %101 = load i64, i64* %97, align 8, !tbaa !2
  store i64 %101, i64* %98, align 8, !tbaa !2
  %102 = inttoptr i64 %90 to i64*
  br label %140

; <label>:103:                                    ; preds = %87
  %104 = sub i64 %96, %95
  %105 = ashr exact i64 %104, 3
  %106 = icmp eq i64 %104, 0
  %107 = select i1 %106, i64 1, i64 %105
  %108 = add nsw i64 %107, %105
  %109 = icmp ult i64 %108, %105
  %110 = icmp ugt i64 %108, 2305843009213693951
  %111 = or i1 %109, %110
  %112 = select i1 %111, i64 2305843009213693951, i64 %108
  %113 = icmp eq i64 %112, 0
  br i1 %113, label %123, label %114

; <label>:114:                                    ; preds = %103
  %115 = icmp ugt i64 %112, 2305843009213693951
  br i1 %115, label %116, label %118

; <label>:116:                                    ; preds = %114
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %117 unwind label %157

; <label>:117:                                    ; preds = %116
  unreachable

; <label>:118:                                    ; preds = %114
  %119 = shl i64 %112, 3
  %120 = invoke i8* @_Znwm(i64 %119)
          to label %121 unwind label %155

; <label>:121:                                    ; preds = %118
  %122 = bitcast i8* %120 to i64*
  br label %123

; <label>:123:                                    ; preds = %121, %103
  %124 = phi i8* [ %120, %121 ], [ null, %103 ]
  %125 = phi i64* [ %122, %121 ], [ null, %103 ]
  %126 = getelementptr inbounds i64, i64* %125, i64 %105
  %127 = load i64, i64* %97, align 8, !tbaa !2
  store i64 %127, i64* %126, align 8, !tbaa !2
  br i1 %106, label %130, label %128

; <label>:128:                                    ; preds = %123
  %129 = inttoptr i64 %95 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %124, i8* %129, i64 %104, i32 8, i1 false) #2
  br label %130

; <label>:130:                                    ; preds = %123, %128
  %131 = icmp eq i64 %95, 0
  br i1 %131, label %134, label %132

; <label>:132:                                    ; preds = %130
  %133 = inttoptr i64 %95 to i8*
  call void @_ZdlPv(i8* %133) #2
  br label %134

; <label>:134:                                    ; preds = %132, %130
  %135 = ptrtoint i8* %124 to i64
  %136 = getelementptr inbounds i64, i64* %125, i64 %112
  %137 = load i64, i64* %33, align 8, !tbaa !22
  %138 = load i64, i64* %13, align 8, !tbaa !19
  %139 = inttoptr i64 %138 to i64*
  br label %140

; <label>:140:                                    ; preds = %134, %100
  %141 = phi i64* [ %139, %134 ], [ %102, %100 ]
  %142 = phi i64* [ %139, %134 ], [ %88, %100 ]
  %143 = phi i64* [ %139, %134 ], [ %89, %100 ]
  %144 = phi i64 [ %138, %134 ], [ %90, %100 ]
  %145 = phi i64 [ %137, %134 ], [ %91, %100 ]
  %146 = phi i64* [ %126, %134 ], [ %98, %100 ]
  %147 = phi i64 [ %135, %134 ], [ %95, %100 ]
  %148 = phi i64* [ %136, %134 ], [ %94, %100 ]
  %149 = getelementptr inbounds i64, i64* %146, i64 1
  %150 = ptrtoint i64* %149 to i64
  %151 = add nuw i64 %93, 1
  %152 = sub i64 %145, %144
  %153 = ashr exact i64 %152, 3
  %154 = icmp ult i64 %151, %153
  br i1 %154, label %87, label %68

; <label>:155:                                    ; preds = %118
  %156 = landingpad { i8*, i32 }
          cleanup
  br label %159

; <label>:157:                                    ; preds = %116
  %158 = landingpad { i8*, i32 }
          cleanup
  br label %159

; <label>:159:                                    ; preds = %157, %155
  %160 = phi { i8*, i32 } [ %156, %155 ], [ %158, %157 ]
  %161 = extractvalue { i8*, i32 } %160, 0
  %162 = extractvalue { i8*, i32 } %160, 1
  br label %482

; <label>:163:                                    ; preds = %80, %85, %83
  %164 = phi i64* [ %82, %80 ], [ %72, %85 ], [ %72, %83 ]
  %165 = phi i64* [ %82, %80 ], [ %73, %85 ], [ %73, %83 ]
  %166 = lshr i64 %1, 1
  %167 = icmp eq i64 %166, 0
  %168 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  br i1 %167, label %176, label %169

; <label>:169:                                    ; preds = %163
  %170 = add i64 %1, -1
  %171 = getelementptr inbounds i64, i64* %165, i64 %170
  %172 = load i64, i64* %165, align 8, !tbaa !2
  %173 = load i64, i64* %171, align 8, !tbaa !2
  store i64 %173, i64* %165, align 8, !tbaa !2
  store i64 %172, i64* %171, align 8, !tbaa !2
  %174 = icmp eq i64 %166, 1
  br i1 %174, label %176, label %175

; <label>:175:                                    ; preds = %169
  br label %189

; <label>:176:                                    ; preds = %189, %169, %163
  %177 = phi i64* [ %165, %163 ], [ %164, %169 ], [ %164, %189 ]
  %178 = load i64*, i64** %15, align 8, !tbaa !23
  %179 = icmp eq i64* %177, %178
  br i1 %179, label %198, label %180

; <label>:180:                                    ; preds = %176
  %181 = ptrtoint i64* %178 to i64
  %182 = ptrtoint i64* %177 to i64
  %183 = sub i64 %181, %182
  %184 = ashr exact i64 %183, 3
  %185 = call i64 @llvm.ctlz.i64(i64 %184, i1 true) #2, !range !24
  %186 = shl nuw nsw i64 %185, 1
  %187 = xor i64 %186, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %177, i64* %178, i64 %187)
          to label %188 unwind label %54

; <label>:188:                                    ; preds = %180
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %177, i64* %178)
          to label %198 unwind label %54

; <label>:189:                                    ; preds = %175, %189
  %190 = phi i64 [ %196, %189 ], [ 1, %175 ]
  %191 = getelementptr inbounds i64, i64* %164, i64 %190
  %192 = sub i64 %170, %190
  %193 = getelementptr inbounds i64, i64* %164, i64 %192
  %194 = load i64, i64* %191, align 8, !tbaa !2
  %195 = load i64, i64* %193, align 8, !tbaa !2
  store i64 %195, i64* %191, align 8, !tbaa !2
  store i64 %194, i64* %193, align 8, !tbaa !2
  %196 = add nuw nsw i64 %190, 1
  %197 = icmp eq i64 %196, %166
  br i1 %197, label %176, label %189, !llvm.loop !46

; <label>:198:                                    ; preds = %176, %188
  %199 = udiv i64 %1, %2
  %200 = add i64 %199, 1
  %201 = sub i64 %74, %75
  %202 = ashr exact i64 %201, 3
  %203 = icmp eq i64 %201, 0
  br i1 %203, label %214, label %204

; <label>:204:                                    ; preds = %198
  %205 = inttoptr i64 %75 to i64*
  %206 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %207 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %208 = bitcast i64** %206 to i64*
  %209 = bitcast %"class.std::vector"* %4 to i64*
  %210 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %211 = icmp eq i64 %200, 0
  %212 = bitcast %"class.std::vector"* %4 to i8**
  %213 = load i64*, i64** %206, align 8, !tbaa !22
  br label %229

; <label>:214:                                    ; preds = %296, %198
  %215 = phi i64 [ 0, %198 ], [ %299, %296 ]
  %216 = load i64, i64* %33, align 8, !tbaa !22
  %217 = load i64, i64* %13, align 8, !tbaa !19
  %218 = sub i64 %216, %217
  %219 = ashr exact i64 %218, 3
  %220 = icmp ult i64 %215, %219
  br i1 %220, label %221, label %469

; <label>:221:                                    ; preds = %214
  %222 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %223 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %224 = bitcast i64** %222 to i64*
  %225 = bitcast %"class.std::vector"* %4 to i64*
  %226 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %227 = bitcast %"class.std::vector"* %4 to i8**
  %228 = load i64*, i64** %222, align 8, !tbaa !22
  br label %386

; <label>:229:                                    ; preds = %204, %296
  %230 = phi i64* [ %213, %204 ], [ %297, %296 ]
  %231 = phi i64 [ 0, %204 ], [ %298, %296 ]
  %232 = phi i64 [ 0, %204 ], [ %299, %296 ]
  %233 = getelementptr inbounds i64, i64* %205, i64 %231
  %234 = load i64*, i64** %207, align 8, !tbaa !28
  %235 = icmp eq i64* %230, %234
  %236 = ptrtoint i64* %230 to i64
  br i1 %235, label %240, label %237

; <label>:237:                                    ; preds = %229
  %238 = load i64, i64* %233, align 8, !tbaa !2
  store i64 %238, i64* %230, align 8, !tbaa !2
  %239 = getelementptr inbounds i64, i64* %230, i64 1
  store i64* %239, i64** %206, align 8, !tbaa !22
  br label %292

; <label>:240:                                    ; preds = %229
  %241 = load i64, i64* %209, align 8, !tbaa !23
  %242 = sub i64 %236, %241
  %243 = ashr exact i64 %242, 3
  %244 = icmp eq i64 %242, 0
  %245 = select i1 %244, i64 1, i64 %243
  %246 = add nsw i64 %245, %243
  %247 = icmp ult i64 %246, %243
  %248 = icmp ugt i64 %246, 2305843009213693951
  %249 = or i1 %247, %248
  %250 = select i1 %249, i64 2305843009213693951, i64 %246
  %251 = icmp eq i64 %250, 0
  %252 = inttoptr i64 %241 to i64*
  br i1 %251, label %263, label %253

; <label>:253:                                    ; preds = %240
  %254 = icmp ugt i64 %250, 2305843009213693951
  br i1 %254, label %255, label %257

; <label>:255:                                    ; preds = %253
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %256 unwind label %303

; <label>:256:                                    ; preds = %255
  unreachable

; <label>:257:                                    ; preds = %253
  %258 = shl i64 %250, 3
  %259 = invoke i8* @_Znwm(i64 %258)
          to label %260 unwind label %301

; <label>:260:                                    ; preds = %257
  %261 = bitcast i8* %259 to i64*
  %262 = load i64*, i64** %210, align 8, !tbaa !19
  br label %263

; <label>:263:                                    ; preds = %260, %240
  %264 = phi i64* [ %262, %260 ], [ %252, %240 ]
  %265 = phi i8* [ %259, %260 ], [ null, %240 ]
  %266 = phi i64* [ %261, %260 ], [ null, %240 ]
  %267 = getelementptr inbounds i64, i64* %266, i64 %243
  %268 = load i64, i64* %233, align 8, !tbaa !2
  store i64 %268, i64* %267, align 8, !tbaa !2
  %269 = ptrtoint i64* %264 to i64
  %270 = sub i64 %236, %269
  %271 = ashr exact i64 %270, 3
  %272 = icmp eq i64 %270, 0
  br i1 %272, label %275, label %273

; <label>:273:                                    ; preds = %263
  %274 = bitcast i64* %264 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %265, i8* %274, i64 %270, i32 8, i1 false) #2
  br label %275

; <label>:275:                                    ; preds = %273, %263
  %276 = getelementptr inbounds i64, i64* %266, i64 %271
  %277 = getelementptr inbounds i64, i64* %276, i64 1
  %278 = load i64, i64* %208, align 8, !tbaa !22
  %279 = sub i64 %278, %236
  %280 = ashr exact i64 %279, 3
  %281 = icmp eq i64 %279, 0
  br i1 %281, label %285, label %282

; <label>:282:                                    ; preds = %275
  %283 = bitcast i64* %277 to i8*
  %284 = bitcast i64* %230 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %283, i8* %284, i64 %279, i32 8, i1 false) #2
  br label %285

; <label>:285:                                    ; preds = %282, %275
  %286 = getelementptr inbounds i64, i64* %277, i64 %280
  %287 = icmp eq i64* %264, null
  br i1 %287, label %290, label %288

; <label>:288:                                    ; preds = %285
  %289 = bitcast i64* %264 to i8*
  call void @_ZdlPv(i8* %289) #2
  br label %290

; <label>:290:                                    ; preds = %288, %285
  store i8* %265, i8** %212, align 8, !tbaa !19
  store i64* %286, i64** %206, align 8, !tbaa !22
  %291 = getelementptr inbounds i64, i64* %266, i64 %250
  store i64* %291, i64** %207, align 8, !tbaa !28
  br label %292

; <label>:292:                                    ; preds = %290, %237
  %293 = phi i64* [ %291, %290 ], [ %234, %237 ]
  %294 = phi i64* [ %286, %290 ], [ %239, %237 ]
  br i1 %211, label %296, label %295

; <label>:295:                                    ; preds = %292
  br label %309

; <label>:296:                                    ; preds = %373, %292
  %297 = phi i64* [ %294, %292 ], [ %375, %373 ]
  %298 = add nuw i64 %231, 1
  %299 = add i64 %232, %200
  %300 = icmp ult i64 %298, %202
  br i1 %300, label %229, label %214

; <label>:301:                                    ; preds = %257
  %302 = landingpad { i8*, i32 }
          cleanup
  br label %305

; <label>:303:                                    ; preds = %255
  %304 = landingpad { i8*, i32 }
          cleanup
  br label %305

; <label>:305:                                    ; preds = %303, %301
  %306 = phi { i8*, i32 } [ %302, %301 ], [ %304, %303 ]
  %307 = extractvalue { i8*, i32 } %306, 0
  %308 = extractvalue { i8*, i32 } %306, 1
  br label %482

; <label>:309:                                    ; preds = %295, %373
  %310 = phi i64* [ %374, %373 ], [ %293, %295 ]
  %311 = phi i64* [ %375, %373 ], [ %294, %295 ]
  %312 = phi i64 [ %376, %373 ], [ 0, %295 ]
  %313 = add i64 %312, %232
  %314 = load i64*, i64** %168, align 8, !tbaa !19
  %315 = getelementptr inbounds i64, i64* %314, i64 %313
  %316 = icmp eq i64* %311, %310
  %317 = ptrtoint i64* %311 to i64
  br i1 %316, label %321, label %318

; <label>:318:                                    ; preds = %309
  %319 = load i64, i64* %315, align 8, !tbaa !2
  store i64 %319, i64* %311, align 8, !tbaa !2
  %320 = getelementptr inbounds i64, i64* %311, i64 1
  store i64* %320, i64** %206, align 8, !tbaa !22
  br label %373

; <label>:321:                                    ; preds = %309
  %322 = load i64, i64* %209, align 8, !tbaa !23
  %323 = sub i64 %317, %322
  %324 = ashr exact i64 %323, 3
  %325 = icmp eq i64 %323, 0
  %326 = select i1 %325, i64 1, i64 %324
  %327 = add nsw i64 %326, %324
  %328 = icmp ult i64 %327, %324
  %329 = icmp ugt i64 %327, 2305843009213693951
  %330 = or i1 %328, %329
  %331 = select i1 %330, i64 2305843009213693951, i64 %327
  %332 = icmp eq i64 %331, 0
  %333 = inttoptr i64 %322 to i64*
  br i1 %332, label %344, label %334

; <label>:334:                                    ; preds = %321
  %335 = icmp ugt i64 %331, 2305843009213693951
  br i1 %335, label %336, label %338

; <label>:336:                                    ; preds = %334
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %337 unwind label %380

; <label>:337:                                    ; preds = %336
  unreachable

; <label>:338:                                    ; preds = %334
  %339 = shl i64 %331, 3
  %340 = invoke i8* @_Znwm(i64 %339)
          to label %341 unwind label %378

; <label>:341:                                    ; preds = %338
  %342 = bitcast i8* %340 to i64*
  %343 = load i64*, i64** %210, align 8, !tbaa !19
  br label %344

; <label>:344:                                    ; preds = %341, %321
  %345 = phi i64* [ %343, %341 ], [ %333, %321 ]
  %346 = phi i8* [ %340, %341 ], [ null, %321 ]
  %347 = phi i64* [ %342, %341 ], [ null, %321 ]
  %348 = getelementptr inbounds i64, i64* %347, i64 %324
  %349 = load i64, i64* %315, align 8, !tbaa !2
  store i64 %349, i64* %348, align 8, !tbaa !2
  %350 = ptrtoint i64* %345 to i64
  %351 = sub i64 %317, %350
  %352 = ashr exact i64 %351, 3
  %353 = icmp eq i64 %351, 0
  br i1 %353, label %356, label %354

; <label>:354:                                    ; preds = %344
  %355 = bitcast i64* %345 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %346, i8* %355, i64 %351, i32 8, i1 false) #2
  br label %356

; <label>:356:                                    ; preds = %354, %344
  %357 = getelementptr inbounds i64, i64* %347, i64 %352
  %358 = getelementptr inbounds i64, i64* %357, i64 1
  %359 = load i64, i64* %208, align 8, !tbaa !22
  %360 = sub i64 %359, %317
  %361 = ashr exact i64 %360, 3
  %362 = icmp eq i64 %360, 0
  br i1 %362, label %366, label %363

; <label>:363:                                    ; preds = %356
  %364 = bitcast i64* %358 to i8*
  %365 = bitcast i64* %310 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %364, i8* %365, i64 %360, i32 8, i1 false) #2
  br label %366

; <label>:366:                                    ; preds = %363, %356
  %367 = getelementptr inbounds i64, i64* %358, i64 %361
  %368 = icmp eq i64* %345, null
  br i1 %368, label %371, label %369

; <label>:369:                                    ; preds = %366
  %370 = bitcast i64* %345 to i8*
  call void @_ZdlPv(i8* %370) #2
  br label %371

; <label>:371:                                    ; preds = %369, %366
  store i8* %346, i8** %212, align 8, !tbaa !19
  store i64* %367, i64** %206, align 8, !tbaa !22
  %372 = getelementptr inbounds i64, i64* %347, i64 %331
  store i64* %372, i64** %207, align 8, !tbaa !28
  br label %373

; <label>:373:                                    ; preds = %371, %318
  %374 = phi i64* [ %372, %371 ], [ %310, %318 ]
  %375 = phi i64* [ %367, %371 ], [ %320, %318 ]
  %376 = add nuw i64 %312, 1
  %377 = icmp ult i64 %376, %200
  br i1 %377, label %309, label %296

; <label>:378:                                    ; preds = %338
  %379 = landingpad { i8*, i32 }
          cleanup
  br label %382

; <label>:380:                                    ; preds = %336
  %381 = landingpad { i8*, i32 }
          cleanup
  br label %382

; <label>:382:                                    ; preds = %380, %378
  %383 = phi { i8*, i32 } [ %379, %378 ], [ %381, %380 ]
  %384 = extractvalue { i8*, i32 } %383, 0
  %385 = extractvalue { i8*, i32 } %383, 1
  br label %482

; <label>:386:                                    ; preds = %221, %453
  %387 = phi i64 [ %217, %221 ], [ %454, %453 ]
  %388 = phi i64 [ %216, %221 ], [ %455, %453 ]
  %389 = phi i64* [ %228, %221 ], [ %456, %453 ]
  %390 = phi i64 [ %215, %221 ], [ %457, %453 ]
  %391 = inttoptr i64 %387 to i64*
  %392 = getelementptr inbounds i64, i64* %391, i64 %390
  %393 = load i64*, i64** %223, align 8, !tbaa !28
  %394 = icmp eq i64* %389, %393
  %395 = ptrtoint i64* %389 to i64
  br i1 %394, label %399, label %396

; <label>:396:                                    ; preds = %386
  %397 = load i64, i64* %392, align 8, !tbaa !2
  store i64 %397, i64* %389, align 8, !tbaa !2
  %398 = getelementptr inbounds i64, i64* %389, i64 1
  store i64* %398, i64** %222, align 8, !tbaa !22
  br label %453

; <label>:399:                                    ; preds = %386
  %400 = load i64, i64* %225, align 8, !tbaa !23
  %401 = sub i64 %395, %400
  %402 = ashr exact i64 %401, 3
  %403 = icmp eq i64 %401, 0
  %404 = select i1 %403, i64 1, i64 %402
  %405 = add nsw i64 %404, %402
  %406 = icmp ult i64 %405, %402
  %407 = icmp ugt i64 %405, 2305843009213693951
  %408 = or i1 %406, %407
  %409 = select i1 %408, i64 2305843009213693951, i64 %405
  %410 = icmp eq i64 %409, 0
  %411 = inttoptr i64 %400 to i64*
  br i1 %410, label %422, label %412

; <label>:412:                                    ; preds = %399
  %413 = icmp ugt i64 %409, 2305843009213693951
  br i1 %413, label %414, label %416

; <label>:414:                                    ; preds = %412
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %415 unwind label %463

; <label>:415:                                    ; preds = %414
  unreachable

; <label>:416:                                    ; preds = %412
  %417 = shl i64 %409, 3
  %418 = invoke i8* @_Znwm(i64 %417)
          to label %419 unwind label %461

; <label>:419:                                    ; preds = %416
  %420 = bitcast i8* %418 to i64*
  %421 = load i64*, i64** %226, align 8, !tbaa !19
  br label %422

; <label>:422:                                    ; preds = %419, %399
  %423 = phi i64* [ %421, %419 ], [ %411, %399 ]
  %424 = phi i8* [ %418, %419 ], [ null, %399 ]
  %425 = phi i64* [ %420, %419 ], [ null, %399 ]
  %426 = getelementptr inbounds i64, i64* %425, i64 %402
  %427 = load i64, i64* %392, align 8, !tbaa !2
  store i64 %427, i64* %426, align 8, !tbaa !2
  %428 = ptrtoint i64* %423 to i64
  %429 = sub i64 %395, %428
  %430 = ashr exact i64 %429, 3
  %431 = icmp eq i64 %429, 0
  br i1 %431, label %434, label %432

; <label>:432:                                    ; preds = %422
  %433 = bitcast i64* %423 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %424, i8* %433, i64 %429, i32 8, i1 false) #2
  br label %434

; <label>:434:                                    ; preds = %432, %422
  %435 = getelementptr inbounds i64, i64* %425, i64 %430
  %436 = getelementptr inbounds i64, i64* %435, i64 1
  %437 = load i64, i64* %224, align 8, !tbaa !22
  %438 = sub i64 %437, %395
  %439 = ashr exact i64 %438, 3
  %440 = icmp eq i64 %438, 0
  br i1 %440, label %444, label %441

; <label>:441:                                    ; preds = %434
  %442 = bitcast i64* %436 to i8*
  %443 = bitcast i64* %389 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %442, i8* %443, i64 %438, i32 8, i1 false) #2
  br label %444

; <label>:444:                                    ; preds = %441, %434
  %445 = getelementptr inbounds i64, i64* %436, i64 %439
  %446 = icmp eq i64* %423, null
  br i1 %446, label %449, label %447

; <label>:447:                                    ; preds = %444
  %448 = bitcast i64* %423 to i8*
  call void @_ZdlPv(i8* %448) #2
  br label %449

; <label>:449:                                    ; preds = %447, %444
  store i8* %424, i8** %227, align 8, !tbaa !19
  store i64* %445, i64** %222, align 8, !tbaa !22
  %450 = getelementptr inbounds i64, i64* %425, i64 %409
  store i64* %450, i64** %223, align 8, !tbaa !28
  %451 = load i64, i64* %33, align 8, !tbaa !22
  %452 = load i64, i64* %13, align 8, !tbaa !19
  br label %453

; <label>:453:                                    ; preds = %449, %396
  %454 = phi i64 [ %452, %449 ], [ %387, %396 ]
  %455 = phi i64 [ %451, %449 ], [ %388, %396 ]
  %456 = phi i64* [ %445, %449 ], [ %398, %396 ]
  %457 = add nuw i64 %390, 1
  %458 = sub i64 %455, %454
  %459 = ashr exact i64 %458, 3
  %460 = icmp ult i64 %457, %459
  br i1 %460, label %386, label %469

; <label>:461:                                    ; preds = %416
  %462 = landingpad { i8*, i32 }
          cleanup
  br label %465

; <label>:463:                                    ; preds = %469, %414
  %464 = landingpad { i8*, i32 }
          cleanup
  br label %465

; <label>:465:                                    ; preds = %463, %461
  %466 = phi { i8*, i32 } [ %462, %461 ], [ %464, %463 ]
  %467 = extractvalue { i8*, i32 } %466, 0
  %468 = extractvalue { i8*, i32 } %466, 1
  br label %482

; <label>:469:                                    ; preds = %453, %214
  %470 = invoke dereferenceable(24) %"class.std::vector"* @_ZNSt6vectorImSaImEEaSERKS1_(%"class.std::vector"* nonnull %0, %"class.std::vector"* nonnull dereferenceable(24) %4)
          to label %471 unwind label %463

; <label>:471:                                    ; preds = %469
  %472 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %473 = load i64*, i64** %472, align 8, !tbaa !19
  %474 = icmp eq i64* %473, null
  br i1 %474, label %477, label %475

; <label>:475:                                    ; preds = %471
  %476 = bitcast i64* %473 to i8*
  call void @_ZdlPv(i8* %476) #2
  br label %477

; <label>:477:                                    ; preds = %471, %475
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %478 = icmp eq i64 %75, 0
  br i1 %478, label %481, label %479

; <label>:479:                                    ; preds = %477
  %480 = inttoptr i64 %75 to i8*
  call void @_ZdlPv(i8* %480) #2
  br label %481

; <label>:481:                                    ; preds = %477, %479
  ret void

; <label>:482:                                    ; preds = %465, %382, %305, %159, %67, %54
  %483 = phi i64 [ %55, %54 ], [ %95, %159 ], [ %75, %382 ], [ %75, %305 ], [ %75, %465 ], [ 0, %67 ]
  %484 = phi i32 [ %58, %54 ], [ %162, %159 ], [ %385, %382 ], [ %308, %305 ], [ %468, %465 ], [ %62, %67 ]
  %485 = phi i8* [ %57, %54 ], [ %161, %159 ], [ %384, %382 ], [ %307, %305 ], [ %467, %465 ], [ %61, %67 ]
  %486 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %487 = load i64*, i64** %486, align 8, !tbaa !19
  %488 = icmp eq i64* %487, null
  br i1 %488, label %491, label %489

; <label>:489:                                    ; preds = %482
  %490 = bitcast i64* %487 to i8*
  call void @_ZdlPv(i8* %490) #2
  br label %491

; <label>:491:                                    ; preds = %482, %489
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %492 = icmp eq i64 %483, 0
  br i1 %492, label %495, label %493

; <label>:493:                                    ; preds = %491
  %494 = inttoptr i64 %483 to i8*
  call void @_ZdlPv(i8* %494) #2
  br label %495

; <label>:495:                                    ; preds = %491, %493
  %496 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %497 = load i64*, i64** %496, align 8, !tbaa !19
  %498 = icmp eq i64* %497, null
  br i1 %498, label %501, label %499

; <label>:499:                                    ; preds = %495
  %500 = bitcast i64* %497 to i8*
  call void @_ZdlPv(i8* %500) #2
  br label %501

; <label>:501:                                    ; preds = %495, %499
  %502 = insertvalue { i8*, i32 } undef, i8* %485, 0
  %503 = insertvalue { i8*, i32 } %502, i32 %484, 1
  resume { i8*, i32 } %503
}

; Function Attrs: uwtable
define linkonce_odr void @_ZN13Int_Generator18reverse_sorted_endEmm(%"class.std::vector"* noalias sret, i64, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %4 = alloca %"class.std::__cxx11::basic_string", align 8
  %5 = bitcast %"class.std::vector"* %0 to i8*
  tail call void @llvm.memset.p0i8.i64(i8* %5, i8 0, i64 24, i32 8, i1 false) #2
  %6 = icmp ugt i64 %1, 2305843009213693951
  br i1 %6, label %7, label %9

; <label>:7:                                      ; preds = %3
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %8 unwind label %55

; <label>:8:                                      ; preds = %7
  unreachable

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %11 = icmp eq i64 %1, 0
  %12 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br i1 %11, label %28, label %13

; <label>:13:                                     ; preds = %9
  %14 = shl i64 %1, 3
  %15 = invoke i8* @_Znwm(i64 %14)
          to label %16 unwind label %55

; <label>:16:                                     ; preds = %13
  %17 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %18 = bitcast i8* %15 to i64*
  %19 = load i64*, i64** %17, align 8, !tbaa !19
  %20 = icmp eq i64* %19, null
  br i1 %20, label %23, label %21

; <label>:21:                                     ; preds = %16
  %22 = bitcast i64* %19 to i8*
  tail call void @_ZdlPv(i8* %22) #2
  br label %23

; <label>:23:                                     ; preds = %21, %16
  %24 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %15, i8** %24, align 8, !tbaa !19
  %25 = bitcast i64** %12 to i8**
  store i8* %15, i8** %25, align 8, !tbaa !22
  %26 = getelementptr inbounds i64, i64* %18, i64 %1
  store i64* %26, i64** %10, align 8, !tbaa !28
  %27 = ptrtoint i8* %15 to i64
  br label %28

; <label>:28:                                     ; preds = %9, %23
  %29 = phi i64 [ %27, %23 ], [ 0, %9 ]
  %30 = bitcast i64** %12 to i64*
  store i64 %29, i64* %30, align 8, !tbaa !22
  %31 = bitcast %"class.std::__cxx11::basic_string"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* nonnull %31) #2
  %32 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 2
  %33 = bitcast %"class.std::__cxx11::basic_string"* %4 to %union.anon**
  store %union.anon* %32, %union.anon** %33, align 8, !tbaa !15
  %34 = bitcast %union.anon* %32 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %34, i8* nonnull getelementptr inbounds ([10 x i8], [10 x i8]* @.str.3, i64 0, i64 0), i64 9, i32 1, i1 false) #2
  %35 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 1
  store i64 9, i64* %35, align 8, !tbaa !17
  %36 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 2, i32 1, i64 1
  store i8 0, i8* %36, align 1, !tbaa !14
  %37 = add i64 %2, %1
  invoke fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %4, %"class.std::vector"* nonnull dereferenceable(24) %0, i64 %37)
          to label %38 unwind label %59

; <label>:38:                                     ; preds = %28
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %40 = load i8*, i8** %39, align 8, !tbaa !32
  %41 = icmp eq i8* %40, %34
  br i1 %41, label %43, label %42

; <label>:42:                                     ; preds = %38
  call void @_ZdlPv(i8* %40) #2
  br label %43

; <label>:43:                                     ; preds = %38, %42
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  %44 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %45 = load i64*, i64** %44, align 8, !tbaa !23
  %46 = getelementptr inbounds i64, i64* %45, i64 %1
  %47 = icmp eq i64 %1, 0
  br i1 %47, label %104, label %48

; <label>:48:                                     ; preds = %43
  %49 = shl nuw i64 %1, 3
  %50 = ashr exact i64 %49, 3
  %51 = call i64 @llvm.ctlz.i64(i64 %50, i1 true) #2, !range !24
  %52 = shl nuw nsw i64 %51, 1
  %53 = xor i64 %52, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %45, i64* %46, i64 %53)
          to label %54 unwind label %55

; <label>:54:                                     ; preds = %48
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %45, i64* %46)
          to label %68 unwind label %55

; <label>:55:                                     ; preds = %54, %48, %13, %7
  %56 = landingpad { i8*, i32 }
          cleanup
  %57 = extractvalue { i8*, i32 } %56, 0
  %58 = extractvalue { i8*, i32 } %56, 1
  br label %105

; <label>:59:                                     ; preds = %28
  %60 = landingpad { i8*, i32 }
          cleanup
  %61 = extractvalue { i8*, i32 } %60, 0
  %62 = extractvalue { i8*, i32 } %60, 1
  %63 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %64 = load i8*, i8** %63, align 8, !tbaa !32
  %65 = icmp eq i8* %64, %34
  br i1 %65, label %67, label %66

; <label>:66:                                     ; preds = %59
  call void @_ZdlPv(i8* %64) #2
  br label %67

; <label>:67:                                     ; preds = %66, %59
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  br label %105

; <label>:68:                                     ; preds = %54
  %69 = lshr i64 %1, 1
  %70 = icmp eq i64 %69, 0
  br i1 %70, label %104, label %71

; <label>:71:                                     ; preds = %68
  %72 = load i64*, i64** %44, align 8, !tbaa !19
  %73 = add i64 %1, -1
  %74 = and i64 %69, 1
  %75 = icmp eq i64 %69, 1
  br i1 %75, label %95, label %76

; <label>:76:                                     ; preds = %71
  %77 = sub nsw i64 %69, %74
  br label %78

; <label>:78:                                     ; preds = %78, %76
  %79 = phi i64 [ 0, %76 ], [ %92, %78 ]
  %80 = phi i64 [ %77, %76 ], [ %93, %78 ]
  %81 = getelementptr inbounds i64, i64* %72, i64 %79
  %82 = sub i64 %73, %79
  %83 = getelementptr inbounds i64, i64* %72, i64 %82
  %84 = load i64, i64* %81, align 8, !tbaa !2
  %85 = load i64, i64* %83, align 8, !tbaa !2
  store i64 %85, i64* %81, align 8, !tbaa !2
  store i64 %84, i64* %83, align 8, !tbaa !2
  %86 = or i64 %79, 1
  %87 = getelementptr inbounds i64, i64* %72, i64 %86
  %88 = sub i64 %73, %86
  %89 = getelementptr inbounds i64, i64* %72, i64 %88
  %90 = load i64, i64* %87, align 8, !tbaa !2
  %91 = load i64, i64* %89, align 8, !tbaa !2
  store i64 %91, i64* %87, align 8, !tbaa !2
  store i64 %90, i64* %89, align 8, !tbaa !2
  %92 = add nuw nsw i64 %79, 2
  %93 = add i64 %80, -2
  %94 = icmp eq i64 %93, 0
  br i1 %94, label %95, label %78

; <label>:95:                                     ; preds = %78, %71
  %96 = phi i64 [ 0, %71 ], [ %92, %78 ]
  %97 = icmp eq i64 %74, 0
  br i1 %97, label %104, label %98

; <label>:98:                                     ; preds = %95
  %99 = getelementptr inbounds i64, i64* %72, i64 %96
  %100 = sub i64 %73, %96
  %101 = getelementptr inbounds i64, i64* %72, i64 %100
  %102 = load i64, i64* %99, align 8, !tbaa !2
  %103 = load i64, i64* %101, align 8, !tbaa !2
  store i64 %103, i64* %99, align 8, !tbaa !2
  store i64 %102, i64* %101, align 8, !tbaa !2
  br label %104

; <label>:104:                                    ; preds = %98, %95, %43, %68
  ret void

; <label>:105:                                    ; preds = %67, %55
  %106 = phi i32 [ %58, %55 ], [ %62, %67 ]
  %107 = phi i8* [ %57, %55 ], [ %61, %67 ]
  %108 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %109 = load i64*, i64** %108, align 8, !tbaa !19
  %110 = icmp eq i64* %109, null
  br i1 %110, label %113, label %111

; <label>:111:                                    ; preds = %105
  %112 = bitcast i64* %109 to i8*
  call void @_ZdlPv(i8* %112) #2
  br label %113

; <label>:113:                                    ; preds = %105, %111
  %114 = insertvalue { i8*, i32 } undef, i8* %107, 0
  %115 = insertvalue { i8*, i32 } %114, i32 %106, 1
  resume { i8*, i32 } %115
}

; Function Attrs: uwtable
define linkonce_odr void @_ZN13Int_Generator21reverse_sorted_middleEmm(%"class.std::vector"* noalias sret, i64, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %4 = alloca %"class.std::vector", align 8
  %5 = alloca %"class.std::__cxx11::basic_string", align 8
  %6 = bitcast %"class.std::vector"* %0 to i8*
  tail call void @llvm.memset.p0i8.i64(i8* %6, i8 0, i64 24, i32 8, i1 false) #2
  %7 = bitcast %"class.std::vector"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %7) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %7, i8 0, i64 24, i32 8, i1 false) #2
  %8 = icmp ugt i64 %1, 2305843009213693951
  br i1 %8, label %9, label %11

; <label>:9:                                      ; preds = %3
  invoke void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.5, i64 0, i64 0)) #16
          to label %10 unwind label %54

; <label>:10:                                     ; preds = %9
  unreachable

; <label>:11:                                     ; preds = %3
  %12 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %13 = bitcast %"class.std::vector"* %0 to i64*
  %14 = icmp eq i64 %1, 0
  %15 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br i1 %14, label %31, label %16

; <label>:16:                                     ; preds = %11
  %17 = shl i64 %1, 3
  %18 = invoke i8* @_Znwm(i64 %17)
          to label %19 unwind label %54

; <label>:19:                                     ; preds = %16
  %20 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %21 = bitcast i8* %18 to i64*
  %22 = load i64*, i64** %20, align 8, !tbaa !19
  %23 = icmp eq i64* %22, null
  br i1 %23, label %26, label %24

; <label>:24:                                     ; preds = %19
  %25 = bitcast i64* %22 to i8*
  tail call void @_ZdlPv(i8* %25) #2
  br label %26

; <label>:26:                                     ; preds = %24, %19
  %27 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %18, i8** %27, align 8, !tbaa !19
  %28 = bitcast i64** %15 to i8**
  store i8* %18, i8** %28, align 8, !tbaa !22
  %29 = getelementptr inbounds i64, i64* %21, i64 %1
  store i64* %29, i64** %12, align 8, !tbaa !28
  %30 = ptrtoint i8* %18 to i64
  br label %31

; <label>:31:                                     ; preds = %11, %26
  %32 = phi i64 [ %30, %26 ], [ 0, %11 ]
  %33 = bitcast i64** %15 to i64*
  store i64 %32, i64* %33, align 8, !tbaa !22
  %34 = bitcast %"class.std::__cxx11::basic_string"* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* nonnull %34) #2
  %35 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 2
  %36 = bitcast %"class.std::__cxx11::basic_string"* %5 to %union.anon**
  store %union.anon* %35, %union.anon** %36, align 8, !tbaa !15
  %37 = bitcast %union.anon* %35 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %37, i8* nonnull getelementptr inbounds ([10 x i8], [10 x i8]* @.str.3, i64 0, i64 0), i64 9, i32 1, i1 false) #2
  %38 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 1
  store i64 9, i64* %38, align 8, !tbaa !17
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 2, i32 1, i64 1
  store i8 0, i8* %39, align 1, !tbaa !14
  %40 = add i64 %2, %1
  invoke fastcc void @_ZN5boost4sort6commonL18fill_vector_uint64ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEERSt6vectorImSaImEEm(%"class.std::__cxx11::basic_string"* nonnull dereferenceable(32) %5, %"class.std::vector"* nonnull dereferenceable(24) %0, i64 %40)
          to label %41 unwind label %59

; <label>:41:                                     ; preds = %31
  %42 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %43 = load i8*, i8** %42, align 8, !tbaa !32
  %44 = icmp eq i8* %43, %37
  br i1 %44, label %46, label %45

; <label>:45:                                     ; preds = %41
  call void @_ZdlPv(i8* %43) #2
  br label %46

; <label>:46:                                     ; preds = %41, %45
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  %47 = load i64, i64* %33, align 8, !tbaa !22
  %48 = load i64, i64* %13, align 8, !tbaa !19
  %49 = sub i64 %47, %48
  %50 = ashr exact i64 %49, 3
  %51 = icmp ugt i64 %50, %1
  %52 = inttoptr i64 %48 to i64*
  br i1 %51, label %53, label %70

; <label>:53:                                     ; preds = %46
  br label %87

; <label>:54:                                     ; preds = %188, %180, %78, %16, %9
  %55 = phi i64 [ 0, %9 ], [ %75, %188 ], [ %75, %180 ], [ %75, %78 ], [ 0, %16 ]
  %56 = landingpad { i8*, i32 }
          cleanup
  %57 = extractvalue { i8*, i32 } %56, 0
  %58 = extractvalue { i8*, i32 } %56, 1
  br label %482

; <label>:59:                                     ; preds = %31
  %60 = landingpad { i8*, i32 }
          cleanup
  %61 = extractvalue { i8*, i32 } %60, 0
  %62 = extractvalue { i8*, i32 } %60, 1
  %63 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %64 = load i8*, i8** %63, align 8, !tbaa !32
  %65 = icmp eq i8* %64, %37
  br i1 %65, label %67, label %66

; <label>:66:                                     ; preds = %59
  call void @_ZdlPv(i8* %64) #2
  br label %67

; <label>:67:                                     ; preds = %66, %59
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  br label %482

; <label>:68:                                     ; preds = %140
  %69 = ptrtoint i64* %149 to i64
  br label %70

; <label>:70:                                     ; preds = %68, %46
  %71 = phi i64* [ %52, %46 ], [ %141, %68 ]
  %72 = phi i64* [ %52, %46 ], [ %142, %68 ]
  %73 = phi i64* [ %52, %46 ], [ %143, %68 ]
  %74 = phi i64 [ 0, %46 ], [ %69, %68 ]
  %75 = phi i64 [ 0, %46 ], [ %147, %68 ]
  %76 = phi i64 [ %50, %46 ], [ %153, %68 ]
  %77 = icmp ult i64 %76, %1
  br i1 %77, label %78, label %83

; <label>:78:                                     ; preds = %70
  %79 = sub i64 %1, %76
  invoke void @_ZNSt6vectorImSaImEE17_M_default_appendEm(%"class.std::vector"* nonnull %0, i64 %79)
          to label %80 unwind label %54

; <label>:80:                                     ; preds = %78
  %81 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %82 = load i64*, i64** %81, align 8, !tbaa !23
  br label %163

; <label>:83:                                     ; preds = %70
  %84 = icmp ugt i64 %76, %1
  br i1 %84, label %85, label %163

; <label>:85:                                     ; preds = %83
  %86 = getelementptr inbounds i64, i64* %71, i64 %1
  store i64* %86, i64** %15, align 8, !tbaa !22
  br label %163

; <label>:87:                                     ; preds = %53, %140
  %88 = phi i64* [ %142, %140 ], [ %52, %53 ]
  %89 = phi i64* [ %143, %140 ], [ %52, %53 ]
  %90 = phi i64 [ %144, %140 ], [ %48, %53 ]
  %91 = phi i64 [ %145, %140 ], [ %47, %53 ]
  %92 = phi i64* [ %141, %140 ], [ %52, %53 ]
  %93 = phi i64 [ %151, %140 ], [ %1, %53 ]
  %94 = phi i64* [ %148, %140 ], [ null, %53 ]
  %95 = phi i64 [ %147, %140 ], [ 0, %53 ]
  %96 = phi i64 [ %150, %140 ], [ 0, %53 ]
  %97 = getelementptr inbounds i64, i64* %92, i64 %93
  %98 = inttoptr i64 %96 to i64*
  %99 = icmp eq i64* %94, %98
  br i1 %99, label %103, label %100

; <label>:100:                                    ; preds = %87
  %101 = load i64, i64* %97, align 8, !tbaa !2
  store i64 %101, i64* %98, align 8, !tbaa !2
  %102 = inttoptr i64 %90 to i64*
  br label %140

; <label>:103:                                    ; preds = %87
  %104 = sub i64 %96, %95
  %105 = ashr exact i64 %104, 3
  %106 = icmp eq i64 %104, 0
  %107 = select i1 %106, i64 1, i64 %105
  %108 = add nsw i64 %107, %105
  %109 = icmp ult i64 %108, %105
  %110 = icmp ugt i64 %108, 2305843009213693951
  %111 = or i1 %109, %110
  %112 = select i1 %111, i64 2305843009213693951, i64 %108
  %113 = icmp eq i64 %112, 0
  br i1 %113, label %123, label %114

; <label>:114:                                    ; preds = %103
  %115 = icmp ugt i64 %112, 2305843009213693951
  br i1 %115, label %116, label %118

; <label>:116:                                    ; preds = %114
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %117 unwind label %157

; <label>:117:                                    ; preds = %116
  unreachable

; <label>:118:                                    ; preds = %114
  %119 = shl i64 %112, 3
  %120 = invoke i8* @_Znwm(i64 %119)
          to label %121 unwind label %155

; <label>:121:                                    ; preds = %118
  %122 = bitcast i8* %120 to i64*
  br label %123

; <label>:123:                                    ; preds = %121, %103
  %124 = phi i8* [ %120, %121 ], [ null, %103 ]
  %125 = phi i64* [ %122, %121 ], [ null, %103 ]
  %126 = getelementptr inbounds i64, i64* %125, i64 %105
  %127 = load i64, i64* %97, align 8, !tbaa !2
  store i64 %127, i64* %126, align 8, !tbaa !2
  br i1 %106, label %130, label %128

; <label>:128:                                    ; preds = %123
  %129 = inttoptr i64 %95 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %124, i8* %129, i64 %104, i32 8, i1 false) #2
  br label %130

; <label>:130:                                    ; preds = %123, %128
  %131 = icmp eq i64 %95, 0
  br i1 %131, label %134, label %132

; <label>:132:                                    ; preds = %130
  %133 = inttoptr i64 %95 to i8*
  call void @_ZdlPv(i8* %133) #2
  br label %134

; <label>:134:                                    ; preds = %132, %130
  %135 = ptrtoint i8* %124 to i64
  %136 = getelementptr inbounds i64, i64* %125, i64 %112
  %137 = load i64, i64* %33, align 8, !tbaa !22
  %138 = load i64, i64* %13, align 8, !tbaa !19
  %139 = inttoptr i64 %138 to i64*
  br label %140

; <label>:140:                                    ; preds = %134, %100
  %141 = phi i64* [ %139, %134 ], [ %102, %100 ]
  %142 = phi i64* [ %139, %134 ], [ %88, %100 ]
  %143 = phi i64* [ %139, %134 ], [ %89, %100 ]
  %144 = phi i64 [ %138, %134 ], [ %90, %100 ]
  %145 = phi i64 [ %137, %134 ], [ %91, %100 ]
  %146 = phi i64* [ %126, %134 ], [ %98, %100 ]
  %147 = phi i64 [ %135, %134 ], [ %95, %100 ]
  %148 = phi i64* [ %136, %134 ], [ %94, %100 ]
  %149 = getelementptr inbounds i64, i64* %146, i64 1
  %150 = ptrtoint i64* %149 to i64
  %151 = add nuw i64 %93, 1
  %152 = sub i64 %145, %144
  %153 = ashr exact i64 %152, 3
  %154 = icmp ult i64 %151, %153
  br i1 %154, label %87, label %68

; <label>:155:                                    ; preds = %118
  %156 = landingpad { i8*, i32 }
          cleanup
  br label %159

; <label>:157:                                    ; preds = %116
  %158 = landingpad { i8*, i32 }
          cleanup
  br label %159

; <label>:159:                                    ; preds = %157, %155
  %160 = phi { i8*, i32 } [ %156, %155 ], [ %158, %157 ]
  %161 = extractvalue { i8*, i32 } %160, 0
  %162 = extractvalue { i8*, i32 } %160, 1
  br label %482

; <label>:163:                                    ; preds = %80, %85, %83
  %164 = phi i64* [ %82, %80 ], [ %72, %85 ], [ %72, %83 ]
  %165 = phi i64* [ %82, %80 ], [ %73, %85 ], [ %73, %83 ]
  %166 = lshr i64 %1, 1
  %167 = icmp eq i64 %166, 0
  %168 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  br i1 %167, label %176, label %169

; <label>:169:                                    ; preds = %163
  %170 = add i64 %1, -1
  %171 = getelementptr inbounds i64, i64* %165, i64 %170
  %172 = load i64, i64* %165, align 8, !tbaa !2
  %173 = load i64, i64* %171, align 8, !tbaa !2
  store i64 %173, i64* %165, align 8, !tbaa !2
  store i64 %172, i64* %171, align 8, !tbaa !2
  %174 = icmp eq i64 %166, 1
  br i1 %174, label %176, label %175

; <label>:175:                                    ; preds = %169
  br label %189

; <label>:176:                                    ; preds = %189, %169, %163
  %177 = phi i64* [ %165, %163 ], [ %164, %169 ], [ %164, %189 ]
  %178 = load i64*, i64** %15, align 8, !tbaa !23
  %179 = icmp eq i64* %177, %178
  br i1 %179, label %198, label %180

; <label>:180:                                    ; preds = %176
  %181 = ptrtoint i64* %178 to i64
  %182 = ptrtoint i64* %177 to i64
  %183 = sub i64 %181, %182
  %184 = ashr exact i64 %183, 3
  %185 = call i64 @llvm.ctlz.i64(i64 %184, i1 true) #2, !range !24
  %186 = shl nuw nsw i64 %185, 1
  %187 = xor i64 %186, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %177, i64* %178, i64 %187)
          to label %188 unwind label %54

; <label>:188:                                    ; preds = %180
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %177, i64* %178)
          to label %198 unwind label %54

; <label>:189:                                    ; preds = %175, %189
  %190 = phi i64 [ %196, %189 ], [ 1, %175 ]
  %191 = getelementptr inbounds i64, i64* %164, i64 %190
  %192 = sub i64 %170, %190
  %193 = getelementptr inbounds i64, i64* %164, i64 %192
  %194 = load i64, i64* %191, align 8, !tbaa !2
  %195 = load i64, i64* %193, align 8, !tbaa !2
  store i64 %195, i64* %191, align 8, !tbaa !2
  store i64 %194, i64* %193, align 8, !tbaa !2
  %196 = add nuw nsw i64 %190, 1
  %197 = icmp eq i64 %196, %166
  br i1 %197, label %176, label %189, !llvm.loop !48

; <label>:198:                                    ; preds = %176, %188
  %199 = udiv i64 %1, %2
  %200 = add i64 %199, 1
  %201 = sub i64 %74, %75
  %202 = ashr exact i64 %201, 3
  %203 = icmp eq i64 %201, 0
  br i1 %203, label %214, label %204

; <label>:204:                                    ; preds = %198
  %205 = inttoptr i64 %75 to i64*
  %206 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %207 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %208 = bitcast i64** %206 to i64*
  %209 = bitcast %"class.std::vector"* %4 to i64*
  %210 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %211 = icmp eq i64 %200, 0
  %212 = bitcast %"class.std::vector"* %4 to i8**
  %213 = load i64*, i64** %206, align 8, !tbaa !22
  br label %229

; <label>:214:                                    ; preds = %296, %198
  %215 = phi i64 [ 0, %198 ], [ %299, %296 ]
  %216 = load i64, i64* %33, align 8, !tbaa !22
  %217 = load i64, i64* %13, align 8, !tbaa !19
  %218 = sub i64 %216, %217
  %219 = ashr exact i64 %218, 3
  %220 = icmp ult i64 %215, %219
  br i1 %220, label %221, label %469

; <label>:221:                                    ; preds = %214
  %222 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %223 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %224 = bitcast i64** %222 to i64*
  %225 = bitcast %"class.std::vector"* %4 to i64*
  %226 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %227 = bitcast %"class.std::vector"* %4 to i8**
  %228 = load i64*, i64** %222, align 8, !tbaa !22
  br label %386

; <label>:229:                                    ; preds = %204, %296
  %230 = phi i64* [ %213, %204 ], [ %297, %296 ]
  %231 = phi i64 [ 0, %204 ], [ %298, %296 ]
  %232 = phi i64 [ 0, %204 ], [ %299, %296 ]
  %233 = getelementptr inbounds i64, i64* %205, i64 %231
  %234 = load i64*, i64** %207, align 8, !tbaa !28
  %235 = icmp eq i64* %230, %234
  %236 = ptrtoint i64* %230 to i64
  br i1 %235, label %240, label %237

; <label>:237:                                    ; preds = %229
  %238 = load i64, i64* %233, align 8, !tbaa !2
  store i64 %238, i64* %230, align 8, !tbaa !2
  %239 = getelementptr inbounds i64, i64* %230, i64 1
  store i64* %239, i64** %206, align 8, !tbaa !22
  br label %292

; <label>:240:                                    ; preds = %229
  %241 = load i64, i64* %209, align 8, !tbaa !23
  %242 = sub i64 %236, %241
  %243 = ashr exact i64 %242, 3
  %244 = icmp eq i64 %242, 0
  %245 = select i1 %244, i64 1, i64 %243
  %246 = add nsw i64 %245, %243
  %247 = icmp ult i64 %246, %243
  %248 = icmp ugt i64 %246, 2305843009213693951
  %249 = or i1 %247, %248
  %250 = select i1 %249, i64 2305843009213693951, i64 %246
  %251 = icmp eq i64 %250, 0
  %252 = inttoptr i64 %241 to i64*
  br i1 %251, label %263, label %253

; <label>:253:                                    ; preds = %240
  %254 = icmp ugt i64 %250, 2305843009213693951
  br i1 %254, label %255, label %257

; <label>:255:                                    ; preds = %253
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %256 unwind label %303

; <label>:256:                                    ; preds = %255
  unreachable

; <label>:257:                                    ; preds = %253
  %258 = shl i64 %250, 3
  %259 = invoke i8* @_Znwm(i64 %258)
          to label %260 unwind label %301

; <label>:260:                                    ; preds = %257
  %261 = bitcast i8* %259 to i64*
  %262 = load i64*, i64** %210, align 8, !tbaa !19
  br label %263

; <label>:263:                                    ; preds = %260, %240
  %264 = phi i64* [ %262, %260 ], [ %252, %240 ]
  %265 = phi i8* [ %259, %260 ], [ null, %240 ]
  %266 = phi i64* [ %261, %260 ], [ null, %240 ]
  %267 = getelementptr inbounds i64, i64* %266, i64 %243
  %268 = load i64, i64* %233, align 8, !tbaa !2
  store i64 %268, i64* %267, align 8, !tbaa !2
  %269 = ptrtoint i64* %264 to i64
  %270 = sub i64 %236, %269
  %271 = ashr exact i64 %270, 3
  %272 = icmp eq i64 %270, 0
  br i1 %272, label %275, label %273

; <label>:273:                                    ; preds = %263
  %274 = bitcast i64* %264 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %265, i8* %274, i64 %270, i32 8, i1 false) #2
  br label %275

; <label>:275:                                    ; preds = %273, %263
  %276 = getelementptr inbounds i64, i64* %266, i64 %271
  %277 = getelementptr inbounds i64, i64* %276, i64 1
  %278 = load i64, i64* %208, align 8, !tbaa !22
  %279 = sub i64 %278, %236
  %280 = ashr exact i64 %279, 3
  %281 = icmp eq i64 %279, 0
  br i1 %281, label %285, label %282

; <label>:282:                                    ; preds = %275
  %283 = bitcast i64* %277 to i8*
  %284 = bitcast i64* %230 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %283, i8* %284, i64 %279, i32 8, i1 false) #2
  br label %285

; <label>:285:                                    ; preds = %282, %275
  %286 = getelementptr inbounds i64, i64* %277, i64 %280
  %287 = icmp eq i64* %264, null
  br i1 %287, label %290, label %288

; <label>:288:                                    ; preds = %285
  %289 = bitcast i64* %264 to i8*
  call void @_ZdlPv(i8* %289) #2
  br label %290

; <label>:290:                                    ; preds = %288, %285
  store i8* %265, i8** %212, align 8, !tbaa !19
  store i64* %286, i64** %206, align 8, !tbaa !22
  %291 = getelementptr inbounds i64, i64* %266, i64 %250
  store i64* %291, i64** %207, align 8, !tbaa !28
  br label %292

; <label>:292:                                    ; preds = %290, %237
  %293 = phi i64* [ %291, %290 ], [ %234, %237 ]
  %294 = phi i64* [ %286, %290 ], [ %239, %237 ]
  br i1 %211, label %296, label %295

; <label>:295:                                    ; preds = %292
  br label %309

; <label>:296:                                    ; preds = %373, %292
  %297 = phi i64* [ %294, %292 ], [ %375, %373 ]
  %298 = add nuw i64 %231, 1
  %299 = add i64 %232, %200
  %300 = icmp ult i64 %298, %202
  br i1 %300, label %229, label %214

; <label>:301:                                    ; preds = %257
  %302 = landingpad { i8*, i32 }
          cleanup
  br label %305

; <label>:303:                                    ; preds = %255
  %304 = landingpad { i8*, i32 }
          cleanup
  br label %305

; <label>:305:                                    ; preds = %303, %301
  %306 = phi { i8*, i32 } [ %302, %301 ], [ %304, %303 ]
  %307 = extractvalue { i8*, i32 } %306, 0
  %308 = extractvalue { i8*, i32 } %306, 1
  br label %482

; <label>:309:                                    ; preds = %295, %373
  %310 = phi i64* [ %374, %373 ], [ %293, %295 ]
  %311 = phi i64* [ %375, %373 ], [ %294, %295 ]
  %312 = phi i64 [ %376, %373 ], [ 0, %295 ]
  %313 = add i64 %312, %232
  %314 = load i64*, i64** %168, align 8, !tbaa !19
  %315 = getelementptr inbounds i64, i64* %314, i64 %313
  %316 = icmp eq i64* %311, %310
  %317 = ptrtoint i64* %311 to i64
  br i1 %316, label %321, label %318

; <label>:318:                                    ; preds = %309
  %319 = load i64, i64* %315, align 8, !tbaa !2
  store i64 %319, i64* %311, align 8, !tbaa !2
  %320 = getelementptr inbounds i64, i64* %311, i64 1
  store i64* %320, i64** %206, align 8, !tbaa !22
  br label %373

; <label>:321:                                    ; preds = %309
  %322 = load i64, i64* %209, align 8, !tbaa !23
  %323 = sub i64 %317, %322
  %324 = ashr exact i64 %323, 3
  %325 = icmp eq i64 %323, 0
  %326 = select i1 %325, i64 1, i64 %324
  %327 = add nsw i64 %326, %324
  %328 = icmp ult i64 %327, %324
  %329 = icmp ugt i64 %327, 2305843009213693951
  %330 = or i1 %328, %329
  %331 = select i1 %330, i64 2305843009213693951, i64 %327
  %332 = icmp eq i64 %331, 0
  %333 = inttoptr i64 %322 to i64*
  br i1 %332, label %344, label %334

; <label>:334:                                    ; preds = %321
  %335 = icmp ugt i64 %331, 2305843009213693951
  br i1 %335, label %336, label %338

; <label>:336:                                    ; preds = %334
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %337 unwind label %380

; <label>:337:                                    ; preds = %336
  unreachable

; <label>:338:                                    ; preds = %334
  %339 = shl i64 %331, 3
  %340 = invoke i8* @_Znwm(i64 %339)
          to label %341 unwind label %378

; <label>:341:                                    ; preds = %338
  %342 = bitcast i8* %340 to i64*
  %343 = load i64*, i64** %210, align 8, !tbaa !19
  br label %344

; <label>:344:                                    ; preds = %341, %321
  %345 = phi i64* [ %343, %341 ], [ %333, %321 ]
  %346 = phi i8* [ %340, %341 ], [ null, %321 ]
  %347 = phi i64* [ %342, %341 ], [ null, %321 ]
  %348 = getelementptr inbounds i64, i64* %347, i64 %324
  %349 = load i64, i64* %315, align 8, !tbaa !2
  store i64 %349, i64* %348, align 8, !tbaa !2
  %350 = ptrtoint i64* %345 to i64
  %351 = sub i64 %317, %350
  %352 = ashr exact i64 %351, 3
  %353 = icmp eq i64 %351, 0
  br i1 %353, label %356, label %354

; <label>:354:                                    ; preds = %344
  %355 = bitcast i64* %345 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %346, i8* %355, i64 %351, i32 8, i1 false) #2
  br label %356

; <label>:356:                                    ; preds = %354, %344
  %357 = getelementptr inbounds i64, i64* %347, i64 %352
  %358 = getelementptr inbounds i64, i64* %357, i64 1
  %359 = load i64, i64* %208, align 8, !tbaa !22
  %360 = sub i64 %359, %317
  %361 = ashr exact i64 %360, 3
  %362 = icmp eq i64 %360, 0
  br i1 %362, label %366, label %363

; <label>:363:                                    ; preds = %356
  %364 = bitcast i64* %358 to i8*
  %365 = bitcast i64* %310 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %364, i8* %365, i64 %360, i32 8, i1 false) #2
  br label %366

; <label>:366:                                    ; preds = %363, %356
  %367 = getelementptr inbounds i64, i64* %358, i64 %361
  %368 = icmp eq i64* %345, null
  br i1 %368, label %371, label %369

; <label>:369:                                    ; preds = %366
  %370 = bitcast i64* %345 to i8*
  call void @_ZdlPv(i8* %370) #2
  br label %371

; <label>:371:                                    ; preds = %369, %366
  store i8* %346, i8** %212, align 8, !tbaa !19
  store i64* %367, i64** %206, align 8, !tbaa !22
  %372 = getelementptr inbounds i64, i64* %347, i64 %331
  store i64* %372, i64** %207, align 8, !tbaa !28
  br label %373

; <label>:373:                                    ; preds = %371, %318
  %374 = phi i64* [ %372, %371 ], [ %310, %318 ]
  %375 = phi i64* [ %367, %371 ], [ %320, %318 ]
  %376 = add nuw i64 %312, 1
  %377 = icmp ult i64 %376, %200
  br i1 %377, label %309, label %296

; <label>:378:                                    ; preds = %338
  %379 = landingpad { i8*, i32 }
          cleanup
  br label %382

; <label>:380:                                    ; preds = %336
  %381 = landingpad { i8*, i32 }
          cleanup
  br label %382

; <label>:382:                                    ; preds = %380, %378
  %383 = phi { i8*, i32 } [ %379, %378 ], [ %381, %380 ]
  %384 = extractvalue { i8*, i32 } %383, 0
  %385 = extractvalue { i8*, i32 } %383, 1
  br label %482

; <label>:386:                                    ; preds = %221, %453
  %387 = phi i64 [ %217, %221 ], [ %454, %453 ]
  %388 = phi i64 [ %216, %221 ], [ %455, %453 ]
  %389 = phi i64* [ %228, %221 ], [ %456, %453 ]
  %390 = phi i64 [ %215, %221 ], [ %457, %453 ]
  %391 = inttoptr i64 %387 to i64*
  %392 = getelementptr inbounds i64, i64* %391, i64 %390
  %393 = load i64*, i64** %223, align 8, !tbaa !28
  %394 = icmp eq i64* %389, %393
  %395 = ptrtoint i64* %389 to i64
  br i1 %394, label %399, label %396

; <label>:396:                                    ; preds = %386
  %397 = load i64, i64* %392, align 8, !tbaa !2
  store i64 %397, i64* %389, align 8, !tbaa !2
  %398 = getelementptr inbounds i64, i64* %389, i64 1
  store i64* %398, i64** %222, align 8, !tbaa !22
  br label %453

; <label>:399:                                    ; preds = %386
  %400 = load i64, i64* %225, align 8, !tbaa !23
  %401 = sub i64 %395, %400
  %402 = ashr exact i64 %401, 3
  %403 = icmp eq i64 %401, 0
  %404 = select i1 %403, i64 1, i64 %402
  %405 = add nsw i64 %404, %402
  %406 = icmp ult i64 %405, %402
  %407 = icmp ugt i64 %405, 2305843009213693951
  %408 = or i1 %406, %407
  %409 = select i1 %408, i64 2305843009213693951, i64 %405
  %410 = icmp eq i64 %409, 0
  %411 = inttoptr i64 %400 to i64*
  br i1 %410, label %422, label %412

; <label>:412:                                    ; preds = %399
  %413 = icmp ugt i64 %409, 2305843009213693951
  br i1 %413, label %414, label %416

; <label>:414:                                    ; preds = %412
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %415 unwind label %463

; <label>:415:                                    ; preds = %414
  unreachable

; <label>:416:                                    ; preds = %412
  %417 = shl i64 %409, 3
  %418 = invoke i8* @_Znwm(i64 %417)
          to label %419 unwind label %461

; <label>:419:                                    ; preds = %416
  %420 = bitcast i8* %418 to i64*
  %421 = load i64*, i64** %226, align 8, !tbaa !19
  br label %422

; <label>:422:                                    ; preds = %419, %399
  %423 = phi i64* [ %421, %419 ], [ %411, %399 ]
  %424 = phi i8* [ %418, %419 ], [ null, %399 ]
  %425 = phi i64* [ %420, %419 ], [ null, %399 ]
  %426 = getelementptr inbounds i64, i64* %425, i64 %402
  %427 = load i64, i64* %392, align 8, !tbaa !2
  store i64 %427, i64* %426, align 8, !tbaa !2
  %428 = ptrtoint i64* %423 to i64
  %429 = sub i64 %395, %428
  %430 = ashr exact i64 %429, 3
  %431 = icmp eq i64 %429, 0
  br i1 %431, label %434, label %432

; <label>:432:                                    ; preds = %422
  %433 = bitcast i64* %423 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %424, i8* %433, i64 %429, i32 8, i1 false) #2
  br label %434

; <label>:434:                                    ; preds = %432, %422
  %435 = getelementptr inbounds i64, i64* %425, i64 %430
  %436 = getelementptr inbounds i64, i64* %435, i64 1
  %437 = load i64, i64* %224, align 8, !tbaa !22
  %438 = sub i64 %437, %395
  %439 = ashr exact i64 %438, 3
  %440 = icmp eq i64 %438, 0
  br i1 %440, label %444, label %441

; <label>:441:                                    ; preds = %434
  %442 = bitcast i64* %436 to i8*
  %443 = bitcast i64* %389 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %442, i8* %443, i64 %438, i32 8, i1 false) #2
  br label %444

; <label>:444:                                    ; preds = %441, %434
  %445 = getelementptr inbounds i64, i64* %436, i64 %439
  %446 = icmp eq i64* %423, null
  br i1 %446, label %449, label %447

; <label>:447:                                    ; preds = %444
  %448 = bitcast i64* %423 to i8*
  call void @_ZdlPv(i8* %448) #2
  br label %449

; <label>:449:                                    ; preds = %447, %444
  store i8* %424, i8** %227, align 8, !tbaa !19
  store i64* %445, i64** %222, align 8, !tbaa !22
  %450 = getelementptr inbounds i64, i64* %425, i64 %409
  store i64* %450, i64** %223, align 8, !tbaa !28
  %451 = load i64, i64* %33, align 8, !tbaa !22
  %452 = load i64, i64* %13, align 8, !tbaa !19
  br label %453

; <label>:453:                                    ; preds = %449, %396
  %454 = phi i64 [ %452, %449 ], [ %387, %396 ]
  %455 = phi i64 [ %451, %449 ], [ %388, %396 ]
  %456 = phi i64* [ %445, %449 ], [ %398, %396 ]
  %457 = add nuw i64 %390, 1
  %458 = sub i64 %455, %454
  %459 = ashr exact i64 %458, 3
  %460 = icmp ult i64 %457, %459
  br i1 %460, label %386, label %469

; <label>:461:                                    ; preds = %416
  %462 = landingpad { i8*, i32 }
          cleanup
  br label %465

; <label>:463:                                    ; preds = %469, %414
  %464 = landingpad { i8*, i32 }
          cleanup
  br label %465

; <label>:465:                                    ; preds = %463, %461
  %466 = phi { i8*, i32 } [ %462, %461 ], [ %464, %463 ]
  %467 = extractvalue { i8*, i32 } %466, 0
  %468 = extractvalue { i8*, i32 } %466, 1
  br label %482

; <label>:469:                                    ; preds = %453, %214
  %470 = invoke dereferenceable(24) %"class.std::vector"* @_ZNSt6vectorImSaImEEaSERKS1_(%"class.std::vector"* nonnull %0, %"class.std::vector"* nonnull dereferenceable(24) %4)
          to label %471 unwind label %463

; <label>:471:                                    ; preds = %469
  %472 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %473 = load i64*, i64** %472, align 8, !tbaa !19
  %474 = icmp eq i64* %473, null
  br i1 %474, label %477, label %475

; <label>:475:                                    ; preds = %471
  %476 = bitcast i64* %473 to i8*
  call void @_ZdlPv(i8* %476) #2
  br label %477

; <label>:477:                                    ; preds = %471, %475
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %478 = icmp eq i64 %75, 0
  br i1 %478, label %481, label %479

; <label>:479:                                    ; preds = %477
  %480 = inttoptr i64 %75 to i8*
  call void @_ZdlPv(i8* %480) #2
  br label %481

; <label>:481:                                    ; preds = %477, %479
  ret void

; <label>:482:                                    ; preds = %465, %382, %305, %159, %67, %54
  %483 = phi i64 [ %55, %54 ], [ %95, %159 ], [ %75, %382 ], [ %75, %305 ], [ %75, %465 ], [ 0, %67 ]
  %484 = phi i32 [ %58, %54 ], [ %162, %159 ], [ %385, %382 ], [ %308, %305 ], [ %468, %465 ], [ %62, %67 ]
  %485 = phi i8* [ %57, %54 ], [ %161, %159 ], [ %384, %382 ], [ %307, %305 ], [ %467, %465 ], [ %61, %67 ]
  %486 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %487 = load i64*, i64** %486, align 8, !tbaa !19
  %488 = icmp eq i64* %487, null
  br i1 %488, label %491, label %489

; <label>:489:                                    ; preds = %482
  %490 = bitcast i64* %487 to i8*
  call void @_ZdlPv(i8* %490) #2
  br label %491

; <label>:491:                                    ; preds = %482, %489
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %492 = icmp eq i64 %483, 0
  br i1 %492, label %495, label %493

; <label>:493:                                    ; preds = %491
  %494 = inttoptr i64 %483 to i8*
  call void @_ZdlPv(i8* %494) #2
  br label %495

; <label>:495:                                    ; preds = %491, %493
  %496 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %497 = load i64*, i64** %496, align 8, !tbaa !19
  %498 = icmp eq i64* %497, null
  br i1 %498, label %501, label %499

; <label>:499:                                    ; preds = %495
  %500 = bitcast i64* %497 to i8*
  call void @_ZdlPv(i8* %500) #2
  br label %501

; <label>:501:                                    ; preds = %495, %499
  %502 = insertvalue { i8*, i32 } undef, i8* %485, 0
  %503 = insertvalue { i8*, i32 } %502, i32 %484, 1
  resume { i8*, i32 } %503
}

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"*, double) local_unnamed_addr #0

; Function Attrs: inlinehint uwtable
define linkonce_odr void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64*, i64*, i32, i1 zeroext) local_unnamed_addr #14 comdat {
  %5 = ptrtoint i64* %0 to i64
  %6 = alloca %"struct.__gnu_cxx::__ops::_Iter_comp_iter", align 1
  %7 = ptrtoint i64* %1 to i64
  %8 = sub i64 %7, %5
  %9 = icmp slt i64 %8, 192
  br i1 %9, label %22, label %10

; <label>:10:                                     ; preds = %4
  %11 = getelementptr inbounds i64, i64* %1, i64 -1
  %12 = getelementptr inbounds i64, i64* %1, i64 -2
  %13 = getelementptr inbounds i64, i64* %1, i64 -3
  br label %14

; <label>:14:                                     ; preds = %10, %579
  %15 = phi i64 [ %8, %10 ], [ %352, %579 ]
  %16 = phi i32 [ %2, %10 ], [ %580, %579 ]
  %17 = phi i1 [ %3, %10 ], [ false, %579 ]
  %18 = phi i64 [ %5, %10 ], [ %351, %579 ]
  br label %136

; <label>:19:                                     ; preds = %579, %572, %460
  %20 = phi i64* [ %350, %460 ], [ %575, %572 ], [ %350, %579 ]
  %21 = icmp eq i64* %20, %1
  br i1 %21, label %582, label %83

; <label>:22:                                     ; preds = %4
  %23 = icmp eq i64* %0, %1
  br i1 %3, label %24, label %82

; <label>:24:                                     ; preds = %22
  br i1 %23, label %582, label %25

; <label>:25:                                     ; preds = %24
  %26 = getelementptr inbounds i64, i64* %0, i64 1
  %27 = icmp eq i64* %26, %1
  br i1 %27, label %582, label %28

; <label>:28:                                     ; preds = %25
  %29 = getelementptr i64, i64* %1, i64 -2
  %30 = ptrtoint i64* %29 to i64
  %31 = sub i64 %30, %5
  %32 = and i64 %31, 8
  %33 = icmp eq i64 %32, 0
  br i1 %33, label %34, label %53

; <label>:34:                                     ; preds = %28
  %35 = load i64, i64* %26, align 8, !tbaa !2
  %36 = load i64, i64* %0, align 8, !tbaa !2
  %37 = icmp ult i64 %35, %36
  br i1 %37, label %38, label %51

; <label>:38:                                     ; preds = %34
  br label %39

; <label>:39:                                     ; preds = %45, %38
  %40 = phi i64 [ %47, %45 ], [ %36, %38 ]
  %41 = phi i64* [ %46, %45 ], [ %0, %38 ]
  %42 = phi i64* [ %43, %45 ], [ %26, %38 ]
  %43 = getelementptr inbounds i64, i64* %42, i64 -1
  store i64 %40, i64* %42, align 8, !tbaa !2
  %44 = icmp eq i64* %43, %0
  br i1 %44, label %49, label %45

; <label>:45:                                     ; preds = %39
  %46 = getelementptr inbounds i64, i64* %41, i64 -1
  %47 = load i64, i64* %46, align 8, !tbaa !2
  %48 = icmp ult i64 %35, %47
  br i1 %48, label %39, label %49

; <label>:49:                                     ; preds = %45, %39
  %50 = phi i64* [ %0, %39 ], [ %43, %45 ]
  store i64 %35, i64* %50, align 8, !tbaa !2
  br label %51

; <label>:51:                                     ; preds = %49, %34
  %52 = getelementptr inbounds i64, i64* %0, i64 2
  br label %53

; <label>:53:                                     ; preds = %51, %28
  %54 = phi i64* [ %26, %28 ], [ %52, %51 ]
  %55 = phi i64* [ %0, %28 ], [ %26, %51 ]
  %56 = icmp ult i64 %31, 8
  br i1 %56, label %582, label %57

; <label>:57:                                     ; preds = %53
  br label %58

; <label>:58:                                     ; preds = %596, %57
  %59 = phi i64* [ %54, %57 ], [ %597, %596 ]
  %60 = phi i64* [ %55, %57 ], [ %78, %596 ]
  %61 = load i64, i64* %59, align 8, !tbaa !2
  %62 = load i64, i64* %60, align 8, !tbaa !2
  %63 = icmp ult i64 %61, %62
  br i1 %63, label %64, label %77

; <label>:64:                                     ; preds = %58
  br label %65

; <label>:65:                                     ; preds = %64, %71
  %66 = phi i64 [ %73, %71 ], [ %62, %64 ]
  %67 = phi i64* [ %72, %71 ], [ %60, %64 ]
  %68 = phi i64* [ %69, %71 ], [ %59, %64 ]
  %69 = getelementptr inbounds i64, i64* %68, i64 -1
  store i64 %66, i64* %68, align 8, !tbaa !2
  %70 = icmp eq i64* %69, %0
  br i1 %70, label %75, label %71

; <label>:71:                                     ; preds = %65
  %72 = getelementptr inbounds i64, i64* %67, i64 -1
  %73 = load i64, i64* %72, align 8, !tbaa !2
  %74 = icmp ult i64 %61, %73
  br i1 %74, label %65, label %75

; <label>:75:                                     ; preds = %71, %65
  %76 = phi i64* [ %0, %65 ], [ %69, %71 ]
  store i64 %61, i64* %76, align 8, !tbaa !2
  br label %77

; <label>:77:                                     ; preds = %75, %58
  %78 = getelementptr inbounds i64, i64* %59, i64 1
  %79 = load i64, i64* %78, align 8, !tbaa !2
  %80 = load i64, i64* %59, align 8, !tbaa !2
  %81 = icmp ult i64 %79, %80
  br i1 %81, label %583, label %596

; <label>:82:                                     ; preds = %22
  br i1 %23, label %582, label %83

; <label>:83:                                     ; preds = %19, %82
  %84 = phi i64* [ %20, %19 ], [ %0, %82 ]
  %85 = getelementptr inbounds i64, i64* %84, i64 1
  %86 = icmp eq i64* %85, %1
  br i1 %86, label %582, label %87

; <label>:87:                                     ; preds = %83
  %88 = ptrtoint i64* %84 to i64
  %89 = getelementptr i64, i64* %1, i64 -2
  %90 = ptrtoint i64* %89 to i64
  %91 = sub i64 %90, %88
  %92 = and i64 %91, 8
  %93 = icmp eq i64 %92, 0
  br i1 %93, label %94, label %110

; <label>:94:                                     ; preds = %87
  %95 = load i64, i64* %85, align 8, !tbaa !2
  %96 = load i64, i64* %84, align 8, !tbaa !2
  %97 = icmp ult i64 %95, %96
  br i1 %97, label %98, label %108

; <label>:98:                                     ; preds = %94
  br label %99

; <label>:99:                                     ; preds = %99, %98
  %100 = phi i64 [ %105, %99 ], [ %96, %98 ]
  %101 = phi i64* [ %104, %99 ], [ %84, %98 ]
  %102 = phi i64* [ %103, %99 ], [ %85, %98 ]
  %103 = getelementptr inbounds i64, i64* %102, i64 -1
  store i64 %100, i64* %102, align 8, !tbaa !2
  %104 = getelementptr inbounds i64, i64* %101, i64 -1
  %105 = load i64, i64* %104, align 8, !tbaa !2
  %106 = icmp ult i64 %95, %105
  br i1 %106, label %99, label %107

; <label>:107:                                    ; preds = %99
  store i64 %95, i64* %103, align 8, !tbaa !2
  br label %108

; <label>:108:                                    ; preds = %107, %94
  %109 = getelementptr inbounds i64, i64* %84, i64 2
  br label %110

; <label>:110:                                    ; preds = %108, %87
  %111 = phi i64* [ %85, %87 ], [ %109, %108 ]
  %112 = phi i64* [ %84, %87 ], [ %85, %108 ]
  %113 = icmp ult i64 %91, 8
  br i1 %113, label %582, label %114

; <label>:114:                                    ; preds = %110
  br label %115

; <label>:115:                                    ; preds = %609, %114
  %116 = phi i64* [ %111, %114 ], [ %610, %609 ]
  %117 = phi i64* [ %112, %114 ], [ %132, %609 ]
  %118 = load i64, i64* %116, align 8, !tbaa !2
  %119 = load i64, i64* %117, align 8, !tbaa !2
  %120 = icmp ult i64 %118, %119
  br i1 %120, label %121, label %131

; <label>:121:                                    ; preds = %115
  br label %122

; <label>:122:                                    ; preds = %121, %122
  %123 = phi i64 [ %128, %122 ], [ %119, %121 ]
  %124 = phi i64* [ %127, %122 ], [ %117, %121 ]
  %125 = phi i64* [ %126, %122 ], [ %116, %121 ]
  %126 = getelementptr inbounds i64, i64* %125, i64 -1
  store i64 %123, i64* %125, align 8, !tbaa !2
  %127 = getelementptr inbounds i64, i64* %124, i64 -1
  %128 = load i64, i64* %127, align 8, !tbaa !2
  %129 = icmp ult i64 %118, %128
  br i1 %129, label %122, label %130

; <label>:130:                                    ; preds = %122
  store i64 %118, i64* %126, align 8, !tbaa !2
  br label %131

; <label>:131:                                    ; preds = %130, %115
  %132 = getelementptr inbounds i64, i64* %116, i64 1
  %133 = load i64, i64* %132, align 8, !tbaa !2
  %134 = load i64, i64* %116, align 8, !tbaa !2
  %135 = icmp ult i64 %133, %134
  br i1 %135, label %599, label %609

; <label>:136:                                    ; preds = %14, %572
  %137 = phi i64 [ %15, %14 ], [ %577, %572 ]
  %138 = phi i64 [ %18, %14 ], [ %576, %572 ]
  %139 = lshr i64 %137, 4
  %140 = icmp sgt i64 %137, 1024
  %141 = inttoptr i64 %138 to i64*
  %142 = getelementptr inbounds i64, i64* %141, i64 %139
  br i1 %140, label %143, label %215

; <label>:143:                                    ; preds = %136
  %144 = load i64, i64* %142, align 8, !tbaa !2
  %145 = load i64, i64* %141, align 8, !tbaa !2
  %146 = icmp ult i64 %144, %145
  br i1 %146, label %147, label %148

; <label>:147:                                    ; preds = %143
  store i64 %144, i64* %141, align 8, !tbaa !2
  store i64 %145, i64* %142, align 8, !tbaa !2
  br label %148

; <label>:148:                                    ; preds = %147, %143
  %149 = phi i64 [ %144, %143 ], [ %145, %147 ]
  %150 = load i64, i64* %11, align 8, !tbaa !2
  %151 = icmp ult i64 %150, %149
  br i1 %151, label %152, label %154

; <label>:152:                                    ; preds = %148
  store i64 %150, i64* %142, align 8, !tbaa !2
  store i64 %149, i64* %11, align 8, !tbaa !2
  %153 = load i64, i64* %142, align 8, !tbaa !2
  br label %154

; <label>:154:                                    ; preds = %152, %148
  %155 = phi i64 [ %149, %148 ], [ %153, %152 ]
  %156 = load i64, i64* %141, align 8, !tbaa !2
  %157 = icmp ult i64 %155, %156
  br i1 %157, label %158, label %159

; <label>:158:                                    ; preds = %154
  store i64 %155, i64* %141, align 8, !tbaa !2
  store i64 %156, i64* %142, align 8, !tbaa !2
  br label %159

; <label>:159:                                    ; preds = %154, %158
  %160 = getelementptr inbounds i64, i64* %141, i64 1
  %161 = add nsw i64 %139, -1
  %162 = getelementptr inbounds i64, i64* %141, i64 %161
  %163 = load i64, i64* %162, align 8, !tbaa !2
  %164 = load i64, i64* %160, align 8, !tbaa !2
  %165 = icmp ult i64 %163, %164
  br i1 %165, label %166, label %167

; <label>:166:                                    ; preds = %159
  store i64 %163, i64* %160, align 8, !tbaa !2
  store i64 %164, i64* %162, align 8, !tbaa !2
  br label %167

; <label>:167:                                    ; preds = %166, %159
  %168 = phi i64 [ %163, %159 ], [ %164, %166 ]
  %169 = load i64, i64* %12, align 8, !tbaa !2
  %170 = icmp ult i64 %169, %168
  br i1 %170, label %171, label %173

; <label>:171:                                    ; preds = %167
  store i64 %169, i64* %162, align 8, !tbaa !2
  store i64 %168, i64* %12, align 8, !tbaa !2
  %172 = load i64, i64* %162, align 8, !tbaa !2
  br label %173

; <label>:173:                                    ; preds = %171, %167
  %174 = phi i64 [ %168, %167 ], [ %172, %171 ]
  %175 = load i64, i64* %160, align 8, !tbaa !2
  %176 = icmp ult i64 %174, %175
  br i1 %176, label %177, label %178

; <label>:177:                                    ; preds = %173
  store i64 %174, i64* %160, align 8, !tbaa !2
  store i64 %175, i64* %162, align 8, !tbaa !2
  br label %178

; <label>:178:                                    ; preds = %173, %177
  %179 = getelementptr inbounds i64, i64* %141, i64 2
  %180 = add nuw nsw i64 %139, 1
  %181 = getelementptr inbounds i64, i64* %141, i64 %180
  %182 = load i64, i64* %181, align 8, !tbaa !2
  %183 = load i64, i64* %179, align 8, !tbaa !2
  %184 = icmp ult i64 %182, %183
  br i1 %184, label %185, label %186

; <label>:185:                                    ; preds = %178
  store i64 %182, i64* %179, align 8, !tbaa !2
  store i64 %183, i64* %181, align 8, !tbaa !2
  br label %186

; <label>:186:                                    ; preds = %185, %178
  %187 = phi i64 [ %182, %178 ], [ %183, %185 ]
  %188 = load i64, i64* %13, align 8, !tbaa !2
  %189 = icmp ult i64 %188, %187
  br i1 %189, label %190, label %192

; <label>:190:                                    ; preds = %186
  store i64 %188, i64* %181, align 8, !tbaa !2
  store i64 %187, i64* %13, align 8, !tbaa !2
  %191 = load i64, i64* %181, align 8, !tbaa !2
  br label %192

; <label>:192:                                    ; preds = %190, %186
  %193 = phi i64 [ %187, %186 ], [ %191, %190 ]
  %194 = load i64, i64* %179, align 8, !tbaa !2
  %195 = icmp ult i64 %193, %194
  br i1 %195, label %196, label %197

; <label>:196:                                    ; preds = %192
  store i64 %193, i64* %179, align 8, !tbaa !2
  store i64 %194, i64* %181, align 8, !tbaa !2
  br label %197

; <label>:197:                                    ; preds = %192, %196
  %198 = phi i64 [ %193, %192 ], [ %194, %196 ]
  %199 = load i64, i64* %142, align 8, !tbaa !2
  %200 = load i64, i64* %162, align 8, !tbaa !2
  %201 = icmp ult i64 %199, %200
  br i1 %201, label %202, label %203

; <label>:202:                                    ; preds = %197
  store i64 %199, i64* %162, align 8, !tbaa !2
  store i64 %200, i64* %142, align 8, !tbaa !2
  br label %203

; <label>:203:                                    ; preds = %202, %197
  %204 = phi i64 [ %200, %197 ], [ %199, %202 ]
  %205 = phi i64 [ %199, %197 ], [ %200, %202 ]
  %206 = icmp ult i64 %198, %205
  br i1 %206, label %207, label %208

; <label>:207:                                    ; preds = %203
  store i64 %198, i64* %142, align 8, !tbaa !2
  store i64 %205, i64* %181, align 8, !tbaa !2
  br label %208

; <label>:208:                                    ; preds = %207, %203
  %209 = phi i64 [ %205, %203 ], [ %198, %207 ]
  %210 = icmp ult i64 %209, %204
  br i1 %210, label %211, label %212

; <label>:211:                                    ; preds = %208
  store i64 %209, i64* %162, align 8, !tbaa !2
  store i64 %204, i64* %142, align 8, !tbaa !2
  br label %212

; <label>:212:                                    ; preds = %208, %211
  %213 = phi i64 [ %209, %208 ], [ %204, %211 ]
  %214 = load i64, i64* %141, align 8, !tbaa !2
  store i64 %213, i64* %141, align 8, !tbaa !2
  store i64 %214, i64* %142, align 8, !tbaa !2
  br label %231

; <label>:215:                                    ; preds = %136
  %216 = load i64, i64* %141, align 8, !tbaa !2
  %217 = load i64, i64* %142, align 8, !tbaa !2
  %218 = icmp ult i64 %216, %217
  br i1 %218, label %219, label %220

; <label>:219:                                    ; preds = %215
  store i64 %216, i64* %142, align 8, !tbaa !2
  store i64 %217, i64* %141, align 8, !tbaa !2
  br label %220

; <label>:220:                                    ; preds = %219, %215
  %221 = phi i64 [ %216, %215 ], [ %217, %219 ]
  %222 = load i64, i64* %11, align 8, !tbaa !2
  %223 = icmp ult i64 %222, %221
  br i1 %223, label %224, label %226

; <label>:224:                                    ; preds = %220
  store i64 %222, i64* %141, align 8, !tbaa !2
  store i64 %221, i64* %11, align 8, !tbaa !2
  %225 = load i64, i64* %141, align 8, !tbaa !2
  br label %226

; <label>:226:                                    ; preds = %224, %220
  %227 = phi i64 [ %221, %220 ], [ %225, %224 ]
  %228 = load i64, i64* %142, align 8, !tbaa !2
  %229 = icmp ult i64 %227, %228
  br i1 %229, label %230, label %231

; <label>:230:                                    ; preds = %226
  store i64 %227, i64* %142, align 8, !tbaa !2
  store i64 %228, i64* %141, align 8, !tbaa !2
  br label %231

; <label>:231:                                    ; preds = %230, %226, %212
  br i1 %17, label %232, label %235

; <label>:232:                                    ; preds = %231
  %233 = inttoptr i64 %138 to i64*
  %234 = load i64, i64* %233, align 8, !tbaa !2
  br label %289

; <label>:235:                                    ; preds = %231
  %236 = getelementptr inbounds i64, i64* %141, i64 -1
  %237 = load i64, i64* %236, align 8, !tbaa !2
  %238 = load i64, i64* %141, align 8, !tbaa !2
  %239 = icmp ult i64 %237, %238
  br i1 %239, label %287, label %240

; <label>:240:                                    ; preds = %235
  br label %241

; <label>:241:                                    ; preds = %240, %241
  %242 = phi i64* [ %243, %241 ], [ %1, %240 ]
  %243 = getelementptr inbounds i64, i64* %242, i64 -1
  %244 = load i64, i64* %243, align 8, !tbaa !2
  %245 = icmp ult i64 %238, %244
  br i1 %245, label %241, label %246

; <label>:246:                                    ; preds = %241
  %247 = icmp eq i64* %242, %1
  br i1 %247, label %249, label %248

; <label>:248:                                    ; preds = %246
  br label %259

; <label>:249:                                    ; preds = %246
  %250 = icmp ugt i64* %243, %141
  br i1 %250, label %251, label %264

; <label>:251:                                    ; preds = %249
  br label %252

; <label>:252:                                    ; preds = %251, %252
  %253 = phi i64* [ %254, %252 ], [ %141, %251 ]
  %254 = getelementptr inbounds i64, i64* %253, i64 1
  %255 = load i64, i64* %254, align 8, !tbaa !2
  %256 = icmp uge i64 %238, %255
  %257 = icmp ugt i64* %243, %254
  %258 = and i1 %256, %257
  br i1 %258, label %252, label %264

; <label>:259:                                    ; preds = %248, %259
  %260 = phi i64* [ %261, %259 ], [ %141, %248 ]
  %261 = getelementptr inbounds i64, i64* %260, i64 1
  %262 = load i64, i64* %261, align 8, !tbaa !2
  %263 = icmp ult i64 %238, %262
  br i1 %263, label %264, label %259

; <label>:264:                                    ; preds = %259, %252, %249
  %265 = phi i64 [ %238, %249 ], [ %255, %252 ], [ %262, %259 ]
  %266 = phi i64* [ %141, %249 ], [ %254, %252 ], [ %261, %259 ]
  %267 = icmp ugt i64* %243, %266
  br i1 %267, label %268, label %572

; <label>:268:                                    ; preds = %264
  br label %269

; <label>:269:                                    ; preds = %268, %285
  %270 = phi i64 [ %277, %285 ], [ %244, %268 ]
  %271 = phi i64 [ %283, %285 ], [ %265, %268 ]
  %272 = phi i64* [ %282, %285 ], [ %266, %268 ]
  %273 = phi i64* [ %276, %285 ], [ %243, %268 ]
  store i64 %270, i64* %272, align 8, !tbaa !2
  store i64 %271, i64* %273, align 8, !tbaa !2
  br label %274

; <label>:274:                                    ; preds = %274, %269
  %275 = phi i64* [ %273, %269 ], [ %276, %274 ]
  %276 = getelementptr inbounds i64, i64* %275, i64 -1
  %277 = load i64, i64* %276, align 8, !tbaa !2
  %278 = icmp ult i64 %238, %277
  br i1 %278, label %274, label %279

; <label>:279:                                    ; preds = %274
  br label %280

; <label>:280:                                    ; preds = %279, %280
  %281 = phi i64* [ %282, %280 ], [ %272, %279 ]
  %282 = getelementptr inbounds i64, i64* %281, i64 1
  %283 = load i64, i64* %282, align 8, !tbaa !2
  %284 = icmp ult i64 %238, %283
  br i1 %284, label %285, label %280

; <label>:285:                                    ; preds = %280
  %286 = icmp ugt i64* %276, %282
  br i1 %286, label %269, label %572

; <label>:287:                                    ; preds = %235
  %288 = inttoptr i64 %138 to i64*
  br label %289

; <label>:289:                                    ; preds = %287, %232
  %290 = phi i64* [ %233, %232 ], [ %288, %287 ]
  %291 = phi i64 [ %234, %232 ], [ %238, %287 ]
  br label %292

; <label>:292:                                    ; preds = %292, %289
  %293 = phi i64 [ 0, %289 ], [ %294, %292 ]
  %294 = add nuw nsw i64 %293, 1
  %295 = getelementptr inbounds i64, i64* %290, i64 %294
  %296 = load i64, i64* %295, align 8, !tbaa !2
  %297 = icmp ult i64 %296, %291
  br i1 %297, label %292, label %298

; <label>:298:                                    ; preds = %292
  %299 = getelementptr inbounds i64, i64* %290, i64 %294
  %300 = icmp eq i64 %293, 0
  br i1 %300, label %302, label %301

; <label>:301:                                    ; preds = %298
  br label %312

; <label>:302:                                    ; preds = %298
  %303 = icmp ult i64* %299, %1
  br i1 %303, label %304, label %317

; <label>:304:                                    ; preds = %302
  br label %305

; <label>:305:                                    ; preds = %304, %305
  %306 = phi i64* [ %307, %305 ], [ %1, %304 ]
  %307 = getelementptr inbounds i64, i64* %306, i64 -1
  %308 = load i64, i64* %307, align 8, !tbaa !2
  %309 = icmp uge i64 %308, %291
  %310 = icmp ult i64* %299, %307
  %311 = and i1 %309, %310
  br i1 %311, label %305, label %317

; <label>:312:                                    ; preds = %301, %312
  %313 = phi i64* [ %314, %312 ], [ %1, %301 ]
  %314 = getelementptr inbounds i64, i64* %313, i64 -1
  %315 = load i64, i64* %314, align 8, !tbaa !2
  %316 = icmp ult i64 %315, %291
  br i1 %316, label %317, label %312

; <label>:317:                                    ; preds = %312, %305, %302
  %318 = phi i64* [ %1, %302 ], [ %307, %305 ], [ %314, %312 ]
  %319 = icmp ult i64* %299, %318
  br i1 %319, label %320, label %343

; <label>:320:                                    ; preds = %317
  %321 = load i64, i64* %318, align 8, !tbaa !2
  br label %322

; <label>:322:                                    ; preds = %341, %320
  %323 = phi i64 [ %321, %320 ], [ %339, %341 ]
  %324 = phi i64 [ %296, %320 ], [ %332, %341 ]
  %325 = phi i64 [ %294, %320 ], [ %330, %341 ]
  %326 = phi i64* [ %318, %320 ], [ %338, %341 ]
  %327 = getelementptr inbounds i64, i64* %290, i64 %325
  store i64 %323, i64* %327, align 8, !tbaa !2
  store i64 %324, i64* %326, align 8, !tbaa !2
  br label %328

; <label>:328:                                    ; preds = %328, %322
  %329 = phi i64 [ %325, %322 ], [ %330, %328 ]
  %330 = add nsw i64 %329, 1
  %331 = getelementptr inbounds i64, i64* %290, i64 %330
  %332 = load i64, i64* %331, align 8, !tbaa !2
  %333 = icmp ult i64 %332, %291
  br i1 %333, label %328, label %334

; <label>:334:                                    ; preds = %328
  %335 = getelementptr inbounds i64, i64* %290, i64 %330
  br label %336

; <label>:336:                                    ; preds = %336, %334
  %337 = phi i64* [ %326, %334 ], [ %338, %336 ]
  %338 = getelementptr inbounds i64, i64* %337, i64 -1
  %339 = load i64, i64* %338, align 8, !tbaa !2
  %340 = icmp ult i64 %339, %291
  br i1 %340, label %341, label %336

; <label>:341:                                    ; preds = %336
  %342 = icmp ugt i64* %338, %335
  br i1 %342, label %322, label %343

; <label>:343:                                    ; preds = %341, %317
  %344 = phi i64 [ %293, %317 ], [ %329, %341 ]
  %345 = getelementptr inbounds i64, i64* %290, i64 %344
  %346 = load i64, i64* %345, align 8, !tbaa !2
  store i64 %346, i64* %290, align 8, !tbaa !2
  store i64 %291, i64* %345, align 8, !tbaa !2
  %347 = ptrtoint i64* %345 to i64
  %348 = sub i64 %347, %138
  %349 = ashr exact i64 %348, 3
  %350 = getelementptr inbounds i64, i64* %345, i64 1
  %351 = ptrtoint i64* %350 to i64
  %352 = sub i64 %7, %351
  %353 = ashr exact i64 %352, 3
  %354 = lshr i64 %137, 6
  %355 = icmp slt i64 %349, %354
  %356 = icmp slt i64 %353, %354
  %357 = or i1 %355, %356
  br i1 %357, label %358, label %491

; <label>:358:                                    ; preds = %343
  %359 = add nsw i32 %16, -1
  %360 = icmp eq i32 %359, 0
  br i1 %360, label %361, label %424

; <label>:361:                                    ; preds = %358
  %362 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_comp_iter", %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* %6, i64 0, i32 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %362) #2
  call void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_comp_iterISt4lessImEEEEvT_SC_RT0_(i64* nonnull %290, i64* %1, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* nonnull dereferenceable(1) %6)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %362) #2
  %363 = icmp sgt i64 %137, 8
  br i1 %363, label %364, label %582

; <label>:364:                                    ; preds = %361
  br label %365

; <label>:365:                                    ; preds = %364, %420
  %366 = phi i64* [ %367, %420 ], [ %1, %364 ]
  %367 = getelementptr inbounds i64, i64* %366, i64 -1
  %368 = ptrtoint i64* %367 to i64
  %369 = load i64, i64* %367, align 8, !tbaa !2
  %370 = load i64, i64* %290, align 8, !tbaa !2
  store i64 %370, i64* %367, align 8, !tbaa !2
  %371 = sub i64 %368, %138
  %372 = ashr exact i64 %371, 3
  %373 = add nsw i64 %372, -1
  %374 = sdiv i64 %373, 2
  %375 = icmp sgt i64 %371, 16
  br i1 %375, label %376, label %392

; <label>:376:                                    ; preds = %365
  br label %377

; <label>:377:                                    ; preds = %376, %377
  %378 = phi i64 [ %387, %377 ], [ 0, %376 ]
  %379 = shl i64 %378, 1
  %380 = add i64 %379, 2
  %381 = getelementptr inbounds i64, i64* %290, i64 %380
  %382 = or i64 %379, 1
  %383 = getelementptr inbounds i64, i64* %290, i64 %382
  %384 = load i64, i64* %381, align 8, !tbaa !2
  %385 = load i64, i64* %383, align 8, !tbaa !2
  %386 = icmp ult i64 %384, %385
  %387 = select i1 %386, i64 %382, i64 %380
  %388 = getelementptr inbounds i64, i64* %290, i64 %387
  %389 = load i64, i64* %388, align 8, !tbaa !2
  %390 = getelementptr inbounds i64, i64* %290, i64 %378
  store i64 %389, i64* %390, align 8, !tbaa !2
  %391 = icmp slt i64 %387, %374
  br i1 %391, label %377, label %392

; <label>:392:                                    ; preds = %377, %365
  %393 = phi i64 [ 0, %365 ], [ %387, %377 ]
  %394 = and i64 %371, 8
  %395 = icmp eq i64 %394, 0
  br i1 %395, label %396, label %406

; <label>:396:                                    ; preds = %392
  %397 = add nsw i64 %372, -2
  %398 = sdiv i64 %397, 2
  %399 = icmp eq i64 %393, %398
  br i1 %399, label %400, label %406

; <label>:400:                                    ; preds = %396
  %401 = shl i64 %393, 1
  %402 = or i64 %401, 1
  %403 = getelementptr inbounds i64, i64* %290, i64 %402
  %404 = load i64, i64* %403, align 8, !tbaa !2
  %405 = getelementptr inbounds i64, i64* %290, i64 %393
  store i64 %404, i64* %405, align 8, !tbaa !2
  br label %406

; <label>:406:                                    ; preds = %400, %396, %392
  %407 = phi i64 [ %402, %400 ], [ %393, %396 ], [ %393, %392 ]
  %408 = icmp sgt i64 %407, 0
  br i1 %408, label %409, label %420

; <label>:409:                                    ; preds = %406
  br label %410

; <label>:410:                                    ; preds = %409, %417
  %411 = phi i64 [ %413, %417 ], [ %407, %409 ]
  %412 = add nsw i64 %411, -1
  %413 = sdiv i64 %412, 2
  %414 = getelementptr inbounds i64, i64* %290, i64 %413
  %415 = load i64, i64* %414, align 8, !tbaa !2
  %416 = icmp ult i64 %415, %369
  br i1 %416, label %417, label %420

; <label>:417:                                    ; preds = %410
  %418 = getelementptr inbounds i64, i64* %290, i64 %411
  store i64 %415, i64* %418, align 8, !tbaa !2
  %419 = icmp sgt i64 %411, 2
  br i1 %419, label %410, label %420

; <label>:420:                                    ; preds = %417, %410, %406
  %421 = phi i64 [ %407, %406 ], [ %411, %410 ], [ %413, %417 ]
  %422 = getelementptr inbounds i64, i64* %290, i64 %421
  store i64 %369, i64* %422, align 8, !tbaa !2
  %423 = icmp sgt i64 %371, 8
  br i1 %423, label %365, label %582

; <label>:424:                                    ; preds = %358
  %425 = icmp sgt i64 %348, 184
  br i1 %425, label %426, label %458

; <label>:426:                                    ; preds = %424
  %427 = lshr i64 %349, 2
  %428 = getelementptr inbounds i64, i64* %290, i64 %427
  %429 = load i64, i64* %290, align 8, !tbaa !2
  %430 = load i64, i64* %428, align 8, !tbaa !2
  store i64 %430, i64* %290, align 8, !tbaa !2
  store i64 %429, i64* %428, align 8, !tbaa !2
  %431 = getelementptr inbounds i64, i64* %345, i64 -1
  %432 = sub nsw i64 0, %427
  %433 = getelementptr inbounds i64, i64* %345, i64 %432
  %434 = load i64, i64* %431, align 8, !tbaa !2
  %435 = load i64, i64* %433, align 8, !tbaa !2
  store i64 %435, i64* %431, align 8, !tbaa !2
  store i64 %434, i64* %433, align 8, !tbaa !2
  %436 = icmp sgt i64 %348, 1024
  br i1 %436, label %437, label %458

; <label>:437:                                    ; preds = %426
  %438 = getelementptr inbounds i64, i64* %290, i64 1
  %439 = add nuw nsw i64 %427, 1
  %440 = getelementptr inbounds i64, i64* %290, i64 %439
  %441 = load i64, i64* %438, align 8, !tbaa !2
  %442 = load i64, i64* %440, align 8, !tbaa !2
  store i64 %442, i64* %438, align 8, !tbaa !2
  store i64 %441, i64* %440, align 8, !tbaa !2
  %443 = getelementptr inbounds i64, i64* %290, i64 2
  %444 = add nuw nsw i64 %427, 2
  %445 = getelementptr inbounds i64, i64* %290, i64 %444
  %446 = load i64, i64* %443, align 8, !tbaa !2
  %447 = load i64, i64* %445, align 8, !tbaa !2
  store i64 %447, i64* %443, align 8, !tbaa !2
  store i64 %446, i64* %445, align 8, !tbaa !2
  %448 = getelementptr inbounds i64, i64* %345, i64 -2
  %449 = xor i64 %427, -1
  %450 = getelementptr inbounds i64, i64* %345, i64 %449
  %451 = load i64, i64* %448, align 8, !tbaa !2
  %452 = load i64, i64* %450, align 8, !tbaa !2
  store i64 %452, i64* %448, align 8, !tbaa !2
  store i64 %451, i64* %450, align 8, !tbaa !2
  %453 = getelementptr inbounds i64, i64* %345, i64 -3
  %454 = sub nuw nsw i64 -2, %427
  %455 = getelementptr inbounds i64, i64* %345, i64 %454
  %456 = load i64, i64* %453, align 8, !tbaa !2
  %457 = load i64, i64* %455, align 8, !tbaa !2
  store i64 %457, i64* %453, align 8, !tbaa !2
  store i64 %456, i64* %455, align 8, !tbaa !2
  br label %458

; <label>:458:                                    ; preds = %426, %437, %424
  %459 = icmp sgt i64 %352, 184
  br i1 %459, label %461, label %460

; <label>:460:                                    ; preds = %458
  tail call void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* nonnull %290, i64* %345, i32 %359, i1 zeroext %17)
  br label %19

; <label>:461:                                    ; preds = %458
  %462 = lshr i64 %353, 2
  %463 = add nuw nsw i64 %462, 1
  %464 = getelementptr inbounds i64, i64* %345, i64 %463
  %465 = load i64, i64* %350, align 8, !tbaa !2
  %466 = load i64, i64* %464, align 8, !tbaa !2
  store i64 %466, i64* %350, align 8, !tbaa !2
  store i64 %465, i64* %464, align 8, !tbaa !2
  %467 = sub nsw i64 0, %462
  %468 = getelementptr inbounds i64, i64* %1, i64 %467
  %469 = load i64, i64* %11, align 8, !tbaa !2
  %470 = load i64, i64* %468, align 8, !tbaa !2
  store i64 %470, i64* %11, align 8, !tbaa !2
  store i64 %469, i64* %468, align 8, !tbaa !2
  %471 = icmp sgt i64 %352, 1024
  br i1 %471, label %472, label %579

; <label>:472:                                    ; preds = %461
  %473 = getelementptr inbounds i64, i64* %345, i64 2
  %474 = add nuw nsw i64 %462, 2
  %475 = getelementptr inbounds i64, i64* %345, i64 %474
  %476 = load i64, i64* %473, align 8, !tbaa !2
  %477 = load i64, i64* %475, align 8, !tbaa !2
  store i64 %477, i64* %473, align 8, !tbaa !2
  store i64 %476, i64* %475, align 8, !tbaa !2
  %478 = getelementptr inbounds i64, i64* %345, i64 3
  %479 = add nuw nsw i64 %462, 3
  %480 = getelementptr inbounds i64, i64* %345, i64 %479
  %481 = load i64, i64* %478, align 8, !tbaa !2
  %482 = load i64, i64* %480, align 8, !tbaa !2
  store i64 %482, i64* %478, align 8, !tbaa !2
  store i64 %481, i64* %480, align 8, !tbaa !2
  %483 = xor i64 %462, -1
  %484 = getelementptr inbounds i64, i64* %1, i64 %483
  %485 = load i64, i64* %12, align 8, !tbaa !2
  %486 = load i64, i64* %484, align 8, !tbaa !2
  store i64 %486, i64* %12, align 8, !tbaa !2
  store i64 %485, i64* %484, align 8, !tbaa !2
  %487 = sub nuw nsw i64 -2, %462
  %488 = getelementptr inbounds i64, i64* %1, i64 %487
  %489 = load i64, i64* %13, align 8, !tbaa !2
  %490 = load i64, i64* %488, align 8, !tbaa !2
  store i64 %490, i64* %13, align 8, !tbaa !2
  store i64 %489, i64* %488, align 8, !tbaa !2
  br label %579

; <label>:491:                                    ; preds = %343
  br i1 %319, label %579, label %492

; <label>:492:                                    ; preds = %491
  %493 = icmp ult i64 %344, 2
  br i1 %493, label %528, label %494

; <label>:494:                                    ; preds = %492
  %495 = getelementptr inbounds i64, i64* %290, i64 1
  br label %496

; <label>:496:                                    ; preds = %524, %494
  %497 = phi i64* [ %495, %494 ], [ %526, %524 ]
  %498 = phi i32 [ 0, %494 ], [ %525, %524 ]
  %499 = phi i64* [ %290, %494 ], [ %497, %524 ]
  %500 = ptrtoint i64* %497 to i64
  %501 = icmp sgt i32 %498, 8
  br i1 %501, label %579, label %502

; <label>:502:                                    ; preds = %496
  %503 = load i64, i64* %497, align 8, !tbaa !2
  %504 = load i64, i64* %499, align 8, !tbaa !2
  %505 = icmp ult i64 %503, %504
  br i1 %505, label %506, label %524

; <label>:506:                                    ; preds = %502
  br label %507

; <label>:507:                                    ; preds = %506, %513
  %508 = phi i64 [ %515, %513 ], [ %504, %506 ]
  %509 = phi i64* [ %514, %513 ], [ %499, %506 ]
  %510 = phi i64* [ %511, %513 ], [ %497, %506 ]
  %511 = getelementptr inbounds i64, i64* %510, i64 -1
  store i64 %508, i64* %510, align 8, !tbaa !2
  %512 = icmp eq i64* %511, %290
  br i1 %512, label %517, label %513

; <label>:513:                                    ; preds = %507
  %514 = getelementptr inbounds i64, i64* %509, i64 -1
  %515 = load i64, i64* %514, align 8, !tbaa !2
  %516 = icmp ult i64 %503, %515
  br i1 %516, label %507, label %517

; <label>:517:                                    ; preds = %513, %507
  %518 = phi i64* [ %290, %507 ], [ %511, %513 ]
  %519 = ptrtoint i64* %518 to i64
  store i64 %503, i64* %518, align 8, !tbaa !2
  %520 = sub i64 %500, %519
  %521 = lshr exact i64 %520, 3
  %522 = trunc i64 %521 to i32
  %523 = add i32 %498, %522
  br label %524

; <label>:524:                                    ; preds = %517, %502
  %525 = phi i32 [ %523, %517 ], [ %498, %502 ]
  %526 = getelementptr inbounds i64, i64* %497, i64 1
  %527 = icmp eq i64* %526, %345
  br i1 %527, label %528, label %496

; <label>:528:                                    ; preds = %524, %492
  %529 = icmp eq i64* %350, %1
  %530 = getelementptr inbounds i64, i64* %345, i64 2
  %531 = icmp eq i64* %530, %1
  %532 = or i1 %529, %531
  br i1 %532, label %582, label %533

; <label>:533:                                    ; preds = %528
  br label %534

; <label>:534:                                    ; preds = %533, %567
  %535 = phi i64 [ %569, %567 ], [ 2, %533 ]
  %536 = phi i32 [ %568, %567 ], [ 0, %533 ]
  %537 = phi i64* [ %538, %567 ], [ %350, %533 ]
  %538 = getelementptr inbounds i64, i64* %345, i64 %535
  %539 = ptrtoint i64* %538 to i64
  %540 = icmp sgt i32 %536, 8
  br i1 %540, label %579, label %541

; <label>:541:                                    ; preds = %534
  %542 = load i64, i64* %538, align 8, !tbaa !2
  %543 = load i64, i64* %537, align 8, !tbaa !2
  %544 = icmp ult i64 %542, %543
  br i1 %544, label %545, label %567

; <label>:545:                                    ; preds = %541
  br label %546

; <label>:546:                                    ; preds = %545, %553
  %547 = phi i64 [ %555, %553 ], [ %543, %545 ]
  %548 = phi i64* [ %554, %553 ], [ %537, %545 ]
  %549 = phi i64 [ %551, %553 ], [ %535, %545 ]
  %550 = getelementptr inbounds i64, i64* %345, i64 %549
  %551 = add nsw i64 %549, -1
  store i64 %547, i64* %550, align 8, !tbaa !2
  %552 = icmp eq i64 %551, 1
  br i1 %552, label %560, label %553

; <label>:553:                                    ; preds = %546
  %554 = getelementptr inbounds i64, i64* %548, i64 -1
  %555 = load i64, i64* %554, align 8, !tbaa !2
  %556 = icmp ult i64 %542, %555
  br i1 %556, label %546, label %557

; <label>:557:                                    ; preds = %553
  %558 = getelementptr inbounds i64, i64* %345, i64 %551
  %559 = ptrtoint i64* %558 to i64
  br label %560

; <label>:560:                                    ; preds = %546, %557
  %561 = phi i64 [ %559, %557 ], [ %351, %546 ]
  %562 = phi i64* [ %558, %557 ], [ %350, %546 ]
  store i64 %542, i64* %562, align 8, !tbaa !2
  %563 = sub i64 %539, %561
  %564 = lshr exact i64 %563, 3
  %565 = trunc i64 %564 to i32
  %566 = add i32 %536, %565
  br label %567

; <label>:567:                                    ; preds = %560, %541
  %568 = phi i32 [ %566, %560 ], [ %536, %541 ]
  %569 = add nuw nsw i64 %535, 1
  %570 = getelementptr inbounds i64, i64* %345, i64 %569
  %571 = icmp eq i64* %570, %1
  br i1 %571, label %582, label %534

; <label>:572:                                    ; preds = %285, %264
  %573 = phi i64 [ %244, %264 ], [ %277, %285 ]
  %574 = phi i64* [ %243, %264 ], [ %276, %285 ]
  store i64 %573, i64* %141, align 8, !tbaa !2
  store i64 %238, i64* %574, align 8, !tbaa !2
  %575 = getelementptr inbounds i64, i64* %574, i64 1
  %576 = ptrtoint i64* %575 to i64
  %577 = sub i64 %7, %576
  %578 = icmp slt i64 %577, 192
  br i1 %578, label %19, label %136

; <label>:579:                                    ; preds = %496, %534, %491, %461, %472
  %580 = phi i32 [ %359, %472 ], [ %359, %461 ], [ %16, %491 ], [ %16, %534 ], [ %16, %496 ]
  tail call void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %290, i64* %345, i32 %580, i1 zeroext %17)
  %581 = icmp slt i64 %352, 192
  br i1 %581, label %19, label %14

; <label>:582:                                    ; preds = %528, %567, %420, %110, %609, %53, %596, %19, %24, %25, %82, %83, %361
  ret void

; <label>:583:                                    ; preds = %77
  br label %584

; <label>:584:                                    ; preds = %590, %583
  %585 = phi i64 [ %592, %590 ], [ %80, %583 ]
  %586 = phi i64* [ %591, %590 ], [ %59, %583 ]
  %587 = phi i64* [ %588, %590 ], [ %78, %583 ]
  %588 = getelementptr inbounds i64, i64* %587, i64 -1
  store i64 %585, i64* %587, align 8, !tbaa !2
  %589 = icmp eq i64* %588, %0
  br i1 %589, label %594, label %590

; <label>:590:                                    ; preds = %584
  %591 = getelementptr inbounds i64, i64* %586, i64 -1
  %592 = load i64, i64* %591, align 8, !tbaa !2
  %593 = icmp ult i64 %79, %592
  br i1 %593, label %584, label %594

; <label>:594:                                    ; preds = %590, %584
  %595 = phi i64* [ %0, %584 ], [ %588, %590 ]
  store i64 %79, i64* %595, align 8, !tbaa !2
  br label %596

; <label>:596:                                    ; preds = %594, %77
  %597 = getelementptr inbounds i64, i64* %59, i64 2
  %598 = icmp eq i64* %597, %1
  br i1 %598, label %582, label %58

; <label>:599:                                    ; preds = %131
  br label %600

; <label>:600:                                    ; preds = %600, %599
  %601 = phi i64 [ %606, %600 ], [ %134, %599 ]
  %602 = phi i64* [ %605, %600 ], [ %116, %599 ]
  %603 = phi i64* [ %604, %600 ], [ %132, %599 ]
  %604 = getelementptr inbounds i64, i64* %603, i64 -1
  store i64 %601, i64* %603, align 8, !tbaa !2
  %605 = getelementptr inbounds i64, i64* %602, i64 -1
  %606 = load i64, i64* %605, align 8, !tbaa !2
  %607 = icmp ult i64 %133, %606
  br i1 %607, label %600, label %608

; <label>:608:                                    ; preds = %600
  store i64 %133, i64* %604, align 8, !tbaa !2
  br label %609

; <label>:609:                                    ; preds = %608, %131
  %610 = getelementptr inbounds i64, i64* %116, i64 2
  %611 = icmp eq i64* %610, %1
  br i1 %611, label %582, label %115
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_comp_iterISt4lessImEEEEvT_SC_RT0_(i64*, i64*, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* dereferenceable(1)) local_unnamed_addr #7 comdat {
  %4 = ptrtoint i64* %0 to i64
  %5 = ptrtoint i64* %1 to i64
  %6 = sub i64 %5, %4
  %7 = ashr exact i64 %6, 3
  %8 = icmp slt i64 %6, 16
  br i1 %8, label %106, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 8
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %17, label %16

; <label>:16:                                     ; preds = %9
  br label %67

; <label>:17:                                     ; preds = %9
  %18 = shl nsw i64 %11, 1
  %19 = or i64 %18, 1
  %20 = getelementptr inbounds i64, i64* %0, i64 %19
  %21 = getelementptr inbounds i64, i64* %0, i64 %11
  br label %22

; <label>:22:                                     ; preds = %62, %17
  %23 = phi i64 [ %11, %17 ], [ %66, %62 ]
  %24 = getelementptr inbounds i64, i64* %0, i64 %23
  %25 = load i64, i64* %24, align 8, !tbaa !2
  %26 = icmp sgt i64 %13, %23
  br i1 %26, label %27, label %43

; <label>:27:                                     ; preds = %22
  br label %28

; <label>:28:                                     ; preds = %27, %28
  %29 = phi i64 [ %38, %28 ], [ %23, %27 ]
  %30 = shl i64 %29, 1
  %31 = add i64 %30, 2
  %32 = getelementptr inbounds i64, i64* %0, i64 %31
  %33 = or i64 %30, 1
  %34 = getelementptr inbounds i64, i64* %0, i64 %33
  %35 = load i64, i64* %32, align 8, !tbaa !2
  %36 = load i64, i64* %34, align 8, !tbaa !2
  %37 = icmp ult i64 %35, %36
  %38 = select i1 %37, i64 %33, i64 %31
  %39 = getelementptr inbounds i64, i64* %0, i64 %38
  %40 = load i64, i64* %39, align 8, !tbaa !2
  %41 = getelementptr inbounds i64, i64* %0, i64 %29
  store i64 %40, i64* %41, align 8, !tbaa !2
  %42 = icmp slt i64 %38, %13
  br i1 %42, label %28, label %43

; <label>:43:                                     ; preds = %28, %22
  %44 = phi i64 [ %23, %22 ], [ %38, %28 ]
  %45 = icmp eq i64 %44, %11
  br i1 %45, label %46, label %48

; <label>:46:                                     ; preds = %43
  %47 = load i64, i64* %20, align 8, !tbaa !2
  store i64 %47, i64* %21, align 8, !tbaa !2
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
  %56 = getelementptr inbounds i64, i64* %0, i64 %55
  %57 = load i64, i64* %56, align 8, !tbaa !2
  %58 = icmp ult i64 %57, %25
  br i1 %58, label %59, label %62

; <label>:59:                                     ; preds = %52
  %60 = getelementptr inbounds i64, i64* %0, i64 %53
  store i64 %57, i64* %60, align 8, !tbaa !2
  %61 = icmp sgt i64 %55, %23
  br i1 %61, label %52, label %62

; <label>:62:                                     ; preds = %52, %59, %48
  %63 = phi i64 [ %49, %48 ], [ %55, %59 ], [ %53, %52 ]
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  store i64 %25, i64* %64, align 8, !tbaa !2
  %65 = icmp eq i64 %23, 0
  %66 = add nsw i64 %23, -1
  br i1 %65, label %106, label %22

; <label>:67:                                     ; preds = %16, %101
  %68 = phi i64 [ %105, %101 ], [ %11, %16 ]
  %69 = getelementptr inbounds i64, i64* %0, i64 %68
  %70 = load i64, i64* %69, align 8, !tbaa !2
  %71 = icmp sgt i64 %13, %68
  br i1 %71, label %72, label %101

; <label>:72:                                     ; preds = %67
  br label %73

; <label>:73:                                     ; preds = %72, %73
  %74 = phi i64 [ %83, %73 ], [ %68, %72 ]
  %75 = shl i64 %74, 1
  %76 = add i64 %75, 2
  %77 = getelementptr inbounds i64, i64* %0, i64 %76
  %78 = or i64 %75, 1
  %79 = getelementptr inbounds i64, i64* %0, i64 %78
  %80 = load i64, i64* %77, align 8, !tbaa !2
  %81 = load i64, i64* %79, align 8, !tbaa !2
  %82 = icmp ult i64 %80, %81
  %83 = select i1 %82, i64 %78, i64 %76
  %84 = getelementptr inbounds i64, i64* %0, i64 %83
  %85 = load i64, i64* %84, align 8, !tbaa !2
  %86 = getelementptr inbounds i64, i64* %0, i64 %74
  store i64 %85, i64* %86, align 8, !tbaa !2
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
  %95 = getelementptr inbounds i64, i64* %0, i64 %94
  %96 = load i64, i64* %95, align 8, !tbaa !2
  %97 = icmp ult i64 %96, %70
  br i1 %97, label %98, label %101

; <label>:98:                                     ; preds = %91
  %99 = getelementptr inbounds i64, i64* %0, i64 %92
  store i64 %96, i64* %99, align 8, !tbaa !2
  %100 = icmp sgt i64 %94, %68
  br i1 %100, label %91, label %101

; <label>:101:                                    ; preds = %91, %98, %67, %88
  %102 = phi i64 [ %83, %88 ], [ %68, %67 ], [ %94, %98 ], [ %92, %91 ]
  %103 = getelementptr inbounds i64, i64* %0, i64 %102
  store i64 %70, i64* %103, align 8, !tbaa !2
  %104 = icmp eq i64 %68, 0
  %105 = add nsw i64 %68, -1
  br i1 %104, label %106, label %67

; <label>:106:                                    ; preds = %101, %62, %3
  ret void
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64*, i64*, i64) local_unnamed_addr #7 comdat {
  %4 = alloca %"struct.__gnu_cxx::__ops::_Iter_less_iter", align 1
  %5 = ptrtoint i64* %0 to i64
  %6 = ptrtoint i64* %1 to i64
  %7 = sub i64 %6, %5
  %8 = icmp sgt i64 %7, 128
  br i1 %8, label %9, label %127

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds i64, i64* %0, i64 1
  br label %11

; <label>:11:                                     ; preds = %9, %123
  %12 = phi i64 [ %7, %9 ], [ %125, %123 ]
  %13 = phi i64 [ %2, %9 ], [ %79, %123 ]
  %14 = phi i64* [ %1, %9 ], [ %110, %123 ]
  %15 = icmp eq i64 %13, 0
  br i1 %15, label %16, label %77

; <label>:16:                                     ; preds = %11
  %17 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_less_iter", %"struct.__gnu_cxx::__ops::_Iter_less_iter"* %4, i64 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %17)
  call void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_RT0_(i64* %0, i64* %14, %"struct.__gnu_cxx::__ops::_Iter_less_iter"* nonnull dereferenceable(1) %4)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %17)
  br label %18

; <label>:18:                                     ; preds = %73, %16
  %19 = phi i64* [ %14, %16 ], [ %20, %73 ]
  %20 = getelementptr inbounds i64, i64* %19, i64 -1
  %21 = ptrtoint i64* %20 to i64
  %22 = load i64, i64* %20, align 8, !tbaa !2
  %23 = load i64, i64* %0, align 8, !tbaa !2
  store i64 %23, i64* %20, align 8, !tbaa !2
  %24 = sub i64 %21, %5
  %25 = ashr exact i64 %24, 3
  %26 = add nsw i64 %25, -1
  %27 = sdiv i64 %26, 2
  %28 = icmp sgt i64 %24, 16
  br i1 %28, label %29, label %45

; <label>:29:                                     ; preds = %18
  br label %30

; <label>:30:                                     ; preds = %29, %30
  %31 = phi i64 [ %40, %30 ], [ 0, %29 ]
  %32 = shl i64 %31, 1
  %33 = add i64 %32, 2
  %34 = getelementptr inbounds i64, i64* %0, i64 %33
  %35 = or i64 %32, 1
  %36 = getelementptr inbounds i64, i64* %0, i64 %35
  %37 = load i64, i64* %34, align 8, !tbaa !2
  %38 = load i64, i64* %36, align 8, !tbaa !2
  %39 = icmp ult i64 %37, %38
  %40 = select i1 %39, i64 %35, i64 %33
  %41 = getelementptr inbounds i64, i64* %0, i64 %40
  %42 = load i64, i64* %41, align 8, !tbaa !2
  %43 = getelementptr inbounds i64, i64* %0, i64 %31
  store i64 %42, i64* %43, align 8, !tbaa !2
  %44 = icmp slt i64 %40, %27
  br i1 %44, label %30, label %45

; <label>:45:                                     ; preds = %30, %18
  %46 = phi i64 [ 0, %18 ], [ %40, %30 ]
  %47 = and i64 %24, 8
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
  %56 = getelementptr inbounds i64, i64* %0, i64 %55
  %57 = load i64, i64* %56, align 8, !tbaa !2
  %58 = getelementptr inbounds i64, i64* %0, i64 %46
  store i64 %57, i64* %58, align 8, !tbaa !2
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
  %67 = getelementptr inbounds i64, i64* %0, i64 %66
  %68 = load i64, i64* %67, align 8, !tbaa !2
  %69 = icmp ult i64 %68, %22
  br i1 %69, label %70, label %73

; <label>:70:                                     ; preds = %63
  %71 = getelementptr inbounds i64, i64* %0, i64 %64
  store i64 %68, i64* %71, align 8, !tbaa !2
  %72 = icmp sgt i64 %64, 2
  br i1 %72, label %63, label %73

; <label>:73:                                     ; preds = %70, %63, %59
  %74 = phi i64 [ %60, %59 ], [ %64, %63 ], [ %66, %70 ]
  %75 = getelementptr inbounds i64, i64* %0, i64 %74
  store i64 %22, i64* %75, align 8, !tbaa !2
  %76 = icmp sgt i64 %24, 8
  br i1 %76, label %18, label %127

; <label>:77:                                     ; preds = %11
  %78 = lshr i64 %12, 4
  %79 = add nsw i64 %13, -1
  %80 = getelementptr inbounds i64, i64* %0, i64 %78
  %81 = getelementptr inbounds i64, i64* %14, i64 -1
  %82 = load i64, i64* %10, align 8, !tbaa !2
  %83 = load i64, i64* %80, align 8, !tbaa !2
  %84 = icmp ult i64 %82, %83
  %85 = load i64, i64* %81, align 8, !tbaa !2
  br i1 %84, label %86, label %95

; <label>:86:                                     ; preds = %77
  %87 = icmp ult i64 %83, %85
  br i1 %87, label %88, label %90

; <label>:88:                                     ; preds = %86
  %89 = load i64, i64* %0, align 8, !tbaa !2
  store i64 %83, i64* %0, align 8, !tbaa !2
  store i64 %89, i64* %80, align 8, !tbaa !2
  br label %104

; <label>:90:                                     ; preds = %86
  %91 = icmp ult i64 %82, %85
  %92 = load i64, i64* %0, align 8, !tbaa !2
  br i1 %91, label %93, label %94

; <label>:93:                                     ; preds = %90
  store i64 %85, i64* %0, align 8, !tbaa !2
  store i64 %92, i64* %81, align 8, !tbaa !2
  br label %104

; <label>:94:                                     ; preds = %90
  store i64 %82, i64* %0, align 8, !tbaa !2
  store i64 %92, i64* %10, align 8, !tbaa !2
  br label %104

; <label>:95:                                     ; preds = %77
  %96 = icmp ult i64 %82, %85
  br i1 %96, label %97, label %99

; <label>:97:                                     ; preds = %95
  %98 = load i64, i64* %0, align 8, !tbaa !2
  store i64 %82, i64* %0, align 8, !tbaa !2
  store i64 %98, i64* %10, align 8, !tbaa !2
  br label %104

; <label>:99:                                     ; preds = %95
  %100 = icmp ult i64 %83, %85
  %101 = load i64, i64* %0, align 8, !tbaa !2
  br i1 %100, label %102, label %103

; <label>:102:                                    ; preds = %99
  store i64 %85, i64* %0, align 8, !tbaa !2
  store i64 %101, i64* %81, align 8, !tbaa !2
  br label %104

; <label>:103:                                    ; preds = %99
  store i64 %83, i64* %0, align 8, !tbaa !2
  store i64 %101, i64* %80, align 8, !tbaa !2
  br label %104

; <label>:104:                                    ; preds = %103, %102, %97, %94, %93, %88
  br label %105

; <label>:105:                                    ; preds = %104, %122
  %106 = phi i64* [ %113, %122 ], [ %10, %104 ]
  %107 = phi i64* [ %117, %122 ], [ %14, %104 ]
  %108 = load i64, i64* %0, align 8, !tbaa !2
  br label %109

; <label>:109:                                    ; preds = %109, %105
  %110 = phi i64* [ %106, %105 ], [ %113, %109 ]
  %111 = load i64, i64* %110, align 8, !tbaa !2
  %112 = icmp ult i64 %111, %108
  %113 = getelementptr inbounds i64, i64* %110, i64 1
  br i1 %112, label %109, label %114

; <label>:114:                                    ; preds = %109
  br label %115

; <label>:115:                                    ; preds = %114, %115
  %116 = phi i64* [ %117, %115 ], [ %107, %114 ]
  %117 = getelementptr inbounds i64, i64* %116, i64 -1
  %118 = load i64, i64* %117, align 8, !tbaa !2
  %119 = icmp ult i64 %108, %118
  br i1 %119, label %115, label %120

; <label>:120:                                    ; preds = %115
  %121 = icmp ult i64* %110, %117
  br i1 %121, label %122, label %123

; <label>:122:                                    ; preds = %120
  store i64 %118, i64* %110, align 8, !tbaa !2
  store i64 %111, i64* %117, align 8, !tbaa !2
  br label %105

; <label>:123:                                    ; preds = %120
  tail call void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %110, i64* %14, i64 %79)
  %124 = ptrtoint i64* %110 to i64
  %125 = sub i64 %124, %5
  %126 = icmp sgt i64 %125, 128
  br i1 %126, label %11, label %127

; <label>:127:                                    ; preds = %123, %73, %3
  ret void
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64*, i64*) local_unnamed_addr #7 comdat {
  %3 = ptrtoint i64* %0 to i64
  %4 = ptrtoint i64* %1 to i64
  %5 = sub i64 %4, %3
  %6 = icmp sgt i64 %5, 128
  br i1 %6, label %7, label %79

; <label>:7:                                      ; preds = %2
  %8 = bitcast i64* %0 to i8*
  %9 = getelementptr i64, i64* %0, i64 1
  %10 = bitcast i64* %9 to i8*
  %11 = getelementptr inbounds i64, i64* %0, i64 1
  %12 = load i64, i64* %11, align 8, !tbaa !2
  %13 = load i64, i64* %0, align 8, !tbaa !2
  %14 = icmp ult i64 %12, %13
  %15 = load i64, i64* %0, align 8
  br i1 %14, label %16, label %17

; <label>:16:                                     ; preds = %7
  store i64 %15, i64* %9, align 8
  br label %27

; <label>:17:                                     ; preds = %7
  %18 = icmp ult i64 %12, %15
  br i1 %18, label %19, label %27

; <label>:19:                                     ; preds = %17
  br label %20

; <label>:20:                                     ; preds = %19, %20
  %21 = phi i64 [ %25, %20 ], [ %15, %19 ]
  %22 = phi i64* [ %24, %20 ], [ %0, %19 ]
  %23 = phi i64* [ %22, %20 ], [ %11, %19 ]
  store i64 %21, i64* %23, align 8, !tbaa !2
  %24 = getelementptr inbounds i64, i64* %22, i64 -1
  %25 = load i64, i64* %24, align 8, !tbaa !2
  %26 = icmp ult i64 %12, %25
  br i1 %26, label %20, label %27

; <label>:27:                                     ; preds = %20, %17, %16
  %28 = phi i64* [ %0, %16 ], [ %11, %17 ], [ %22, %20 ]
  store i64 %12, i64* %28, align 8, !tbaa !2
  %29 = getelementptr inbounds i64, i64* %0, i64 2
  %30 = load i64, i64* %29, align 8, !tbaa !2
  %31 = load i64, i64* %0, align 8, !tbaa !2
  %32 = icmp ult i64 %30, %31
  br i1 %32, label %141, label %130

; <label>:33:                                     ; preds = %376
  %34 = getelementptr i64, i64* %1, i64 -17
  %35 = ptrtoint i64* %34 to i64
  %36 = sub i64 %35, %3
  %37 = and i64 %36, 8
  %38 = icmp eq i64 %37, 0
  br i1 %38, label %39, label %55

; <label>:39:                                     ; preds = %33
  %40 = load i64, i64* %378, align 8, !tbaa !2
  %41 = getelementptr inbounds i64, i64* %0, i64 15
  %42 = load i64, i64* %41, align 8, !tbaa !2
  %43 = icmp ult i64 %40, %42
  br i1 %43, label %44, label %52

; <label>:44:                                     ; preds = %39
  br label %45

; <label>:45:                                     ; preds = %45, %44
  %46 = phi i64 [ %50, %45 ], [ %42, %44 ]
  %47 = phi i64* [ %49, %45 ], [ %41, %44 ]
  %48 = phi i64* [ %47, %45 ], [ %378, %44 ]
  store i64 %46, i64* %48, align 8, !tbaa !2
  %49 = getelementptr inbounds i64, i64* %47, i64 -1
  %50 = load i64, i64* %49, align 8, !tbaa !2
  %51 = icmp ult i64 %40, %50
  br i1 %51, label %45, label %52

; <label>:52:                                     ; preds = %45, %39
  %53 = phi i64* [ %378, %39 ], [ %47, %45 ]
  store i64 %40, i64* %53, align 8, !tbaa !2
  %54 = getelementptr inbounds i64, i64* %0, i64 17
  br label %55

; <label>:55:                                     ; preds = %52, %33
  %56 = phi i64* [ %378, %33 ], [ %54, %52 ]
  %57 = icmp ult i64 %36, 8
  br i1 %57, label %117, label %58

; <label>:58:                                     ; preds = %55
  br label %59

; <label>:59:                                     ; preds = %126, %58
  %60 = phi i64* [ %56, %58 ], [ %128, %126 ]
  %61 = load i64, i64* %60, align 8, !tbaa !2
  %62 = getelementptr inbounds i64, i64* %60, i64 -1
  %63 = load i64, i64* %62, align 8, !tbaa !2
  %64 = icmp ult i64 %61, %63
  br i1 %64, label %65, label %73

; <label>:65:                                     ; preds = %59
  br label %66

; <label>:66:                                     ; preds = %65, %66
  %67 = phi i64 [ %71, %66 ], [ %63, %65 ]
  %68 = phi i64* [ %70, %66 ], [ %62, %65 ]
  %69 = phi i64* [ %68, %66 ], [ %60, %65 ]
  store i64 %67, i64* %69, align 8, !tbaa !2
  %70 = getelementptr inbounds i64, i64* %68, i64 -1
  %71 = load i64, i64* %70, align 8, !tbaa !2
  %72 = icmp ult i64 %61, %71
  br i1 %72, label %66, label %73

; <label>:73:                                     ; preds = %66, %59
  %74 = phi i64* [ %60, %59 ], [ %68, %66 ]
  store i64 %61, i64* %74, align 8, !tbaa !2
  %75 = getelementptr inbounds i64, i64* %60, i64 1
  %76 = load i64, i64* %75, align 8, !tbaa !2
  %77 = load i64, i64* %60, align 8, !tbaa !2
  %78 = icmp ult i64 %76, %77
  br i1 %78, label %118, label %126

; <label>:79:                                     ; preds = %2
  %80 = icmp eq i64* %0, %1
  br i1 %80, label %117, label %81

; <label>:81:                                     ; preds = %79
  %82 = getelementptr inbounds i64, i64* %0, i64 1
  %83 = icmp eq i64* %82, %1
  br i1 %83, label %117, label %84

; <label>:84:                                     ; preds = %81
  %85 = bitcast i64* %0 to i8*
  br label %86

; <label>:86:                                     ; preds = %113, %84
  %87 = phi i64* [ %82, %84 ], [ %115, %113 ]
  %88 = phi i64* [ %0, %84 ], [ %87, %113 ]
  %89 = load i64, i64* %87, align 8, !tbaa !2
  %90 = load i64, i64* %0, align 8, !tbaa !2
  %91 = icmp ult i64 %89, %90
  br i1 %91, label %92, label %102

; <label>:92:                                     ; preds = %86
  %93 = ptrtoint i64* %87 to i64
  %94 = sub i64 %93, %3
  %95 = icmp eq i64 %94, 0
  br i1 %95, label %113, label %96

; <label>:96:                                     ; preds = %92
  %97 = getelementptr inbounds i64, i64* %88, i64 2
  %98 = ashr exact i64 %94, 3
  %99 = sub nsw i64 0, %98
  %100 = getelementptr inbounds i64, i64* %97, i64 %99
  %101 = bitcast i64* %100 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %101, i8* nonnull %85, i64 %94, i32 8, i1 false) #2
  br label %113

; <label>:102:                                    ; preds = %86
  %103 = load i64, i64* %88, align 8, !tbaa !2
  %104 = icmp ult i64 %89, %103
  br i1 %104, label %105, label %113

; <label>:105:                                    ; preds = %102
  br label %106

; <label>:106:                                    ; preds = %105, %106
  %107 = phi i64 [ %111, %106 ], [ %103, %105 ]
  %108 = phi i64* [ %110, %106 ], [ %88, %105 ]
  %109 = phi i64* [ %108, %106 ], [ %87, %105 ]
  store i64 %107, i64* %109, align 8, !tbaa !2
  %110 = getelementptr inbounds i64, i64* %108, i64 -1
  %111 = load i64, i64* %110, align 8, !tbaa !2
  %112 = icmp ult i64 %89, %111
  br i1 %112, label %106, label %113

; <label>:113:                                    ; preds = %106, %102, %92, %96
  %114 = phi i64* [ %0, %96 ], [ %0, %92 ], [ %87, %102 ], [ %108, %106 ]
  store i64 %89, i64* %114, align 8, !tbaa !2
  %115 = getelementptr inbounds i64, i64* %87, i64 1
  %116 = icmp eq i64* %115, %1
  br i1 %116, label %117, label %86

; <label>:117:                                    ; preds = %113, %55, %126, %81, %79, %376
  ret void

; <label>:118:                                    ; preds = %73
  br label %119

; <label>:119:                                    ; preds = %119, %118
  %120 = phi i64 [ %124, %119 ], [ %77, %118 ]
  %121 = phi i64* [ %123, %119 ], [ %60, %118 ]
  %122 = phi i64* [ %121, %119 ], [ %75, %118 ]
  store i64 %120, i64* %122, align 8, !tbaa !2
  %123 = getelementptr inbounds i64, i64* %121, i64 -1
  %124 = load i64, i64* %123, align 8, !tbaa !2
  %125 = icmp ult i64 %76, %124
  br i1 %125, label %119, label %126

; <label>:126:                                    ; preds = %119, %73
  %127 = phi i64* [ %75, %73 ], [ %121, %119 ]
  store i64 %76, i64* %127, align 8, !tbaa !2
  %128 = getelementptr inbounds i64, i64* %60, i64 2
  %129 = icmp eq i64* %128, %1
  br i1 %129, label %117, label %59

; <label>:130:                                    ; preds = %27
  %131 = load i64, i64* %11, align 8, !tbaa !2
  %132 = icmp ult i64 %30, %131
  br i1 %132, label %133, label %142

; <label>:133:                                    ; preds = %130
  br label %134

; <label>:134:                                    ; preds = %134, %133
  %135 = phi i64 [ %139, %134 ], [ %131, %133 ]
  %136 = phi i64* [ %138, %134 ], [ %11, %133 ]
  %137 = phi i64* [ %136, %134 ], [ %29, %133 ]
  store i64 %135, i64* %137, align 8, !tbaa !2
  %138 = getelementptr inbounds i64, i64* %136, i64 -1
  %139 = load i64, i64* %138, align 8, !tbaa !2
  %140 = icmp ult i64 %30, %139
  br i1 %140, label %134, label %142

; <label>:141:                                    ; preds = %27
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 16, i32 8, i1 false) #2
  br label %142

; <label>:142:                                    ; preds = %134, %141, %130
  %143 = phi i64* [ %0, %141 ], [ %29, %130 ], [ %136, %134 ]
  store i64 %30, i64* %143, align 8, !tbaa !2
  %144 = getelementptr inbounds i64, i64* %0, i64 3
  %145 = load i64, i64* %144, align 8, !tbaa !2
  %146 = load i64, i64* %0, align 8, !tbaa !2
  %147 = icmp ult i64 %145, %146
  br i1 %147, label %159, label %148

; <label>:148:                                    ; preds = %142
  %149 = load i64, i64* %29, align 8, !tbaa !2
  %150 = icmp ult i64 %145, %149
  br i1 %150, label %151, label %160

; <label>:151:                                    ; preds = %148
  br label %152

; <label>:152:                                    ; preds = %152, %151
  %153 = phi i64 [ %157, %152 ], [ %149, %151 ]
  %154 = phi i64* [ %156, %152 ], [ %29, %151 ]
  %155 = phi i64* [ %154, %152 ], [ %144, %151 ]
  store i64 %153, i64* %155, align 8, !tbaa !2
  %156 = getelementptr inbounds i64, i64* %154, i64 -1
  %157 = load i64, i64* %156, align 8, !tbaa !2
  %158 = icmp ult i64 %145, %157
  br i1 %158, label %152, label %160

; <label>:159:                                    ; preds = %142
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 24, i32 8, i1 false) #2
  br label %160

; <label>:160:                                    ; preds = %152, %159, %148
  %161 = phi i64* [ %0, %159 ], [ %144, %148 ], [ %154, %152 ]
  store i64 %145, i64* %161, align 8, !tbaa !2
  %162 = getelementptr inbounds i64, i64* %0, i64 4
  %163 = load i64, i64* %162, align 8, !tbaa !2
  %164 = load i64, i64* %0, align 8, !tbaa !2
  %165 = icmp ult i64 %163, %164
  br i1 %165, label %177, label %166

; <label>:166:                                    ; preds = %160
  %167 = load i64, i64* %144, align 8, !tbaa !2
  %168 = icmp ult i64 %163, %167
  br i1 %168, label %169, label %178

; <label>:169:                                    ; preds = %166
  br label %170

; <label>:170:                                    ; preds = %170, %169
  %171 = phi i64 [ %175, %170 ], [ %167, %169 ]
  %172 = phi i64* [ %174, %170 ], [ %144, %169 ]
  %173 = phi i64* [ %172, %170 ], [ %162, %169 ]
  store i64 %171, i64* %173, align 8, !tbaa !2
  %174 = getelementptr inbounds i64, i64* %172, i64 -1
  %175 = load i64, i64* %174, align 8, !tbaa !2
  %176 = icmp ult i64 %163, %175
  br i1 %176, label %170, label %178

; <label>:177:                                    ; preds = %160
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 32, i32 8, i1 false) #2
  br label %178

; <label>:178:                                    ; preds = %170, %177, %166
  %179 = phi i64* [ %0, %177 ], [ %162, %166 ], [ %172, %170 ]
  store i64 %163, i64* %179, align 8, !tbaa !2
  %180 = getelementptr inbounds i64, i64* %0, i64 5
  %181 = load i64, i64* %180, align 8, !tbaa !2
  %182 = load i64, i64* %0, align 8, !tbaa !2
  %183 = icmp ult i64 %181, %182
  br i1 %183, label %195, label %184

; <label>:184:                                    ; preds = %178
  %185 = load i64, i64* %162, align 8, !tbaa !2
  %186 = icmp ult i64 %181, %185
  br i1 %186, label %187, label %196

; <label>:187:                                    ; preds = %184
  br label %188

; <label>:188:                                    ; preds = %188, %187
  %189 = phi i64 [ %193, %188 ], [ %185, %187 ]
  %190 = phi i64* [ %192, %188 ], [ %162, %187 ]
  %191 = phi i64* [ %190, %188 ], [ %180, %187 ]
  store i64 %189, i64* %191, align 8, !tbaa !2
  %192 = getelementptr inbounds i64, i64* %190, i64 -1
  %193 = load i64, i64* %192, align 8, !tbaa !2
  %194 = icmp ult i64 %181, %193
  br i1 %194, label %188, label %196

; <label>:195:                                    ; preds = %178
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 40, i32 8, i1 false) #2
  br label %196

; <label>:196:                                    ; preds = %188, %195, %184
  %197 = phi i64* [ %0, %195 ], [ %180, %184 ], [ %190, %188 ]
  store i64 %181, i64* %197, align 8, !tbaa !2
  %198 = getelementptr inbounds i64, i64* %0, i64 6
  %199 = load i64, i64* %198, align 8, !tbaa !2
  %200 = load i64, i64* %0, align 8, !tbaa !2
  %201 = icmp ult i64 %199, %200
  br i1 %201, label %213, label %202

; <label>:202:                                    ; preds = %196
  %203 = load i64, i64* %180, align 8, !tbaa !2
  %204 = icmp ult i64 %199, %203
  br i1 %204, label %205, label %214

; <label>:205:                                    ; preds = %202
  br label %206

; <label>:206:                                    ; preds = %206, %205
  %207 = phi i64 [ %211, %206 ], [ %203, %205 ]
  %208 = phi i64* [ %210, %206 ], [ %180, %205 ]
  %209 = phi i64* [ %208, %206 ], [ %198, %205 ]
  store i64 %207, i64* %209, align 8, !tbaa !2
  %210 = getelementptr inbounds i64, i64* %208, i64 -1
  %211 = load i64, i64* %210, align 8, !tbaa !2
  %212 = icmp ult i64 %199, %211
  br i1 %212, label %206, label %214

; <label>:213:                                    ; preds = %196
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 48, i32 8, i1 false) #2
  br label %214

; <label>:214:                                    ; preds = %206, %213, %202
  %215 = phi i64* [ %0, %213 ], [ %198, %202 ], [ %208, %206 ]
  store i64 %199, i64* %215, align 8, !tbaa !2
  %216 = getelementptr inbounds i64, i64* %0, i64 7
  %217 = load i64, i64* %216, align 8, !tbaa !2
  %218 = load i64, i64* %0, align 8, !tbaa !2
  %219 = icmp ult i64 %217, %218
  br i1 %219, label %231, label %220

; <label>:220:                                    ; preds = %214
  %221 = load i64, i64* %198, align 8, !tbaa !2
  %222 = icmp ult i64 %217, %221
  br i1 %222, label %223, label %232

; <label>:223:                                    ; preds = %220
  br label %224

; <label>:224:                                    ; preds = %224, %223
  %225 = phi i64 [ %229, %224 ], [ %221, %223 ]
  %226 = phi i64* [ %228, %224 ], [ %198, %223 ]
  %227 = phi i64* [ %226, %224 ], [ %216, %223 ]
  store i64 %225, i64* %227, align 8, !tbaa !2
  %228 = getelementptr inbounds i64, i64* %226, i64 -1
  %229 = load i64, i64* %228, align 8, !tbaa !2
  %230 = icmp ult i64 %217, %229
  br i1 %230, label %224, label %232

; <label>:231:                                    ; preds = %214
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 56, i32 8, i1 false) #2
  br label %232

; <label>:232:                                    ; preds = %224, %231, %220
  %233 = phi i64* [ %0, %231 ], [ %216, %220 ], [ %226, %224 ]
  store i64 %217, i64* %233, align 8, !tbaa !2
  %234 = getelementptr inbounds i64, i64* %0, i64 8
  %235 = load i64, i64* %234, align 8, !tbaa !2
  %236 = load i64, i64* %0, align 8, !tbaa !2
  %237 = icmp ult i64 %235, %236
  br i1 %237, label %249, label %238

; <label>:238:                                    ; preds = %232
  %239 = load i64, i64* %216, align 8, !tbaa !2
  %240 = icmp ult i64 %235, %239
  br i1 %240, label %241, label %250

; <label>:241:                                    ; preds = %238
  br label %242

; <label>:242:                                    ; preds = %242, %241
  %243 = phi i64 [ %247, %242 ], [ %239, %241 ]
  %244 = phi i64* [ %246, %242 ], [ %216, %241 ]
  %245 = phi i64* [ %244, %242 ], [ %234, %241 ]
  store i64 %243, i64* %245, align 8, !tbaa !2
  %246 = getelementptr inbounds i64, i64* %244, i64 -1
  %247 = load i64, i64* %246, align 8, !tbaa !2
  %248 = icmp ult i64 %235, %247
  br i1 %248, label %242, label %250

; <label>:249:                                    ; preds = %232
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 64, i32 8, i1 false) #2
  br label %250

; <label>:250:                                    ; preds = %242, %249, %238
  %251 = phi i64* [ %0, %249 ], [ %234, %238 ], [ %244, %242 ]
  store i64 %235, i64* %251, align 8, !tbaa !2
  %252 = getelementptr inbounds i64, i64* %0, i64 9
  %253 = load i64, i64* %252, align 8, !tbaa !2
  %254 = load i64, i64* %0, align 8, !tbaa !2
  %255 = icmp ult i64 %253, %254
  br i1 %255, label %267, label %256

; <label>:256:                                    ; preds = %250
  %257 = load i64, i64* %234, align 8, !tbaa !2
  %258 = icmp ult i64 %253, %257
  br i1 %258, label %259, label %268

; <label>:259:                                    ; preds = %256
  br label %260

; <label>:260:                                    ; preds = %260, %259
  %261 = phi i64 [ %265, %260 ], [ %257, %259 ]
  %262 = phi i64* [ %264, %260 ], [ %234, %259 ]
  %263 = phi i64* [ %262, %260 ], [ %252, %259 ]
  store i64 %261, i64* %263, align 8, !tbaa !2
  %264 = getelementptr inbounds i64, i64* %262, i64 -1
  %265 = load i64, i64* %264, align 8, !tbaa !2
  %266 = icmp ult i64 %253, %265
  br i1 %266, label %260, label %268

; <label>:267:                                    ; preds = %250
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 72, i32 8, i1 false) #2
  br label %268

; <label>:268:                                    ; preds = %260, %267, %256
  %269 = phi i64* [ %0, %267 ], [ %252, %256 ], [ %262, %260 ]
  store i64 %253, i64* %269, align 8, !tbaa !2
  %270 = getelementptr inbounds i64, i64* %0, i64 10
  %271 = load i64, i64* %270, align 8, !tbaa !2
  %272 = load i64, i64* %0, align 8, !tbaa !2
  %273 = icmp ult i64 %271, %272
  br i1 %273, label %285, label %274

; <label>:274:                                    ; preds = %268
  %275 = load i64, i64* %252, align 8, !tbaa !2
  %276 = icmp ult i64 %271, %275
  br i1 %276, label %277, label %286

; <label>:277:                                    ; preds = %274
  br label %278

; <label>:278:                                    ; preds = %278, %277
  %279 = phi i64 [ %283, %278 ], [ %275, %277 ]
  %280 = phi i64* [ %282, %278 ], [ %252, %277 ]
  %281 = phi i64* [ %280, %278 ], [ %270, %277 ]
  store i64 %279, i64* %281, align 8, !tbaa !2
  %282 = getelementptr inbounds i64, i64* %280, i64 -1
  %283 = load i64, i64* %282, align 8, !tbaa !2
  %284 = icmp ult i64 %271, %283
  br i1 %284, label %278, label %286

; <label>:285:                                    ; preds = %268
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 80, i32 8, i1 false) #2
  br label %286

; <label>:286:                                    ; preds = %278, %285, %274
  %287 = phi i64* [ %0, %285 ], [ %270, %274 ], [ %280, %278 ]
  store i64 %271, i64* %287, align 8, !tbaa !2
  %288 = getelementptr inbounds i64, i64* %0, i64 11
  %289 = load i64, i64* %288, align 8, !tbaa !2
  %290 = load i64, i64* %0, align 8, !tbaa !2
  %291 = icmp ult i64 %289, %290
  br i1 %291, label %303, label %292

; <label>:292:                                    ; preds = %286
  %293 = load i64, i64* %270, align 8, !tbaa !2
  %294 = icmp ult i64 %289, %293
  br i1 %294, label %295, label %304

; <label>:295:                                    ; preds = %292
  br label %296

; <label>:296:                                    ; preds = %296, %295
  %297 = phi i64 [ %301, %296 ], [ %293, %295 ]
  %298 = phi i64* [ %300, %296 ], [ %270, %295 ]
  %299 = phi i64* [ %298, %296 ], [ %288, %295 ]
  store i64 %297, i64* %299, align 8, !tbaa !2
  %300 = getelementptr inbounds i64, i64* %298, i64 -1
  %301 = load i64, i64* %300, align 8, !tbaa !2
  %302 = icmp ult i64 %289, %301
  br i1 %302, label %296, label %304

; <label>:303:                                    ; preds = %286
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 88, i32 8, i1 false) #2
  br label %304

; <label>:304:                                    ; preds = %296, %303, %292
  %305 = phi i64* [ %0, %303 ], [ %288, %292 ], [ %298, %296 ]
  store i64 %289, i64* %305, align 8, !tbaa !2
  %306 = getelementptr inbounds i64, i64* %0, i64 12
  %307 = load i64, i64* %306, align 8, !tbaa !2
  %308 = load i64, i64* %0, align 8, !tbaa !2
  %309 = icmp ult i64 %307, %308
  br i1 %309, label %321, label %310

; <label>:310:                                    ; preds = %304
  %311 = load i64, i64* %288, align 8, !tbaa !2
  %312 = icmp ult i64 %307, %311
  br i1 %312, label %313, label %322

; <label>:313:                                    ; preds = %310
  br label %314

; <label>:314:                                    ; preds = %314, %313
  %315 = phi i64 [ %319, %314 ], [ %311, %313 ]
  %316 = phi i64* [ %318, %314 ], [ %288, %313 ]
  %317 = phi i64* [ %316, %314 ], [ %306, %313 ]
  store i64 %315, i64* %317, align 8, !tbaa !2
  %318 = getelementptr inbounds i64, i64* %316, i64 -1
  %319 = load i64, i64* %318, align 8, !tbaa !2
  %320 = icmp ult i64 %307, %319
  br i1 %320, label %314, label %322

; <label>:321:                                    ; preds = %304
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 96, i32 8, i1 false) #2
  br label %322

; <label>:322:                                    ; preds = %314, %321, %310
  %323 = phi i64* [ %0, %321 ], [ %306, %310 ], [ %316, %314 ]
  store i64 %307, i64* %323, align 8, !tbaa !2
  %324 = getelementptr inbounds i64, i64* %0, i64 13
  %325 = load i64, i64* %324, align 8, !tbaa !2
  %326 = load i64, i64* %0, align 8, !tbaa !2
  %327 = icmp ult i64 %325, %326
  br i1 %327, label %339, label %328

; <label>:328:                                    ; preds = %322
  %329 = load i64, i64* %306, align 8, !tbaa !2
  %330 = icmp ult i64 %325, %329
  br i1 %330, label %331, label %340

; <label>:331:                                    ; preds = %328
  br label %332

; <label>:332:                                    ; preds = %332, %331
  %333 = phi i64 [ %337, %332 ], [ %329, %331 ]
  %334 = phi i64* [ %336, %332 ], [ %306, %331 ]
  %335 = phi i64* [ %334, %332 ], [ %324, %331 ]
  store i64 %333, i64* %335, align 8, !tbaa !2
  %336 = getelementptr inbounds i64, i64* %334, i64 -1
  %337 = load i64, i64* %336, align 8, !tbaa !2
  %338 = icmp ult i64 %325, %337
  br i1 %338, label %332, label %340

; <label>:339:                                    ; preds = %322
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 104, i32 8, i1 false) #2
  br label %340

; <label>:340:                                    ; preds = %332, %339, %328
  %341 = phi i64* [ %0, %339 ], [ %324, %328 ], [ %334, %332 ]
  store i64 %325, i64* %341, align 8, !tbaa !2
  %342 = getelementptr inbounds i64, i64* %0, i64 14
  %343 = load i64, i64* %342, align 8, !tbaa !2
  %344 = load i64, i64* %0, align 8, !tbaa !2
  %345 = icmp ult i64 %343, %344
  br i1 %345, label %357, label %346

; <label>:346:                                    ; preds = %340
  %347 = load i64, i64* %324, align 8, !tbaa !2
  %348 = icmp ult i64 %343, %347
  br i1 %348, label %349, label %358

; <label>:349:                                    ; preds = %346
  br label %350

; <label>:350:                                    ; preds = %350, %349
  %351 = phi i64 [ %355, %350 ], [ %347, %349 ]
  %352 = phi i64* [ %354, %350 ], [ %324, %349 ]
  %353 = phi i64* [ %352, %350 ], [ %342, %349 ]
  store i64 %351, i64* %353, align 8, !tbaa !2
  %354 = getelementptr inbounds i64, i64* %352, i64 -1
  %355 = load i64, i64* %354, align 8, !tbaa !2
  %356 = icmp ult i64 %343, %355
  br i1 %356, label %350, label %358

; <label>:357:                                    ; preds = %340
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 112, i32 8, i1 false) #2
  br label %358

; <label>:358:                                    ; preds = %350, %357, %346
  %359 = phi i64* [ %0, %357 ], [ %342, %346 ], [ %352, %350 ]
  store i64 %343, i64* %359, align 8, !tbaa !2
  %360 = getelementptr inbounds i64, i64* %0, i64 15
  %361 = load i64, i64* %360, align 8, !tbaa !2
  %362 = load i64, i64* %0, align 8, !tbaa !2
  %363 = icmp ult i64 %361, %362
  br i1 %363, label %375, label %364

; <label>:364:                                    ; preds = %358
  %365 = load i64, i64* %342, align 8, !tbaa !2
  %366 = icmp ult i64 %361, %365
  br i1 %366, label %367, label %376

; <label>:367:                                    ; preds = %364
  br label %368

; <label>:368:                                    ; preds = %368, %367
  %369 = phi i64 [ %373, %368 ], [ %365, %367 ]
  %370 = phi i64* [ %372, %368 ], [ %342, %367 ]
  %371 = phi i64* [ %370, %368 ], [ %360, %367 ]
  store i64 %369, i64* %371, align 8, !tbaa !2
  %372 = getelementptr inbounds i64, i64* %370, i64 -1
  %373 = load i64, i64* %372, align 8, !tbaa !2
  %374 = icmp ult i64 %361, %373
  br i1 %374, label %368, label %376

; <label>:375:                                    ; preds = %358
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 120, i32 8, i1 false) #2
  br label %376

; <label>:376:                                    ; preds = %368, %375, %364
  %377 = phi i64* [ %0, %375 ], [ %360, %364 ], [ %370, %368 ]
  store i64 %361, i64* %377, align 8, !tbaa !2
  %378 = getelementptr inbounds i64, i64* %0, i64 16
  %379 = icmp eq i64* %378, %1
  br i1 %379, label %117, label %33
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_RT0_(i64*, i64*, %"struct.__gnu_cxx::__ops::_Iter_less_iter"* dereferenceable(1)) local_unnamed_addr #7 comdat {
  %4 = ptrtoint i64* %0 to i64
  %5 = ptrtoint i64* %1 to i64
  %6 = sub i64 %5, %4
  %7 = ashr exact i64 %6, 3
  %8 = icmp slt i64 %6, 16
  br i1 %8, label %106, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 8
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %17, label %16

; <label>:16:                                     ; preds = %9
  br label %67

; <label>:17:                                     ; preds = %9
  %18 = shl nsw i64 %11, 1
  %19 = or i64 %18, 1
  %20 = getelementptr inbounds i64, i64* %0, i64 %19
  %21 = getelementptr inbounds i64, i64* %0, i64 %11
  br label %22

; <label>:22:                                     ; preds = %62, %17
  %23 = phi i64 [ %11, %17 ], [ %66, %62 ]
  %24 = getelementptr inbounds i64, i64* %0, i64 %23
  %25 = load i64, i64* %24, align 8, !tbaa !2
  %26 = icmp sgt i64 %13, %23
  br i1 %26, label %27, label %43

; <label>:27:                                     ; preds = %22
  br label %28

; <label>:28:                                     ; preds = %27, %28
  %29 = phi i64 [ %38, %28 ], [ %23, %27 ]
  %30 = shl i64 %29, 1
  %31 = add i64 %30, 2
  %32 = getelementptr inbounds i64, i64* %0, i64 %31
  %33 = or i64 %30, 1
  %34 = getelementptr inbounds i64, i64* %0, i64 %33
  %35 = load i64, i64* %32, align 8, !tbaa !2
  %36 = load i64, i64* %34, align 8, !tbaa !2
  %37 = icmp ult i64 %35, %36
  %38 = select i1 %37, i64 %33, i64 %31
  %39 = getelementptr inbounds i64, i64* %0, i64 %38
  %40 = load i64, i64* %39, align 8, !tbaa !2
  %41 = getelementptr inbounds i64, i64* %0, i64 %29
  store i64 %40, i64* %41, align 8, !tbaa !2
  %42 = icmp slt i64 %38, %13
  br i1 %42, label %28, label %43

; <label>:43:                                     ; preds = %28, %22
  %44 = phi i64 [ %23, %22 ], [ %38, %28 ]
  %45 = icmp eq i64 %44, %11
  br i1 %45, label %46, label %48

; <label>:46:                                     ; preds = %43
  %47 = load i64, i64* %20, align 8, !tbaa !2
  store i64 %47, i64* %21, align 8, !tbaa !2
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
  %56 = getelementptr inbounds i64, i64* %0, i64 %55
  %57 = load i64, i64* %56, align 8, !tbaa !2
  %58 = icmp ult i64 %57, %25
  br i1 %58, label %59, label %62

; <label>:59:                                     ; preds = %52
  %60 = getelementptr inbounds i64, i64* %0, i64 %53
  store i64 %57, i64* %60, align 8, !tbaa !2
  %61 = icmp sgt i64 %55, %23
  br i1 %61, label %52, label %62

; <label>:62:                                     ; preds = %52, %59, %48
  %63 = phi i64 [ %49, %48 ], [ %55, %59 ], [ %53, %52 ]
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  store i64 %25, i64* %64, align 8, !tbaa !2
  %65 = icmp eq i64 %23, 0
  %66 = add nsw i64 %23, -1
  br i1 %65, label %106, label %22

; <label>:67:                                     ; preds = %16, %101
  %68 = phi i64 [ %105, %101 ], [ %11, %16 ]
  %69 = getelementptr inbounds i64, i64* %0, i64 %68
  %70 = load i64, i64* %69, align 8, !tbaa !2
  %71 = icmp sgt i64 %13, %68
  br i1 %71, label %72, label %101

; <label>:72:                                     ; preds = %67
  br label %73

; <label>:73:                                     ; preds = %72, %73
  %74 = phi i64 [ %83, %73 ], [ %68, %72 ]
  %75 = shl i64 %74, 1
  %76 = add i64 %75, 2
  %77 = getelementptr inbounds i64, i64* %0, i64 %76
  %78 = or i64 %75, 1
  %79 = getelementptr inbounds i64, i64* %0, i64 %78
  %80 = load i64, i64* %77, align 8, !tbaa !2
  %81 = load i64, i64* %79, align 8, !tbaa !2
  %82 = icmp ult i64 %80, %81
  %83 = select i1 %82, i64 %78, i64 %76
  %84 = getelementptr inbounds i64, i64* %0, i64 %83
  %85 = load i64, i64* %84, align 8, !tbaa !2
  %86 = getelementptr inbounds i64, i64* %0, i64 %74
  store i64 %85, i64* %86, align 8, !tbaa !2
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
  %95 = getelementptr inbounds i64, i64* %0, i64 %94
  %96 = load i64, i64* %95, align 8, !tbaa !2
  %97 = icmp ult i64 %96, %70
  br i1 %97, label %98, label %101

; <label>:98:                                     ; preds = %91
  %99 = getelementptr inbounds i64, i64* %0, i64 %92
  store i64 %96, i64* %99, align 8, !tbaa !2
  %100 = icmp sgt i64 %94, %68
  br i1 %100, label %91, label %101

; <label>:101:                                    ; preds = %91, %98, %67, %88
  %102 = phi i64 [ %83, %88 ], [ %68, %67 ], [ %94, %98 ], [ %92, %91 ]
  %103 = getelementptr inbounds i64, i64* %0, i64 %102
  store i64 %70, i64* %103, align 8, !tbaa !2
  %104 = icmp eq i64 %68, 0
  %105 = add nsw i64 %68, -1
  br i1 %104, label %106, label %67

; <label>:106:                                    ; preds = %101, %62, %3
  ret void
}

; Function Attrs: nounwind readnone speculatable
declare i64 @llvm.ctlz.i64(i64, i1) #15

; Function Attrs: uwtable
define linkonce_odr dereferenceable(24) %"class.std::vector"* @_ZNSt6vectorImSaImEEaSERKS1_(%"class.std::vector"*, %"class.std::vector"* dereferenceable(24)) local_unnamed_addr #7 comdat align 2 personality i32 (...)* @__gxx_personality_v0 {
  %3 = icmp eq %"class.std::vector"* %1, %0
  br i1 %3, label %80, label %4

; <label>:4:                                      ; preds = %2
  %5 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %1, i64 0, i32 0, i32 0, i32 1
  %6 = bitcast i64** %5 to i64*
  %7 = load i64, i64* %6, align 8, !tbaa !22
  %8 = bitcast %"class.std::vector"* %1 to i64*
  %9 = load i64, i64* %8, align 8, !tbaa !19
  %10 = sub i64 %7, %9
  %11 = ashr exact i64 %10, 3
  %12 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %13 = bitcast i64** %12 to i64*
  %14 = load i64, i64* %13, align 8, !tbaa !28
  %15 = bitcast %"class.std::vector"* %0 to i64*
  %16 = load i64, i64* %15, align 8, !tbaa !19
  %17 = sub i64 %14, %16
  %18 = ashr exact i64 %17, 3
  %19 = icmp ugt i64 %11, %18
  %20 = inttoptr i64 %9 to i64*
  %21 = inttoptr i64 %16 to i8*
  br i1 %19, label %22, label %41

; <label>:22:                                     ; preds = %4
  %23 = icmp eq i64 %10, 0
  br i1 %23, label %31, label %24

; <label>:24:                                     ; preds = %22
  %25 = icmp ugt i64 %11, 2305843009213693951
  br i1 %25, label %26, label %27

; <label>:26:                                     ; preds = %24
  tail call void @_ZSt17__throw_bad_allocv() #16
  unreachable

; <label>:27:                                     ; preds = %24
  %28 = tail call i8* @_Znwm(i64 %10)
  %29 = bitcast i8* %28 to i64*
  %30 = inttoptr i64 %9 to i8*
  tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %28, i8* %30, i64 %10, i32 8, i1 false) #2
  br label %31

; <label>:31:                                     ; preds = %22, %27
  %32 = phi i64* [ %29, %27 ], [ null, %22 ]
  %33 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %34 = load i64*, i64** %33, align 8, !tbaa !19
  %35 = icmp eq i64* %34, null
  br i1 %35, label %38, label %36

; <label>:36:                                     ; preds = %31
  %37 = bitcast i64* %34 to i8*
  tail call void @_ZdlPv(i8* %37) #2
  br label %38

; <label>:38:                                     ; preds = %31, %36
  store i64* %32, i64** %33, align 8, !tbaa !19
  %39 = getelementptr inbounds i64, i64* %32, i64 %11
  store i64* %39, i64** %12, align 8, !tbaa !28
  %40 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  br label %75

; <label>:41:                                     ; preds = %4
  %42 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  %43 = bitcast i64** %42 to i64*
  %44 = load i64, i64* %43, align 8, !tbaa !22
  %45 = sub i64 %44, %16
  %46 = ashr exact i64 %45, 3
  %47 = icmp ult i64 %46, %11
  %48 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %1, i64 0, i32 0, i32 0, i32 0
  br i1 %47, label %53, label %49

; <label>:49:                                     ; preds = %41
  %50 = icmp eq i64 %10, 0
  br i1 %50, label %75, label %51

; <label>:51:                                     ; preds = %49
  %52 = inttoptr i64 %9 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* %21, i8* %52, i64 %10, i32 8, i1 false) #2
  br label %75

; <label>:53:                                     ; preds = %41
  %54 = icmp eq i64 %45, 0
  br i1 %54, label %63, label %55

; <label>:55:                                     ; preds = %53
  %56 = inttoptr i64 %9 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* %21, i8* %56, i64 %45, i32 8, i1 false) #2
  %57 = load i64*, i64** %48, align 8, !tbaa !19
  %58 = load i64, i64* %43, align 8, !tbaa !22
  %59 = load i64, i64* %15, align 8, !tbaa !19
  %60 = load i64, i64* %6, align 8, !tbaa !22
  %61 = sub i64 %58, %59
  %62 = ashr exact i64 %61, 3
  br label %63

; <label>:63:                                     ; preds = %53, %55
  %64 = phi i64 [ 0, %53 ], [ %62, %55 ]
  %65 = phi i64 [ %44, %53 ], [ %58, %55 ]
  %66 = phi i64 [ %7, %53 ], [ %60, %55 ]
  %67 = phi i64* [ %20, %53 ], [ %57, %55 ]
  %68 = getelementptr inbounds i64, i64* %67, i64 %64
  %69 = ptrtoint i64* %68 to i64
  %70 = sub i64 %66, %69
  %71 = icmp eq i64 %70, 0
  br i1 %71, label %75, label %72

; <label>:72:                                     ; preds = %63
  %73 = inttoptr i64 %65 to i8*
  %74 = bitcast i64* %68 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* %73, i8* %74, i64 %70, i32 8, i1 false) #2
  br label %75

; <label>:75:                                     ; preds = %51, %49, %72, %63, %38
  %76 = phi i64** [ %42, %51 ], [ %42, %49 ], [ %42, %72 ], [ %42, %63 ], [ %40, %38 ]
  %77 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %78 = load i64*, i64** %77, align 8, !tbaa !19
  %79 = getelementptr inbounds i64, i64* %78, i64 %11
  store i64* %79, i64** %76, align 8, !tbaa !22
  br label %80

; <label>:80:                                     ; preds = %2, %75
  ret %"class.std::vector"* %0
}

; Function Attrs: uwtable
define linkonce_odr void @_ZNSt6vectorImSaImEE17_M_default_appendEm(%"class.std::vector"*, i64) local_unnamed_addr #7 comdat align 2 personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*) {
  %3 = icmp eq i64 %1, 0
  br i1 %3, label %71, label %4

; <label>:4:                                      ; preds = %2
  %5 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 2
  %6 = bitcast i64** %5 to i64*
  %7 = load i64, i64* %6, align 8, !tbaa !28
  %8 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 1
  %9 = load i64*, i64** %8, align 8, !tbaa !22
  %10 = ptrtoint i64* %9 to i64
  %11 = sub i64 %7, %10
  %12 = ashr exact i64 %11, 3
  %13 = icmp ult i64 %12, %1
  br i1 %13, label %18, label %14

; <label>:14:                                     ; preds = %4
  %15 = bitcast i64* %9 to i8*
  %16 = shl i64 %1, 3
  tail call void @llvm.memset.p0i8.i64(i8* %15, i8 0, i64 %16, i32 8, i1 false)
  %17 = getelementptr i64, i64* %9, i64 %1
  br label %68

; <label>:18:                                     ; preds = %4
  %19 = bitcast i64** %8 to i64*
  %20 = bitcast %"class.std::vector"* %0 to i64*
  %21 = load i64, i64* %20, align 8, !tbaa !19
  %22 = sub i64 %10, %21
  %23 = ashr exact i64 %22, 3
  %24 = sub nsw i64 2305843009213693951, %23
  %25 = icmp ult i64 %24, %1
  br i1 %25, label %26, label %27

; <label>:26:                                     ; preds = %18
  tail call void @_ZSt20__throw_length_errorPKc(i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.13, i64 0, i64 0)) #16
  unreachable

; <label>:27:                                     ; preds = %18
  %28 = inttoptr i64 %21 to i64*
  %29 = icmp ult i64 %23, %1
  %30 = select i1 %29, i64 %1, i64 %23
  %31 = add i64 %30, %23
  %32 = icmp ult i64 %31, %23
  %33 = icmp ugt i64 %31, 2305843009213693951
  %34 = or i1 %32, %33
  %35 = select i1 %34, i64 2305843009213693951, i64 %31
  %36 = icmp eq i64 %35, 0
  br i1 %36, label %47, label %37

; <label>:37:                                     ; preds = %27
  %38 = icmp ugt i64 %35, 2305843009213693951
  br i1 %38, label %39, label %40

; <label>:39:                                     ; preds = %37
  tail call void @_ZSt17__throw_bad_allocv() #16
  unreachable

; <label>:40:                                     ; preds = %37
  %41 = shl i64 %35, 3
  %42 = tail call i8* @_Znwm(i64 %41)
  %43 = bitcast i8* %42 to i64*
  %44 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %45 = load i64*, i64** %44, align 8, !tbaa !19
  %46 = load i64, i64* %19, align 8, !tbaa !22
  br label %47

; <label>:47:                                     ; preds = %27, %40
  %48 = phi i64 [ %46, %40 ], [ %10, %27 ]
  %49 = phi i64* [ %45, %40 ], [ %28, %27 ]
  %50 = phi i8* [ %42, %40 ], [ null, %27 ]
  %51 = phi i64* [ %43, %40 ], [ null, %27 ]
  %52 = getelementptr inbounds i64, i64* %51, i64 %23
  %53 = bitcast i64* %52 to i8*
  %54 = shl i64 %1, 3
  tail call void @llvm.memset.p0i8.i64(i8* %53, i8 0, i64 %54, i32 8, i1 false)
  %55 = ptrtoint i64* %49 to i64
  %56 = sub i64 %48, %55
  %57 = icmp eq i64 %56, 0
  br i1 %57, label %60, label %58

; <label>:58:                                     ; preds = %47
  %59 = bitcast i64* %49 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* %50, i8* %59, i64 %56, i32 8, i1 false) #2
  br label %60

; <label>:60:                                     ; preds = %58, %47
  %61 = icmp eq i64* %49, null
  br i1 %61, label %64, label %62

; <label>:62:                                     ; preds = %60
  %63 = bitcast i64* %49 to i8*
  tail call void @_ZdlPv(i8* %63) #2
  br label %64

; <label>:64:                                     ; preds = %60, %62
  %65 = bitcast %"class.std::vector"* %0 to i8**
  store i8* %50, i8** %65, align 8, !tbaa !19
  %66 = getelementptr inbounds i64, i64* %52, i64 %1
  store i64* %66, i64** %8, align 8, !tbaa !22
  %67 = getelementptr inbounds i64, i64* %51, i64 %35
  br label %68

; <label>:68:                                     ; preds = %64, %14
  %69 = phi i64** [ %8, %14 ], [ %5, %64 ]
  %70 = phi i64* [ %17, %14 ], [ %67, %64 ]
  store i64* %70, i64** %69, align 8, !tbaa !23
  br label %71

; <label>:71:                                     ; preds = %68, %2
  ret void
}

; Function Attrs: uwtable
define internal void @_GLOBAL__sub_I_sexplore.cpp() #7 section ".text.startup" {
  tail call void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"* nonnull @_ZStL8__ioinit)
  %1 = tail call i32 @__cxa_atexit(void (i8*)* bitcast (void (%"class.std::ios_base::Init"*)* @_ZNSt8ios_base4InitD1Ev to void (i8*)*), i8* getelementptr inbounds (%"class.std::ios_base::Init", %"class.std::ios_base::Init"* @_ZStL8__ioinit, i64 0, i32 0), i8* nonnull @__dso_handle) #2
  ret void
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1) #5

attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }
attributes #3 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { readonly uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { argmemonly nounwind }
attributes #6 = { norecurse nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { inlinehint norecurse uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { inlinehint norecurse nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #10 = { norecurse uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #11 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #12 = { nobuiltin "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #13 = { nobuiltin nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #14 = { inlinehint uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #15 = { nounwind readnone speculatable }
attributes #16 = { noreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!2 = !{!3, !3, i64 0}
!3 = !{!"long", !4, i64 0}
!4 = !{!"omnipotent char", !5, i64 0}
!5 = !{!"Simple C++ TBAA"}
!6 = !{!7, !7, i64 0}
!7 = !{!"vtable pointer", !5, i64 0}
!8 = !{!9, !10, i64 240}
!9 = !{!"_ZTSSt9basic_iosIcSt11char_traitsIcEE", !10, i64 216, !4, i64 224, !11, i64 225, !10, i64 232, !10, i64 240, !10, i64 248, !10, i64 256}
!10 = !{!"any pointer", !4, i64 0}
!11 = !{!"bool", !4, i64 0}
!12 = !{!13, !4, i64 56}
!13 = !{!"_ZTSSt5ctypeIcE", !10, i64 16, !11, i64 24, !10, i64 32, !10, i64 40, !10, i64 48, !4, i64 56, !4, i64 57, !4, i64 313, !4, i64 569}
!14 = !{!4, !4, i64 0}
!15 = !{!16, !10, i64 0}
!16 = !{!"_ZTSNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE12_Alloc_hiderE", !10, i64 0}
!17 = !{!18, !3, i64 8}
!18 = !{!"_ZTSNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEE", !16, i64 0, !3, i64 8, !4, i64 16}
!19 = !{!20, !10, i64 0}
!20 = !{!"_ZTSSt12_Vector_baseImSaImEE", !21, i64 0}
!21 = !{!"_ZTSNSt12_Vector_baseImSaImEE12_Vector_implE", !10, i64 0, !10, i64 8, !10, i64 16}
!22 = !{!20, !10, i64 8}
!23 = !{!10, !10, i64 0}
!24 = !{i64 0, i64 65}
!25 = !{!26}
!26 = distinct !{!26, !27, !"_ZN13Int_Generator6sortedEm: argument 0"}
!27 = distinct !{!27, !"_ZN13Int_Generator6sortedEm"}
!28 = !{!20, !10, i64 16}
!29 = !{!30}
!30 = distinct !{!30, !31, !"_ZN13Int_Generator14reverse_sortedEm: argument 0"}
!31 = distinct !{!31, !"_ZN13Int_Generator14reverse_sortedEm"}
!32 = !{!18, !10, i64 0}
!33 = !{!34}
!34 = distinct !{!34, !35, !"_ZN13Int_Generator6sortedEm: argument 0"}
!35 = distinct !{!35, !"_ZN13Int_Generator6sortedEm"}
!36 = !{!37}
!37 = distinct !{!37, !38, !"_ZN13Int_Generator14reverse_sortedEm: argument 0"}
!38 = distinct !{!38, !"_ZN13Int_Generator14reverse_sortedEm"}
!39 = !{!40, !42, i64 32}
!40 = !{!"_ZTSSt8ios_base", !3, i64 8, !3, i64 16, !41, i64 24, !42, i64 28, !42, i64 32, !10, i64 40, !43, i64 48, !4, i64 64, !44, i64 192, !10, i64 200, !45, i64 208}
!41 = !{!"_ZTSSt13_Ios_Fmtflags", !4, i64 0}
!42 = !{!"_ZTSSt12_Ios_Iostate", !4, i64 0}
!43 = !{!"_ZTSNSt8ios_base6_WordsE", !10, i64 0, !3, i64 8}
!44 = !{!"int", !4, i64 0}
!45 = !{!"_ZTSSt6locale", !10, i64 0}
!46 = distinct !{!46, !47}
!47 = !{!"llvm.loop.unroll.disable"}
!48 = distinct !{!48, !47}
