; ModuleID = 'sexplore.ll'
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

; Function Attrs: norecurse nounwind readonly uwtable
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

; Function Attrs: nounwind uwtable
define void @_Z10xintrosortPmm(i64*, i64) local_unnamed_addr #3 {
  %3 = icmp ugt i64 %1, 16
  br i1 %3, label %.preheader39, label %.loopexit2

.preheader39:                                     ; preds = %2
  br label %4

; <label>:4:                                      ; preds = %.preheader39, %58
  %5 = phi i64 [ %65, %58 ], [ %1, %.preheader39 ]
  %6 = phi i64* [ %47, %58 ], [ %0, %.preheader39 ]
  %7 = lshr i64 %5, 1
  %8 = getelementptr inbounds i64, i64* %6, i64 %7
  %9 = getelementptr inbounds i64, i64* %6, i64 1
  %10 = getelementptr inbounds i64, i64* %6, i64 %5
  %11 = getelementptr inbounds i64, i64* %10, i64 -1
  %12 = load i64, i64* %9, align 8, !tbaa !2
  %13 = load i64, i64* %8, align 8, !tbaa !2
  %14 = icmp ult i64 %12, %13
  %15 = load i64, i64* %11, align 8, !tbaa !2
  br i1 %14, label %16, label %25

; <label>:16:                                     ; preds = %4
  %17 = icmp ult i64 %13, %15
  br i1 %17, label %18, label %20

; <label>:18:                                     ; preds = %16
  %19 = load i64, i64* %6, align 8, !tbaa !2
  store i64 %13, i64* %6, align 8, !tbaa !2
  store i64 %19, i64* %8, align 8, !tbaa !2
  br label %34

; <label>:20:                                     ; preds = %16
  %21 = icmp ult i64 %12, %15
  %22 = load i64, i64* %6, align 8, !tbaa !2
  br i1 %21, label %23, label %24

; <label>:23:                                     ; preds = %20
  store i64 %15, i64* %6, align 8, !tbaa !2
  store i64 %22, i64* %11, align 8, !tbaa !2
  br label %34

; <label>:24:                                     ; preds = %20
  store i64 %12, i64* %6, align 8, !tbaa !2
  store i64 %22, i64* %9, align 8, !tbaa !2
  br label %34

; <label>:25:                                     ; preds = %4
  %26 = icmp ult i64 %12, %15
  br i1 %26, label %27, label %29

; <label>:27:                                     ; preds = %25
  %28 = load i64, i64* %6, align 8, !tbaa !2
  store i64 %12, i64* %6, align 8, !tbaa !2
  store i64 %28, i64* %9, align 8, !tbaa !2
  br label %34

; <label>:29:                                     ; preds = %25
  %30 = icmp ult i64 %13, %15
  %31 = load i64, i64* %6, align 8, !tbaa !2
  br i1 %30, label %32, label %33

; <label>:32:                                     ; preds = %29
  store i64 %15, i64* %6, align 8, !tbaa !2
  store i64 %31, i64* %11, align 8, !tbaa !2
  br label %34

; <label>:33:                                     ; preds = %29
  store i64 %13, i64* %6, align 8, !tbaa !2
  store i64 %31, i64* %8, align 8, !tbaa !2
  br label %34

; <label>:34:                                     ; preds = %33, %32, %27, %24, %23, %18
  %35 = add i64 %5, -1
  %36 = load i64, i64* %6, align 8, !tbaa !2
  br label %37

; <label>:37:                                     ; preds = %56, %34
  %38 = phi i64 [ 0, %34 ], [ %45, %56 ]
  %39 = phi i64 [ %35, %34 ], [ %50, %56 ]
  br label %40

; <label>:40:                                     ; preds = %40, %37
  %41 = phi i64 [ %38, %37 ], [ %45, %40 ]
  %42 = getelementptr inbounds i64, i64* %9, i64 %41
  %43 = load i64, i64* %42, align 8, !tbaa !2
  %44 = icmp ult i64 %43, %36
  %45 = add i64 %41, 1
  br i1 %44, label %40, label %46

; <label>:46:                                     ; preds = %40
  %47 = getelementptr inbounds i64, i64* %9, i64 %41
  br label %48

; <label>:48:                                     ; preds = %48, %46
  %49 = phi i64 [ %39, %46 ], [ %50, %48 ]
  %50 = add i64 %49, -1
  %51 = getelementptr inbounds i64, i64* %6, i64 %49
  %52 = load i64, i64* %51, align 8, !tbaa !2
  %53 = icmp ugt i64 %52, %36
  br i1 %53, label %48, label %54

; <label>:54:                                     ; preds = %48
  %55 = icmp ult i64 %41, %50
  br i1 %55, label %56, label %58

; <label>:56:                                     ; preds = %54
  %57 = getelementptr inbounds i64, i64* %6, i64 %49
  store i64 %52, i64* %47, align 8, !tbaa !2
  store i64 %43, i64* %57, align 8, !tbaa !2
  br label %37

; <label>:58:                                     ; preds = %54
  %59 = ptrtoint i64* %47 to i64
  %60 = ptrtoint i64* %6 to i64
  %61 = sub i64 %59, %60
  %62 = ashr exact i64 %61, 3
  tail call void @_Z10xintrosortPmm(i64* nonnull %6, i64 %62)
  %63 = ptrtoint i64* %10 to i64
  %64 = sub i64 %63, %59
  %65 = ashr exact i64 %64, 3
  %66 = icmp ugt i64 %65, 16
  br i1 %66, label %4, label %.loopexit2

.loopexit2:                                       ; preds = %58, %2
  %67 = phi i64* [ %0, %2 ], [ %47, %58 ]
  %68 = phi i64 [ %1, %2 ], [ %65, %58 ]
  %69 = getelementptr inbounds i64, i64* %67, i64 %68
  %70 = icmp ult i64 %68, 2
  br i1 %70, label %.loopexit1, label %71

; <label>:71:                                     ; preds = %.loopexit2
  %72 = getelementptr inbounds i64, i64* %67, i64 1
  %73 = ptrtoint i64* %67 to i64
  %74 = bitcast i64* %67 to i8*
  br label %75

; <label>:75:                                     ; preds = %.loopexit, %71
  %76 = phi i64* [ %72, %71 ], [ %102, %.loopexit ]
  %77 = phi i64* [ %67, %71 ], [ %76, %.loopexit ]
  %78 = load i64, i64* %76, align 8, !tbaa !2
  %79 = load i64, i64* %67, align 8, !tbaa !2
  %80 = icmp ult i64 %78, %79
  br i1 %80, label %81, label %91

; <label>:81:                                     ; preds = %75
  %82 = ptrtoint i64* %76 to i64
  %83 = sub i64 %82, %73
  %84 = icmp eq i64 %83, 0
  br i1 %84, label %.loopexit, label %85

; <label>:85:                                     ; preds = %81
  %86 = getelementptr inbounds i64, i64* %77, i64 2
  %87 = ashr exact i64 %83, 3
  %88 = sub nsw i64 0, %87
  %89 = getelementptr inbounds i64, i64* %86, i64 %88
  %90 = bitcast i64* %89 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %90, i8* nonnull %74, i64 %83, i32 8, i1 false) #2
  br label %.loopexit

; <label>:91:                                     ; preds = %75
  %92 = load i64, i64* %77, align 8, !tbaa !2
  %93 = icmp ult i64 %78, %92
  br i1 %93, label %.preheader, label %.loopexit

.preheader:                                       ; preds = %91
  br label %94

; <label>:94:                                     ; preds = %.preheader, %94
  %95 = phi i64 [ %99, %94 ], [ %92, %.preheader ]
  %96 = phi i64* [ %98, %94 ], [ %77, %.preheader ]
  %97 = phi i64* [ %96, %94 ], [ %76, %.preheader ]
  store i64 %95, i64* %97, align 8, !tbaa !2
  %98 = getelementptr inbounds i64, i64* %96, i64 -1
  %99 = load i64, i64* %98, align 8, !tbaa !2
  %100 = icmp ult i64 %78, %99
  br i1 %100, label %94, label %.loopexit

.loopexit:                                        ; preds = %94, %91, %85, %81
  %101 = phi i64* [ %67, %85 ], [ %67, %81 ], [ %76, %91 ], [ %96, %94 ]
  store i64 %78, i64* %101, align 8, !tbaa !2
  %102 = getelementptr inbounds i64, i64* %76, i64 1
  %103 = icmp eq i64* %102, %69
  br i1 %103, label %.loopexit1, label %75

.loopexit1:                                       ; preds = %.loopexit, %.loopexit2
  ret void
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i32, i1) #5

; Function Attrs: uwtable
define void @_Z11pdqsort_recPmmmib(i64*, i64, i64, i32, i1 zeroext) local_unnamed_addr #7 {
  %6 = alloca %"struct.__gnu_cxx::__ops::_Iter_comp_iter", align 1
  %7 = sub i64 %1, %2
  %8 = icmp ult i64 %7, 24
  br i1 %8, label %9, label %107

; <label>:9:                                      ; preds = %5
  %10 = getelementptr inbounds i64, i64* %0, i64 %1
  %11 = getelementptr inbounds i64, i64* %0, i64 %2
  %12 = icmp eq i64 %1, %2
  br i1 %4, label %13, label %57

; <label>:13:                                     ; preds = %9
  br i1 %12, label %.loopexit, label %14

; <label>:14:                                     ; preds = %13
  %15 = getelementptr inbounds i64, i64* %10, i64 1
  %16 = icmp eq i64* %15, %11
  br i1 %16, label %.loopexit, label %17

; <label>:17:                                     ; preds = %14
  %18 = shl i64 %2, 3
  %19 = shl i64 %1, 3
  %20 = sub i64 -16, %19
  %21 = add i64 %20, %18
  %22 = and i64 %21, 8
  %23 = icmp eq i64 %22, 0
  br i1 %23, label %24, label %30

; <label>:24:                                     ; preds = %17
  %25 = load i64, i64* %15, align 8, !tbaa !2
  %26 = load i64, i64* %10, align 8, !tbaa !2
  %27 = icmp ult i64 %25, %26
  br i1 %27, label %.preheader152, label %28

.preheader152:                                    ; preds = %24
  store i64 %26, i64* %15, align 8, !tbaa !2
  store i64 %25, i64* %10, align 8, !tbaa !2
  br label %28

; <label>:28:                                     ; preds = %.preheader152, %24
  %29 = getelementptr inbounds i64, i64* %15, i64 1
  br label %30

; <label>:30:                                     ; preds = %28, %17
  %31 = phi i64* [ %15, %17 ], [ %29, %28 ]
  %32 = phi i64* [ %10, %17 ], [ %15, %28 ]
  %33 = icmp eq i64 %21, 0
  br i1 %33, label %.loopexit, label %.preheader151

.preheader151:                                    ; preds = %30
  br label %34

; <label>:34:                                     ; preds = %.preheader151, %397
  %35 = phi i64* [ %398, %397 ], [ %31, %.preheader151 ]
  %36 = phi i64* [ %54, %397 ], [ %32, %.preheader151 ]
  %37 = load i64, i64* %35, align 8, !tbaa !2
  %38 = load i64, i64* %36, align 8, !tbaa !2
  %39 = icmp ult i64 %37, %38
  br i1 %39, label %.preheader150, label %52

.preheader150:                                    ; preds = %34
  br label %40

; <label>:40:                                     ; preds = %.preheader150, %46
  %41 = phi i64 [ %48, %46 ], [ %38, %.preheader150 ]
  %42 = phi i64* [ %44, %46 ], [ %35, %.preheader150 ]
  %43 = phi i64* [ %47, %46 ], [ %36, %.preheader150 ]
  %44 = getelementptr inbounds i64, i64* %42, i64 -1
  store i64 %41, i64* %42, align 8, !tbaa !2
  %45 = icmp eq i64* %44, %10
  br i1 %45, label %50, label %46

; <label>:46:                                     ; preds = %40
  %47 = getelementptr inbounds i64, i64* %43, i64 -1
  %48 = load i64, i64* %47, align 8, !tbaa !2
  %49 = icmp ult i64 %37, %48
  br i1 %49, label %40, label %50

; <label>:50:                                     ; preds = %46, %40
  %51 = phi i64* [ %10, %40 ], [ %44, %46 ]
  store i64 %37, i64* %51, align 8, !tbaa !2
  %.pre79 = load i64, i64* %35, align 8, !tbaa !2
  br label %52

; <label>:52:                                     ; preds = %50, %34
  %53 = phi i64 [ %.pre79, %50 ], [ %37, %34 ]
  %54 = getelementptr inbounds i64, i64* %35, i64 1
  %55 = load i64, i64* %54, align 8, !tbaa !2
  %56 = icmp ult i64 %55, %53
  br i1 %56, label %.preheader, label %397

.preheader:                                       ; preds = %52
  br label %385

; <label>:57:                                     ; preds = %9
  br i1 %12, label %.loopexit, label %58

; <label>:58:                                     ; preds = %57
  %59 = getelementptr inbounds i64, i64* %10, i64 1
  %60 = icmp eq i64* %59, %11
  br i1 %60, label %.loopexit, label %61

; <label>:61:                                     ; preds = %58
  %62 = shl i64 %2, 3
  %63 = shl i64 %1, 3
  %64 = sub i64 -16, %63
  %65 = add i64 %64, %62
  %66 = and i64 %65, 8
  %67 = icmp eq i64 %66, 0
  br i1 %67, label %68, label %83

; <label>:68:                                     ; preds = %61
  %69 = load i64, i64* %59, align 8, !tbaa !2
  %70 = load i64, i64* %10, align 8, !tbaa !2
  %71 = icmp ult i64 %69, %70
  br i1 %71, label %.preheader157, label %81

.preheader157:                                    ; preds = %68
  br label %72

; <label>:72:                                     ; preds = %.preheader157, %72
  %73 = phi i64 [ %78, %72 ], [ %70, %.preheader157 ]
  %74 = phi i64* [ %76, %72 ], [ %59, %.preheader157 ]
  %75 = phi i64* [ %77, %72 ], [ %10, %.preheader157 ]
  %76 = getelementptr inbounds i64, i64* %74, i64 -1
  store i64 %73, i64* %74, align 8, !tbaa !2
  %77 = getelementptr inbounds i64, i64* %75, i64 -1
  %78 = load i64, i64* %77, align 8, !tbaa !2
  %79 = icmp ult i64 %69, %78
  br i1 %79, label %72, label %80

; <label>:80:                                     ; preds = %72
  store i64 %69, i64* %76, align 8, !tbaa !2
  br label %81

; <label>:81:                                     ; preds = %80, %68
  %82 = getelementptr inbounds i64, i64* %59, i64 1
  br label %83

; <label>:83:                                     ; preds = %81, %61
  %84 = phi i64* [ %59, %61 ], [ %82, %81 ]
  %85 = phi i64* [ %10, %61 ], [ %59, %81 ]
  %86 = icmp eq i64 %65, 0
  br i1 %86, label %.loopexit, label %.preheader155

.preheader155:                                    ; preds = %83
  br label %87

; <label>:87:                                     ; preds = %.preheader155, %409
  %88 = phi i64* [ %410, %409 ], [ %84, %.preheader155 ]
  %89 = phi i64* [ %104, %409 ], [ %85, %.preheader155 ]
  %90 = load i64, i64* %88, align 8, !tbaa !2
  %91 = load i64, i64* %89, align 8, !tbaa !2
  %92 = icmp ult i64 %90, %91
  br i1 %92, label %.preheader154, label %102

.preheader154:                                    ; preds = %87
  br label %93

; <label>:93:                                     ; preds = %.preheader154, %93
  %94 = phi i64 [ %99, %93 ], [ %91, %.preheader154 ]
  %95 = phi i64* [ %97, %93 ], [ %88, %.preheader154 ]
  %96 = phi i64* [ %98, %93 ], [ %89, %.preheader154 ]
  %97 = getelementptr inbounds i64, i64* %95, i64 -1
  store i64 %94, i64* %95, align 8, !tbaa !2
  %98 = getelementptr inbounds i64, i64* %96, i64 -1
  %99 = load i64, i64* %98, align 8, !tbaa !2
  %100 = icmp ult i64 %90, %99
  br i1 %100, label %93, label %101

; <label>:101:                                    ; preds = %93
  store i64 %90, i64* %97, align 8, !tbaa !2
  %.pre = load i64, i64* %88, align 8, !tbaa !2
  br label %102

; <label>:102:                                    ; preds = %101, %87
  %103 = phi i64 [ %.pre, %101 ], [ %90, %87 ]
  %104 = getelementptr inbounds i64, i64* %88, i64 1
  %105 = load i64, i64* %104, align 8, !tbaa !2
  %106 = icmp ult i64 %105, %103
  br i1 %106, label %.preheader153, label %409

.preheader153:                                    ; preds = %102
  br label %400

; <label>:107:                                    ; preds = %5
  tail call void @_Z19move_pivot_to_frontPmmm(i64* %0, i64 %1, i64 %2)
  br i1 %4, label %108, label %111

; <label>:108:                                    ; preds = %107
  %109 = getelementptr inbounds i64, i64* %0, i64 %1
  %110 = load i64, i64* %109, align 8, !tbaa !2
  br label %168

; <label>:111:                                    ; preds = %107
  %112 = add i64 %1, -1
  %113 = getelementptr inbounds i64, i64* %0, i64 %112
  %114 = getelementptr inbounds i64, i64* %0, i64 %1
  %115 = load i64, i64* %113, align 8, !tbaa !2
  %116 = load i64, i64* %114, align 8, !tbaa !2
  %117 = icmp ult i64 %115, %116
  br i1 %117, label %168, label %118

; <label>:118:                                    ; preds = %111
  %119 = getelementptr inbounds i64, i64* %0, i64 %2
  br label %120

; <label>:120:                                    ; preds = %120, %118
  %121 = phi i64* [ %119, %118 ], [ %122, %120 ]
  %122 = getelementptr inbounds i64, i64* %121, i64 -1
  %123 = load i64, i64* %122, align 8, !tbaa !2
  %124 = icmp ult i64 %116, %123
  br i1 %124, label %120, label %125

; <label>:125:                                    ; preds = %120
  %126 = icmp eq i64* %121, %119
  br i1 %126, label %127, label %.preheader172

.preheader172:                                    ; preds = %125
  br label %136

; <label>:127:                                    ; preds = %125
  %128 = icmp ugt i64* %122, %114
  br i1 %128, label %.preheader171, label %.loopexit15

.preheader171:                                    ; preds = %127
  br label %129

; <label>:129:                                    ; preds = %.preheader171, %129
  %130 = phi i64* [ %131, %129 ], [ %114, %.preheader171 ]
  %131 = getelementptr inbounds i64, i64* %130, i64 1
  %132 = load i64, i64* %131, align 8, !tbaa !2
  %133 = icmp uge i64 %116, %132
  %134 = icmp ult i64* %131, %122
  %135 = and i1 %133, %134
  br i1 %135, label %129, label %.loopexit15

; <label>:136:                                    ; preds = %.preheader172, %136
  %137 = phi i64* [ %138, %136 ], [ %114, %.preheader172 ]
  %138 = getelementptr inbounds i64, i64* %137, i64 1
  %139 = load i64, i64* %138, align 8, !tbaa !2
  %140 = icmp ult i64 %116, %139
  br i1 %140, label %.loopexit15, label %136

.loopexit15:                                      ; preds = %136, %129, %127
  %141 = phi i64 [ %116, %127 ], [ %132, %129 ], [ %139, %136 ]
  %142 = phi i64* [ %114, %127 ], [ %131, %129 ], [ %138, %136 ]
  %143 = icmp ult i64* %142, %122
  br i1 %143, label %.preheader170, label %.loopexit14

.preheader170:                                    ; preds = %.loopexit15
  br label %144

; <label>:144:                                    ; preds = %.preheader170, %159
  %145 = phi i64 [ %152, %159 ], [ %123, %.preheader170 ]
  %146 = phi i64 [ %157, %159 ], [ %141, %.preheader170 ]
  %147 = phi i64* [ %156, %159 ], [ %142, %.preheader170 ]
  %148 = phi i64* [ %151, %159 ], [ %122, %.preheader170 ]
  store i64 %145, i64* %147, align 8, !tbaa !2
  store i64 %146, i64* %148, align 8, !tbaa !2
  br label %149

; <label>:149:                                    ; preds = %149, %144
  %150 = phi i64* [ %148, %144 ], [ %151, %149 ]
  %151 = getelementptr inbounds i64, i64* %150, i64 -1
  %152 = load i64, i64* %151, align 8, !tbaa !2
  %153 = icmp ult i64 %116, %152
  br i1 %153, label %149, label %.preheader169

.preheader169:                                    ; preds = %149
  br label %154

; <label>:154:                                    ; preds = %.preheader169, %154
  %155 = phi i64* [ %156, %154 ], [ %147, %.preheader169 ]
  %156 = getelementptr inbounds i64, i64* %155, i64 1
  %157 = load i64, i64* %156, align 8, !tbaa !2
  %158 = icmp ult i64 %116, %157
  br i1 %158, label %159, label %154

; <label>:159:                                    ; preds = %154
  %160 = icmp ult i64* %156, %151
  br i1 %160, label %144, label %.loopexit14

.loopexit14:                                      ; preds = %159, %.loopexit15
  %161 = phi i64 [ %123, %.loopexit15 ], [ %152, %159 ]
  %162 = phi i64* [ %122, %.loopexit15 ], [ %151, %159 ]
  store i64 %161, i64* %114, align 8, !tbaa !2
  store i64 %116, i64* %162, align 8, !tbaa !2
  %163 = getelementptr inbounds i64, i64* %162, i64 1
  %164 = ptrtoint i64* %163 to i64
  %165 = ptrtoint i64* %0 to i64
  %166 = sub i64 %164, %165
  %167 = ashr exact i64 %166, 3
  tail call void @_Z11pdqsort_recPmmmib(i64* %0, i64 %167, i64 %2, i32 %3, i1 zeroext false)
  br label %.loopexit

; <label>:168:                                    ; preds = %111, %108
  %169 = phi i64* [ %114, %111 ], [ %109, %108 ]
  %170 = phi i64 [ %116, %111 ], [ %110, %108 ]
  %171 = getelementptr inbounds i64, i64* %0, i64 %1
  br label %172

; <label>:172:                                    ; preds = %172, %168
  %173 = phi i64 [ 0, %168 ], [ %174, %172 ]
  %174 = add nuw nsw i64 %173, 1
  %175 = getelementptr inbounds i64, i64* %171, i64 %174
  %176 = load i64, i64* %175, align 8, !tbaa !2
  %177 = icmp ult i64 %176, %170
  br i1 %177, label %172, label %178

; <label>:178:                                    ; preds = %172
  %179 = getelementptr inbounds i64, i64* %171, i64 %174
  %180 = getelementptr inbounds i64, i64* %0, i64 %2
  %181 = icmp eq i64 %173, 0
  br i1 %181, label %182, label %.preheader167

.preheader167:                                    ; preds = %178
  br label %191

; <label>:182:                                    ; preds = %178
  %183 = icmp ult i64* %179, %180
  br i1 %183, label %.preheader166, label %.loopexit12

.preheader166:                                    ; preds = %182
  br label %184

; <label>:184:                                    ; preds = %.preheader166, %184
  %185 = phi i64* [ %186, %184 ], [ %180, %.preheader166 ]
  %186 = getelementptr inbounds i64, i64* %185, i64 -1
  %187 = load i64, i64* %186, align 8, !tbaa !2
  %188 = icmp uge i64 %187, %170
  %189 = icmp ult i64* %179, %186
  %190 = and i1 %188, %189
  br i1 %190, label %184, label %.loopexit12

; <label>:191:                                    ; preds = %.preheader167, %191
  %192 = phi i64* [ %193, %191 ], [ %180, %.preheader167 ]
  %193 = getelementptr inbounds i64, i64* %192, i64 -1
  %194 = load i64, i64* %193, align 8, !tbaa !2
  %195 = icmp ult i64 %194, %170
  br i1 %195, label %.loopexit12, label %191

.loopexit12:                                      ; preds = %191, %184, %182
  %196 = phi i64* [ %180, %182 ], [ %186, %184 ], [ %193, %191 ]
  %197 = icmp ult i64* %179, %196
  br i1 %197, label %198, label %.loopexit11

; <label>:198:                                    ; preds = %.loopexit12
  %199 = load i64, i64* %196, align 8, !tbaa !2
  %200 = getelementptr inbounds i64, i64* %0, i64 %1
  %201 = getelementptr inbounds i64, i64* %0, i64 %1
  br label %202

; <label>:202:                                    ; preds = %221, %198
  %203 = phi i64 [ %199, %198 ], [ %219, %221 ]
  %204 = phi i64 [ %176, %198 ], [ %212, %221 ]
  %205 = phi i64* [ %196, %198 ], [ %218, %221 ]
  %206 = phi i64 [ %174, %198 ], [ %210, %221 ]
  %207 = getelementptr inbounds i64, i64* %200, i64 %206
  store i64 %203, i64* %207, align 8, !tbaa !2
  store i64 %204, i64* %205, align 8, !tbaa !2
  br label %208

; <label>:208:                                    ; preds = %208, %202
  %209 = phi i64 [ %206, %202 ], [ %210, %208 ]
  %210 = add nsw i64 %209, 1
  %211 = getelementptr inbounds i64, i64* %201, i64 %210
  %212 = load i64, i64* %211, align 8, !tbaa !2
  %213 = icmp ult i64 %212, %170
  br i1 %213, label %208, label %214

; <label>:214:                                    ; preds = %208
  %215 = getelementptr inbounds i64, i64* %201, i64 %210
  br label %216

; <label>:216:                                    ; preds = %216, %214
  %217 = phi i64* [ %205, %214 ], [ %218, %216 ]
  %218 = getelementptr inbounds i64, i64* %217, i64 -1
  %219 = load i64, i64* %218, align 8, !tbaa !2
  %220 = icmp ult i64 %219, %170
  br i1 %220, label %221, label %216

; <label>:221:                                    ; preds = %216
  %222 = icmp ult i64* %215, %218
  br i1 %222, label %202, label %.loopexit11

.loopexit11:                                      ; preds = %221, %.loopexit12
  %223 = phi i64 [ %173, %.loopexit12 ], [ %209, %221 ]
  %224 = getelementptr inbounds i64, i64* %0, i64 %1
  %225 = getelementptr inbounds i64, i64* %224, i64 %223
  %226 = load i64, i64* %225, align 8, !tbaa !2
  store i64 %226, i64* %169, align 8, !tbaa !2
  store i64 %170, i64* %225, align 8, !tbaa !2
  %227 = ptrtoint i64* %225 to i64
  %228 = ptrtoint i64* %0 to i64
  %229 = sub i64 %227, %228
  %230 = ashr exact i64 %229, 3
  %231 = tail call zeroext i1 @_Z7shufflePmmmm(i64* %0, i64 %1, i64 %2, i64 %230)
  br i1 %231, label %232, label %306

; <label>:232:                                    ; preds = %.loopexit11
  %233 = add nsw i32 %3, -1
  %234 = icmp eq i32 %233, 0
  br i1 %234, label %235, label %306

; <label>:235:                                    ; preds = %232
  %236 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_comp_iter", %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* %6, i64 0, i32 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %236) #2
  call void @_ZSt11__make_heapIPmN9__gnu_cxx5__ops15_Iter_comp_iterISt4lessImEEEEvT_S7_RT0_(i64* nonnull %169, i64* nonnull %180, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* nonnull dereferenceable(1) %6)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %236) #2
  %237 = ptrtoint i64* %180 to i64
  %238 = ptrtoint i64* %169 to i64
  %239 = sub i64 %237, %238
  %240 = icmp sgt i64 %239, 8
  br i1 %240, label %241, label %.loopexit

; <label>:241:                                    ; preds = %235
  %242 = getelementptr inbounds i64, i64* %0, i64 %1
  %243 = getelementptr inbounds i64, i64* %0, i64 %1
  %244 = getelementptr inbounds i64, i64* %0, i64 %1
  %245 = getelementptr inbounds i64, i64* %0, i64 %1
  %246 = getelementptr inbounds i64, i64* %0, i64 %1
  %247 = getelementptr inbounds i64, i64* %0, i64 %1
  %248 = getelementptr inbounds i64, i64* %0, i64 %1
  %249 = getelementptr inbounds i64, i64* %0, i64 %1
  %250 = getelementptr inbounds i64, i64* %0, i64 %1
  br label %251

; <label>:251:                                    ; preds = %.loopexit3, %241
  %252 = phi i64* [ %180, %241 ], [ %253, %.loopexit3 ]
  %253 = getelementptr inbounds i64, i64* %252, i64 -1
  %254 = load i64, i64* %253, align 8, !tbaa !2
  %255 = load i64, i64* %169, align 8, !tbaa !2
  store i64 %255, i64* %253, align 8, !tbaa !2
  %256 = ptrtoint i64* %253 to i64
  %257 = sub i64 %256, %238
  %258 = ashr exact i64 %257, 3
  %259 = add nsw i64 %258, -1
  %260 = sdiv i64 %259, 2
  %261 = icmp sgt i64 %257, 16
  br i1 %261, label %.preheader159, label %.loopexit4

.preheader159:                                    ; preds = %251
  br label %262

; <label>:262:                                    ; preds = %.preheader159, %262
  %263 = phi i64 [ %272, %262 ], [ 0, %.preheader159 ]
  %264 = shl i64 %263, 1
  %265 = add i64 %264, 2
  %266 = getelementptr inbounds i64, i64* %245, i64 %265
  %267 = or i64 %264, 1
  %268 = getelementptr inbounds i64, i64* %244, i64 %267
  %269 = load i64, i64* %266, align 8, !tbaa !2
  %270 = load i64, i64* %268, align 8, !tbaa !2
  %271 = icmp ult i64 %269, %270
  %272 = select i1 %271, i64 %267, i64 %265
  %273 = getelementptr inbounds i64, i64* %243, i64 %272
  %274 = load i64, i64* %273, align 8, !tbaa !2
  %275 = getelementptr inbounds i64, i64* %242, i64 %263
  store i64 %274, i64* %275, align 8, !tbaa !2
  %276 = icmp slt i64 %272, %260
  br i1 %276, label %262, label %.loopexit4

.loopexit4:                                       ; preds = %262, %251
  %277 = phi i64 [ 0, %251 ], [ %272, %262 ]
  %278 = and i64 %257, 8
  %279 = icmp eq i64 %278, 0
  br i1 %279, label %280, label %290

; <label>:280:                                    ; preds = %.loopexit4
  %281 = add nsw i64 %258, -2
  %282 = sdiv i64 %281, 2
  %283 = icmp eq i64 %277, %282
  br i1 %283, label %284, label %290

; <label>:284:                                    ; preds = %280
  %285 = shl i64 %277, 1
  %286 = or i64 %285, 1
  %287 = getelementptr inbounds i64, i64* %247, i64 %286
  %288 = load i64, i64* %287, align 8, !tbaa !2
  %289 = getelementptr inbounds i64, i64* %246, i64 %277
  store i64 %288, i64* %289, align 8, !tbaa !2
  br label %290

; <label>:290:                                    ; preds = %284, %280, %.loopexit4
  %291 = phi i64 [ %286, %284 ], [ %277, %280 ], [ %277, %.loopexit4 ]
  %292 = icmp sgt i64 %291, 0
  br i1 %292, label %.preheader158, label %.loopexit3

.preheader158:                                    ; preds = %290
  br label %293

; <label>:293:                                    ; preds = %.preheader158, %300
  %294 = phi i64 [ %296, %300 ], [ %291, %.preheader158 ]
  %295 = add nsw i64 %294, -1
  %296 = sdiv i64 %295, 2
  %297 = getelementptr inbounds i64, i64* %249, i64 %296
  %298 = load i64, i64* %297, align 8, !tbaa !2
  %299 = icmp ult i64 %298, %254
  br i1 %299, label %300, label %.loopexit3

; <label>:300:                                    ; preds = %293
  %301 = getelementptr inbounds i64, i64* %248, i64 %294
  store i64 %298, i64* %301, align 8, !tbaa !2
  %302 = icmp sgt i64 %294, 2
  br i1 %302, label %293, label %.loopexit3

.loopexit3:                                       ; preds = %300, %293, %290
  %303 = phi i64 [ %291, %290 ], [ %296, %300 ], [ %294, %293 ]
  %304 = getelementptr inbounds i64, i64* %250, i64 %303
  store i64 %254, i64* %304, align 8, !tbaa !2
  %305 = icmp sgt i64 %257, 8
  br i1 %305, label %251, label %.loopexit

; <label>:306:                                    ; preds = %232, %.loopexit11
  %307 = phi i32 [ %233, %232 ], [ %3, %.loopexit11 ]
  br i1 %197, label %.loopexit7, label %308

; <label>:308:                                    ; preds = %306
  %309 = icmp ult i64 %223, 2
  br i1 %309, label %.loopexit10, label %310

; <label>:310:                                    ; preds = %308
  %311 = getelementptr inbounds i64, i64* %0, i64 %1
  %312 = getelementptr inbounds i64, i64* %311, i64 1
  br label %313

; <label>:313:                                    ; preds = %340, %310
  %314 = phi i64* [ %312, %310 ], [ %342, %340 ]
  %315 = phi i64* [ %169, %310 ], [ %314, %340 ]
  %316 = phi i32 [ 0, %310 ], [ %341, %340 ]
  %317 = icmp sgt i32 %316, 8
  br i1 %317, label %.loopexit7, label %318

; <label>:318:                                    ; preds = %313
  %319 = load i64, i64* %314, align 8, !tbaa !2
  %320 = load i64, i64* %315, align 8, !tbaa !2
  %321 = icmp ult i64 %319, %320
  br i1 %321, label %.preheader164, label %340

.preheader164:                                    ; preds = %318
  br label %322

; <label>:322:                                    ; preds = %.preheader164, %328
  %323 = phi i64 [ %330, %328 ], [ %320, %.preheader164 ]
  %324 = phi i64* [ %326, %328 ], [ %314, %.preheader164 ]
  %325 = phi i64* [ %329, %328 ], [ %315, %.preheader164 ]
  %326 = getelementptr inbounds i64, i64* %324, i64 -1
  store i64 %323, i64* %324, align 8, !tbaa !2
  %327 = icmp eq i64* %326, %169
  br i1 %327, label %332, label %328

; <label>:328:                                    ; preds = %322
  %329 = getelementptr inbounds i64, i64* %325, i64 -1
  %330 = load i64, i64* %329, align 8, !tbaa !2
  %331 = icmp ult i64 %319, %330
  br i1 %331, label %322, label %332

; <label>:332:                                    ; preds = %328, %322
  %333 = phi i64* [ %169, %322 ], [ %326, %328 ]
  store i64 %319, i64* %333, align 8, !tbaa !2
  %334 = ptrtoint i64* %314 to i64
  %335 = ptrtoint i64* %333 to i64
  %336 = sub i64 %334, %335
  %337 = lshr exact i64 %336, 3
  %338 = trunc i64 %337 to i32
  %339 = add i32 %316, %338
  br label %340

; <label>:340:                                    ; preds = %332, %318
  %341 = phi i32 [ %339, %332 ], [ %316, %318 ]
  %342 = getelementptr inbounds i64, i64* %314, i64 1
  %343 = icmp eq i64* %342, %225
  br i1 %343, label %.loopexit10, label %313

.loopexit10:                                      ; preds = %340, %308
  %344 = getelementptr inbounds i64, i64* %225, i64 1
  %345 = icmp eq i64* %344, %180
  %346 = getelementptr inbounds i64, i64* %225, i64 2
  %347 = icmp eq i64* %346, %180
  %348 = or i1 %345, %347
  br i1 %348, label %.loopexit, label %.preheader162

.preheader162:                                    ; preds = %.loopexit10
  br label %349

; <label>:349:                                    ; preds = %.preheader162, %379
  %350 = phi i64 [ %381, %379 ], [ 2, %.preheader162 ]
  %351 = phi i64* [ %353, %379 ], [ %344, %.preheader162 ]
  %352 = phi i32 [ %380, %379 ], [ 0, %.preheader162 ]
  %353 = getelementptr inbounds i64, i64* %225, i64 %350
  %354 = icmp sgt i32 %352, 8
  br i1 %354, label %.loopexit7, label %355

; <label>:355:                                    ; preds = %349
  %356 = load i64, i64* %353, align 8, !tbaa !2
  %357 = load i64, i64* %351, align 8, !tbaa !2
  %358 = icmp ult i64 %356, %357
  br i1 %358, label %.preheader161, label %379

.preheader161:                                    ; preds = %355
  br label %359

; <label>:359:                                    ; preds = %.preheader161, %366
  %360 = phi i64 [ %368, %366 ], [ %357, %.preheader161 ]
  %361 = phi i64 [ %364, %366 ], [ %350, %.preheader161 ]
  %362 = phi i64* [ %367, %366 ], [ %351, %.preheader161 ]
  %363 = getelementptr inbounds i64, i64* %225, i64 %361
  %364 = add nsw i64 %361, -1
  store i64 %360, i64* %363, align 8, !tbaa !2
  %365 = icmp eq i64 %364, 1
  br i1 %365, label %.loopexit6, label %366

; <label>:366:                                    ; preds = %359
  %367 = getelementptr inbounds i64, i64* %362, i64 -1
  %368 = load i64, i64* %367, align 8, !tbaa !2
  %369 = icmp ult i64 %356, %368
  br i1 %369, label %359, label %370

; <label>:370:                                    ; preds = %366
  %371 = getelementptr inbounds i64, i64* %225, i64 %364
  br label %.loopexit6

.loopexit6:                                       ; preds = %359, %370
  %372 = phi i64* [ %371, %370 ], [ %344, %359 ]
  store i64 %356, i64* %372, align 8, !tbaa !2
  %373 = ptrtoint i64* %353 to i64
  %374 = ptrtoint i64* %372 to i64
  %375 = sub i64 %373, %374
  %376 = lshr exact i64 %375, 3
  %377 = trunc i64 %376 to i32
  %378 = add i32 %352, %377
  br label %379

; <label>:379:                                    ; preds = %.loopexit6, %355
  %380 = phi i32 [ %378, %.loopexit6 ], [ %352, %355 ]
  %381 = add nuw nsw i64 %350, 1
  %382 = getelementptr inbounds i64, i64* %225, i64 %381
  %383 = icmp eq i64* %382, %180
  br i1 %383, label %.loopexit, label %349

.loopexit7:                                       ; preds = %313, %349, %306
  tail call void @_Z11pdqsort_recPmmmib(i64* %0, i64 %1, i64 %230, i32 %307, i1 zeroext %4)
  %384 = add nsw i64 %230, 1
  tail call void @_Z11pdqsort_recPmmmib(i64* %0, i64 %384, i64 %2, i32 %307, i1 zeroext false)
  br label %.loopexit

.loopexit:                                        ; preds = %379, %.loopexit3, %409, %397, %.loopexit7, %.loopexit10, %235, %.loopexit14, %83, %58, %57, %30, %14, %13
  ret void

; <label>:385:                                    ; preds = %.preheader, %391
  %386 = phi i64 [ %393, %391 ], [ %53, %.preheader ]
  %387 = phi i64* [ %389, %391 ], [ %54, %.preheader ]
  %388 = phi i64* [ %392, %391 ], [ %35, %.preheader ]
  %389 = getelementptr inbounds i64, i64* %387, i64 -1
  store i64 %386, i64* %387, align 8, !tbaa !2
  %390 = icmp eq i64* %389, %10
  br i1 %390, label %395, label %391

; <label>:391:                                    ; preds = %385
  %392 = getelementptr inbounds i64, i64* %388, i64 -1
  %393 = load i64, i64* %392, align 8, !tbaa !2
  %394 = icmp ult i64 %55, %393
  br i1 %394, label %385, label %395

; <label>:395:                                    ; preds = %391, %385
  %396 = phi i64* [ %10, %385 ], [ %389, %391 ]
  store i64 %55, i64* %396, align 8, !tbaa !2
  br label %397

; <label>:397:                                    ; preds = %395, %52
  %398 = getelementptr inbounds i64, i64* %35, i64 2
  %399 = icmp eq i64* %398, %11
  br i1 %399, label %.loopexit, label %34

; <label>:400:                                    ; preds = %.preheader153, %400
  %401 = phi i64 [ %406, %400 ], [ %103, %.preheader153 ]
  %402 = phi i64* [ %404, %400 ], [ %104, %.preheader153 ]
  %403 = phi i64* [ %405, %400 ], [ %88, %.preheader153 ]
  %404 = getelementptr inbounds i64, i64* %402, i64 -1
  store i64 %401, i64* %402, align 8, !tbaa !2
  %405 = getelementptr inbounds i64, i64* %403, i64 -1
  %406 = load i64, i64* %405, align 8, !tbaa !2
  %407 = icmp ult i64 %105, %406
  br i1 %407, label %400, label %408

; <label>:408:                                    ; preds = %400
  store i64 %105, i64* %404, align 8, !tbaa !2
  br label %409

; <label>:409:                                    ; preds = %408, %102
  %410 = getelementptr inbounds i64, i64* %88, i64 2
  %411 = icmp eq i64* %410, %11
  br i1 %411, label %.loopexit, label %87
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

; <label>:28:                                     ; preds = %27, %23
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

; <label>:50:                                     ; preds = %49, %45
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

; <label>:72:                                     ; preds = %71, %67
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

; <label>:87:                                     ; preds = %86, %83
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

; <label>:56:                                     ; preds = %29, %15, %13
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
  %83 = add i64 %60, %81
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

; <label>:99:                                     ; preds = %73, %58, %56, %4
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

; <label>:48:                                     ; preds = %42, %39
  %49 = phi i8 [ %41, %39 ], [ %47, %42 ]
  %50 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %49)
  %51 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %50)
  %52 = bitcast %"class.std::vector"* %21 to i8*
  %53 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %21, i64 0, i32 0, i32 0, i32 0
  %54 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %21, i64 0, i32 0, i32 0, i32 1
  %55 = bitcast i64** %54 to i64*
  br label %64

; <label>:56:                                     ; preds = %85
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
          to label %97 unwind label %1377

; <label>:64:                                     ; preds = %85, %48
  %65 = phi i64 [ 0, %48 ], [ %86, %85 ]
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %52) #2
  call void @_ZN13Int_Generator6randomEm(%"class.std::vector"* nonnull sret %21, i64 1000)
  %66 = load i64*, i64** %53, align 8, !tbaa !19
  %67 = load i64, i64* %55, align 8, !tbaa !22
  %68 = ptrtoint i64* %66 to i64
  %69 = sub i64 %67, %68
  %70 = ashr exact i64 %69, 3
  %71 = icmp eq i64 %69, 0
  br i1 %71, label %79, label %.preheader45

.preheader45:                                     ; preds = %64
  br label %72

; <label>:72:                                     ; preds = %.preheader45, %72
  %73 = phi i64 [ %75, %72 ], [ %70, %.preheader45 ]
  %74 = phi i32 [ %77, %72 ], [ 0, %.preheader45 ]
  %75 = lshr i64 %73, 1
  %76 = icmp eq i64 %75, 0
  %77 = add nuw nsw i32 %74, 1
  br i1 %76, label %78, label %72

; <label>:78:                                     ; preds = %72
  invoke void @_Z11pdqsort_recPmmmib(i64* %66, i64 0, i64 %70, i32 %74, i1 zeroext true)
          to label %79 unwind label %88

; <label>:79:                                     ; preds = %78, %64
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %21)
          to label %80 unwind label %88

; <label>:80:                                     ; preds = %79
  %81 = load i64*, i64** %53, align 8, !tbaa !19
  %82 = icmp eq i64* %81, null
  br i1 %82, label %85, label %83

; <label>:83:                                     ; preds = %80
  %84 = bitcast i64* %81 to i8*
  call void @_ZdlPv(i8* %84) #2
  br label %85

; <label>:85:                                     ; preds = %83, %80
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %52) #2
  %86 = add nuw nsw i64 %65, 1
  %87 = icmp ult i64 %86, 100
  br i1 %87, label %64, label %56

; <label>:88:                                     ; preds = %79, %78
  %89 = landingpad { i8*, i32 }
          cleanup
  %90 = extractvalue { i8*, i32 } %89, 0
  %91 = extractvalue { i8*, i32 } %89, 1
  %92 = load i64*, i64** %53, align 8, !tbaa !19
  %93 = icmp eq i64* %92, null
  br i1 %93, label %96, label %94

; <label>:94:                                     ; preds = %88
  %95 = bitcast i64* %92 to i8*
  call void @_ZdlPv(i8* %95) #2
  br label %96

; <label>:96:                                     ; preds = %94, %88
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %52) #2
  br label %1395

; <label>:97:                                     ; preds = %56
  %98 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) %63, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i64 1)
          to label %99 unwind label %1377

; <label>:99:                                     ; preds = %97
  %100 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %101 unwind label %1377

; <label>:101:                                    ; preds = %99
  %102 = bitcast %"class.std::vector"* %12 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %102) #2
  invoke void @_ZN13Int_Generator6randomEm(%"class.std::vector"* nonnull sret %12, i64 10000000)
          to label %103 unwind label %1377

; <label>:103:                                    ; preds = %101
  %104 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %105 unwind label %623

; <label>:105:                                    ; preds = %103
  %106 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %107 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %12, i64 0, i32 0, i32 0, i32 0
  %108 = load i64*, i64** %107, align 8, !tbaa !23
  %109 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %12, i64 0, i32 0, i32 0, i32 1
  %110 = load i64*, i64** %109, align 8, !tbaa !23
  %111 = icmp eq i64* %108, %110
  br i1 %111, label %120, label %112

; <label>:112:                                    ; preds = %105
  %113 = ptrtoint i64* %110 to i64
  %114 = ptrtoint i64* %108 to i64
  %115 = sub i64 %113, %114
  %116 = ashr i64 %115, 4
  %117 = call i64 @llvm.ctlz.i64(i64 %116, i1 false) #2, !range !24
  %118 = trunc i64 %117 to i32
  %119 = sub nsw i32 64, %118
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %108, i64* %110, i32 %119, i1 zeroext true)
          to label %120 unwind label %623

; <label>:120:                                    ; preds = %112, %105
  %121 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %122 = sub nsw i64 %121, %106
  %123 = sitofp i64 %122 to double
  %124 = fdiv double %123, 1.000000e+09
  %125 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %124)
          to label %126 unwind label %623

; <label>:126:                                    ; preds = %120
  %127 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %128 unwind label %623

; <label>:128:                                    ; preds = %126
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %12)
          to label %129 unwind label %623

; <label>:129:                                    ; preds = %128
  %130 = load i64*, i64** %107, align 8, !tbaa !19
  %131 = icmp eq i64* %130, null
  br i1 %131, label %134, label %132

; <label>:132:                                    ; preds = %129
  %133 = bitcast i64* %130 to i8*
  call void @_ZdlPv(i8* %133) #2
  br label %134

; <label>:134:                                    ; preds = %132, %129
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %102) #2
  %135 = bitcast %"class.std::vector"* %13 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %135) #2
  invoke void @_ZN13Int_Generator10random_dupEmm(%"class.std::vector"* nonnull sret %13, i64 10000000, i64 10000)
          to label %136 unwind label %1377

; <label>:136:                                    ; preds = %134
  %137 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %138 unwind label %633

; <label>:138:                                    ; preds = %136
  %139 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %140 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %13, i64 0, i32 0, i32 0, i32 0
  %141 = load i64*, i64** %140, align 8, !tbaa !23
  %142 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %13, i64 0, i32 0, i32 0, i32 1
  %143 = load i64*, i64** %142, align 8, !tbaa !23
  %144 = icmp eq i64* %141, %143
  br i1 %144, label %153, label %145

; <label>:145:                                    ; preds = %138
  %146 = ptrtoint i64* %143 to i64
  %147 = ptrtoint i64* %141 to i64
  %148 = sub i64 %146, %147
  %149 = ashr i64 %148, 4
  %150 = call i64 @llvm.ctlz.i64(i64 %149, i1 false) #2, !range !24
  %151 = trunc i64 %150 to i32
  %152 = sub nsw i32 64, %151
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %141, i64* %143, i32 %152, i1 zeroext true)
          to label %153 unwind label %633

; <label>:153:                                    ; preds = %145, %138
  %154 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %155 = sub nsw i64 %154, %139
  %156 = sitofp i64 %155 to double
  %157 = fdiv double %156, 1.000000e+09
  %158 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %157)
          to label %159 unwind label %633

; <label>:159:                                    ; preds = %153
  %160 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %161 unwind label %633

; <label>:161:                                    ; preds = %159
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %13)
          to label %162 unwind label %633

; <label>:162:                                    ; preds = %161
  %163 = load i64*, i64** %140, align 8, !tbaa !19
  %164 = icmp eq i64* %163, null
  br i1 %164, label %167, label %165

; <label>:165:                                    ; preds = %162
  %166 = bitcast i64* %163 to i8*
  call void @_ZdlPv(i8* %166) #2
  br label %167

; <label>:167:                                    ; preds = %165, %162
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %135) #2
  %168 = bitcast %"class.std::vector"* %14 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %168) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %168, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !25
  %169 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %14, i64 0, i32 0, i32 0, i32 2
  %170 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %14, i64 0, i32 0, i32 0, i32 1
  %171 = invoke i8* @_Znwm(i64 800000000)
          to label %172 unwind label %181, !noalias !25

; <label>:172:                                    ; preds = %167
  %173 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %14, i64 0, i32 0, i32 0, i32 0
  %174 = bitcast %"class.std::vector"* %14 to i8**
  store i8* %171, i8** %174, align 8, !tbaa !19, !alias.scope !25
  %175 = getelementptr inbounds i8, i8* %171, i64 800000000
  %176 = bitcast i64** %169 to i8**
  store i8* %175, i8** %176, align 8, !tbaa !28, !alias.scope !25
  %177 = ptrtoint i8* %171 to i64
  %178 = bitcast i64** %170 to i64*
  store i64 %177, i64* %178, align 8, !tbaa !22, !alias.scope !25
  %179 = bitcast i8* %171 to i64*
  %180 = bitcast i8* %175 to i64*
  br label %185

; <label>:181:                                    ; preds = %167
  %182 = landingpad { i8*, i32 }
          cleanup
  %183 = extractvalue { i8*, i32 } %182, 0
  %184 = extractvalue { i8*, i32 } %182, 1
  br label %263

; <label>:185:                                    ; preds = %245, %172
  %186 = phi i64 [ %177, %172 ], [ %246, %245 ]
  %187 = phi i64* [ %180, %172 ], [ %247, %245 ]
  %188 = phi i64* [ %179, %172 ], [ %248, %245 ]
  %189 = phi i64 [ 0, %172 ], [ %249, %245 ]
  %190 = icmp eq i64* %188, %187
  %191 = ptrtoint i64* %188 to i64
  br i1 %190, label %194, label %192

; <label>:192:                                    ; preds = %185
  store i64 %189, i64* %188, align 8, !tbaa !2
  %193 = getelementptr inbounds i64, i64* %188, i64 1
  store i64* %193, i64** %170, align 8, !tbaa !22
  br label %245

; <label>:194:                                    ; preds = %185
  %195 = sub i64 %191, %186
  %196 = ashr exact i64 %195, 3
  %197 = icmp eq i64 %195, 0
  %198 = select i1 %197, i64 1, i64 %196
  %199 = add nsw i64 %198, %196
  %200 = icmp ult i64 %199, %196
  %201 = icmp ugt i64 %199, 2305843009213693951
  %202 = or i1 %200, %201
  %203 = select i1 %202, i64 2305843009213693951, i64 %199
  %204 = icmp eq i64 %203, 0
  %205 = inttoptr i64 %186 to i64*
  br i1 %204, label %216, label %206

; <label>:206:                                    ; preds = %194
  %207 = icmp ugt i64 %203, 2305843009213693951
  br i1 %207, label %208, label %210

; <label>:208:                                    ; preds = %206
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %209 unwind label %253

; <label>:209:                                    ; preds = %208
  unreachable

; <label>:210:                                    ; preds = %206
  %211 = shl i64 %203, 3
  %212 = invoke i8* @_Znwm(i64 %211)
          to label %213 unwind label %251

; <label>:213:                                    ; preds = %210
  %214 = bitcast i8* %212 to i64*
  %215 = load i64*, i64** %173, align 8, !tbaa !19
  br label %216

; <label>:216:                                    ; preds = %213, %194
  %217 = phi i64* [ %215, %213 ], [ %205, %194 ]
  %218 = phi i8* [ %212, %213 ], [ null, %194 ]
  %219 = phi i64* [ %214, %213 ], [ null, %194 ]
  %220 = getelementptr inbounds i64, i64* %219, i64 %196
  store i64 %189, i64* %220, align 8, !tbaa !2
  %221 = ptrtoint i64* %217 to i64
  %222 = sub i64 %191, %221
  %223 = ashr exact i64 %222, 3
  %224 = icmp eq i64 %222, 0
  br i1 %224, label %227, label %225

; <label>:225:                                    ; preds = %216
  %226 = bitcast i64* %217 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %218, i8* %226, i64 %222, i32 8, i1 false) #2
  br label %227

; <label>:227:                                    ; preds = %225, %216
  %228 = getelementptr inbounds i64, i64* %219, i64 %223
  %229 = getelementptr inbounds i64, i64* %228, i64 1
  %230 = load i64, i64* %178, align 8, !tbaa !22
  %231 = sub i64 %230, %191
  %232 = ashr exact i64 %231, 3
  %233 = icmp eq i64 %231, 0
  br i1 %233, label %237, label %234

; <label>:234:                                    ; preds = %227
  %235 = bitcast i64* %229 to i8*
  %236 = bitcast i64* %187 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %235, i8* %236, i64 %231, i32 8, i1 false) #2
  br label %237

; <label>:237:                                    ; preds = %234, %227
  %238 = getelementptr inbounds i64, i64* %229, i64 %232
  %239 = icmp eq i64* %217, null
  br i1 %239, label %242, label %240

; <label>:240:                                    ; preds = %237
  %241 = bitcast i64* %217 to i8*
  call void @_ZdlPv(i8* %241) #2
  br label %242

; <label>:242:                                    ; preds = %240, %237
  store i8* %218, i8** %174, align 8, !tbaa !19
  store i64* %238, i64** %170, align 8, !tbaa !22
  %243 = getelementptr inbounds i64, i64* %219, i64 %203
  store i64* %243, i64** %169, align 8, !tbaa !28
  %244 = ptrtoint i8* %218 to i64
  br label %245

; <label>:245:                                    ; preds = %242, %192
  %246 = phi i64 [ %244, %242 ], [ %186, %192 ]
  %247 = phi i64* [ %243, %242 ], [ %187, %192 ]
  %248 = phi i64* [ %238, %242 ], [ %193, %192 ]
  %249 = add nuw nsw i64 %189, 1
  %250 = icmp ult i64 %249, 100000000
  br i1 %250, label %185, label %268

; <label>:251:                                    ; preds = %210
  %252 = landingpad { i8*, i32 }
          cleanup
  br label %255

; <label>:253:                                    ; preds = %208
  %254 = landingpad { i8*, i32 }
          cleanup
  br label %255

; <label>:255:                                    ; preds = %253, %251
  %256 = phi { i8*, i32 } [ %252, %251 ], [ %254, %253 ]
  %257 = extractvalue { i8*, i32 } %256, 0
  %258 = extractvalue { i8*, i32 } %256, 1
  %259 = load i64*, i64** %173, align 8, !tbaa !19, !alias.scope !25
  %260 = icmp eq i64* %259, null
  br i1 %260, label %263, label %261

; <label>:261:                                    ; preds = %255
  %262 = bitcast i64* %259 to i8*
  call void @_ZdlPv(i8* %262) #2
  br label %263

; <label>:263:                                    ; preds = %261, %255, %181
  %264 = phi i32 [ %184, %181 ], [ %258, %261 ], [ %258, %255 ]
  %265 = phi i8* [ %183, %181 ], [ %257, %261 ], [ %257, %255 ]
  %266 = insertvalue { i8*, i32 } undef, i8* %265, 0
  %267 = insertvalue { i8*, i32 } %266, i32 %264, 1
  br label %1379

; <label>:268:                                    ; preds = %245
  %269 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %270 unwind label %643

; <label>:270:                                    ; preds = %268
  %271 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %272 = load i64*, i64** %173, align 8, !tbaa !23
  %273 = load i64*, i64** %170, align 8, !tbaa !23
  %274 = icmp eq i64* %272, %273
  br i1 %274, label %283, label %275

; <label>:275:                                    ; preds = %270
  %276 = ptrtoint i64* %273 to i64
  %277 = ptrtoint i64* %272 to i64
  %278 = sub i64 %276, %277
  %279 = ashr i64 %278, 4
  %280 = call i64 @llvm.ctlz.i64(i64 %279, i1 false) #2, !range !24
  %281 = trunc i64 %280 to i32
  %282 = sub nsw i32 64, %281
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %272, i64* %273, i32 %282, i1 zeroext true)
          to label %283 unwind label %643

; <label>:283:                                    ; preds = %275, %270
  %284 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %285 = sub nsw i64 %284, %271
  %286 = sitofp i64 %285 to double
  %287 = fdiv double %286, 1.000000e+09
  %288 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %287)
          to label %289 unwind label %643

; <label>:289:                                    ; preds = %283
  %290 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %291 unwind label %643

; <label>:291:                                    ; preds = %289
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %14)
          to label %292 unwind label %643

; <label>:292:                                    ; preds = %291
  %293 = load i64*, i64** %173, align 8, !tbaa !19
  %294 = icmp eq i64* %293, null
  br i1 %294, label %297, label %295

; <label>:295:                                    ; preds = %292
  %296 = bitcast i64* %293 to i8*
  call void @_ZdlPv(i8* %296) #2
  br label %297

; <label>:297:                                    ; preds = %295, %292
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %168) #2
  %298 = bitcast %"class.std::vector"* %15 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %298) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %15, i64 10000000, i64 100000)
          to label %299 unwind label %1377

; <label>:299:                                    ; preds = %297
  %300 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %301 unwind label %652

; <label>:301:                                    ; preds = %299
  %302 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %303 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %15, i64 0, i32 0, i32 0, i32 0
  %304 = load i64*, i64** %303, align 8, !tbaa !23
  %305 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %15, i64 0, i32 0, i32 0, i32 1
  %306 = load i64*, i64** %305, align 8, !tbaa !23
  %307 = icmp eq i64* %304, %306
  br i1 %307, label %316, label %308

; <label>:308:                                    ; preds = %301
  %309 = ptrtoint i64* %306 to i64
  %310 = ptrtoint i64* %304 to i64
  %311 = sub i64 %309, %310
  %312 = ashr i64 %311, 4
  %313 = call i64 @llvm.ctlz.i64(i64 %312, i1 false) #2, !range !24
  %314 = trunc i64 %313 to i32
  %315 = sub nsw i32 64, %314
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %304, i64* %306, i32 %315, i1 zeroext true)
          to label %316 unwind label %652

; <label>:316:                                    ; preds = %308, %301
  %317 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %318 = sub nsw i64 %317, %302
  %319 = sitofp i64 %318 to double
  %320 = fdiv double %319, 1.000000e+09
  %321 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %320)
          to label %322 unwind label %652

; <label>:322:                                    ; preds = %316
  %323 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %324 unwind label %652

; <label>:324:                                    ; preds = %322
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %15)
          to label %325 unwind label %652

; <label>:325:                                    ; preds = %324
  %326 = load i64*, i64** %303, align 8, !tbaa !19
  %327 = icmp eq i64* %326, null
  br i1 %327, label %330, label %328

; <label>:328:                                    ; preds = %325
  %329 = bitcast i64* %326 to i8*
  call void @_ZdlPv(i8* %329) #2
  br label %330

; <label>:330:                                    ; preds = %328, %325
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %298) #2
  %331 = bitcast %"class.std::vector"* %16 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %331) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %16, i64 10000000, i64 1000000)
          to label %332 unwind label %1377

; <label>:332:                                    ; preds = %330
  %333 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %334 unwind label %662

; <label>:334:                                    ; preds = %332
  %335 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %336 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %16, i64 0, i32 0, i32 0, i32 0
  %337 = load i64*, i64** %336, align 8, !tbaa !23
  %338 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %16, i64 0, i32 0, i32 0, i32 1
  %339 = load i64*, i64** %338, align 8, !tbaa !23
  %340 = icmp eq i64* %337, %339
  br i1 %340, label %349, label %341

; <label>:341:                                    ; preds = %334
  %342 = ptrtoint i64* %339 to i64
  %343 = ptrtoint i64* %337 to i64
  %344 = sub i64 %342, %343
  %345 = ashr i64 %344, 4
  %346 = call i64 @llvm.ctlz.i64(i64 %345, i1 false) #2, !range !24
  %347 = trunc i64 %346 to i32
  %348 = sub nsw i32 64, %347
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %337, i64* %339, i32 %348, i1 zeroext true)
          to label %349 unwind label %662

; <label>:349:                                    ; preds = %341, %334
  %350 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %351 = sub nsw i64 %350, %335
  %352 = sitofp i64 %351 to double
  %353 = fdiv double %352, 1.000000e+09
  %354 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %353)
          to label %355 unwind label %662

; <label>:355:                                    ; preds = %349
  %356 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %357 unwind label %662

; <label>:357:                                    ; preds = %355
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %16)
          to label %358 unwind label %662

; <label>:358:                                    ; preds = %357
  %359 = load i64*, i64** %336, align 8, !tbaa !19
  %360 = icmp eq i64* %359, null
  br i1 %360, label %363, label %361

; <label>:361:                                    ; preds = %358
  %362 = bitcast i64* %359 to i8*
  call void @_ZdlPv(i8* %362) #2
  br label %363

; <label>:363:                                    ; preds = %361, %358
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %331) #2
  %364 = bitcast %"class.std::vector"* %17 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %364) #2
  invoke void @_ZN13Int_Generator13sorted_middleEmm(%"class.std::vector"* nonnull sret %17, i64 10000000, i64 1000000)
          to label %365 unwind label %1377

; <label>:365:                                    ; preds = %363
  %366 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %367 unwind label %672

; <label>:367:                                    ; preds = %365
  %368 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %369 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %17, i64 0, i32 0, i32 0, i32 0
  %370 = load i64*, i64** %369, align 8, !tbaa !23
  %371 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %17, i64 0, i32 0, i32 0, i32 1
  %372 = load i64*, i64** %371, align 8, !tbaa !23
  %373 = icmp eq i64* %370, %372
  br i1 %373, label %382, label %374

; <label>:374:                                    ; preds = %367
  %375 = ptrtoint i64* %372 to i64
  %376 = ptrtoint i64* %370 to i64
  %377 = sub i64 %375, %376
  %378 = ashr i64 %377, 4
  %379 = call i64 @llvm.ctlz.i64(i64 %378, i1 false) #2, !range !24
  %380 = trunc i64 %379 to i32
  %381 = sub nsw i32 64, %380
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %370, i64* %372, i32 %381, i1 zeroext true)
          to label %382 unwind label %672

; <label>:382:                                    ; preds = %374, %367
  %383 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %384 = sub nsw i64 %383, %368
  %385 = sitofp i64 %384 to double
  %386 = fdiv double %385, 1.000000e+09
  %387 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %386)
          to label %388 unwind label %672

; <label>:388:                                    ; preds = %382
  %389 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %390 unwind label %672

; <label>:390:                                    ; preds = %388
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %17)
          to label %391 unwind label %672

; <label>:391:                                    ; preds = %390
  %392 = load i64*, i64** %369, align 8, !tbaa !19
  %393 = icmp eq i64* %392, null
  br i1 %393, label %396, label %394

; <label>:394:                                    ; preds = %391
  %395 = bitcast i64* %392 to i8*
  call void @_ZdlPv(i8* %395) #2
  br label %396

; <label>:396:                                    ; preds = %394, %391
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %364) #2
  %397 = bitcast %"class.std::vector"* %18 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %397) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %397, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !29
  %398 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %18, i64 0, i32 0, i32 0, i32 2
  %399 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %18, i64 0, i32 0, i32 0, i32 1
  %400 = invoke i8* @_Znwm(i64 800000000)
          to label %401 unwind label %410, !noalias !29

; <label>:401:                                    ; preds = %396
  %402 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %18, i64 0, i32 0, i32 0, i32 0
  %403 = bitcast %"class.std::vector"* %18 to i8**
  store i8* %400, i8** %403, align 8, !tbaa !19, !alias.scope !29
  %404 = getelementptr inbounds i8, i8* %400, i64 800000000
  %405 = bitcast i64** %398 to i8**
  store i8* %404, i8** %405, align 8, !tbaa !28, !alias.scope !29
  %406 = ptrtoint i8* %400 to i64
  %407 = bitcast i64** %399 to i64*
  store i64 %406, i64* %407, align 8, !tbaa !22, !alias.scope !29
  %408 = bitcast i8* %400 to i64*
  %409 = bitcast i8* %404 to i64*
  br label %414

; <label>:410:                                    ; preds = %396
  %411 = landingpad { i8*, i32 }
          cleanup
  %412 = extractvalue { i8*, i32 } %411, 0
  %413 = extractvalue { i8*, i32 } %411, 1
  br label %492

; <label>:414:                                    ; preds = %474, %401
  %415 = phi i64 [ %406, %401 ], [ %475, %474 ]
  %416 = phi i64* [ %409, %401 ], [ %476, %474 ]
  %417 = phi i64* [ %408, %401 ], [ %477, %474 ]
  %418 = phi i64 [ 100000000, %401 ], [ %478, %474 ]
  %419 = icmp eq i64* %417, %416
  %420 = ptrtoint i64* %417 to i64
  br i1 %419, label %423, label %421

; <label>:421:                                    ; preds = %414
  store i64 %418, i64* %417, align 8, !tbaa !2
  %422 = getelementptr inbounds i64, i64* %417, i64 1
  store i64* %422, i64** %399, align 8, !tbaa !22
  br label %474

; <label>:423:                                    ; preds = %414
  %424 = sub i64 %420, %415
  %425 = ashr exact i64 %424, 3
  %426 = icmp eq i64 %424, 0
  %427 = select i1 %426, i64 1, i64 %425
  %428 = add nsw i64 %427, %425
  %429 = icmp ult i64 %428, %425
  %430 = icmp ugt i64 %428, 2305843009213693951
  %431 = or i1 %429, %430
  %432 = select i1 %431, i64 2305843009213693951, i64 %428
  %433 = icmp eq i64 %432, 0
  %434 = inttoptr i64 %415 to i64*
  br i1 %433, label %445, label %435

; <label>:435:                                    ; preds = %423
  %436 = icmp ugt i64 %432, 2305843009213693951
  br i1 %436, label %437, label %439

; <label>:437:                                    ; preds = %435
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %438 unwind label %482

; <label>:438:                                    ; preds = %437
  unreachable

; <label>:439:                                    ; preds = %435
  %440 = shl i64 %432, 3
  %441 = invoke i8* @_Znwm(i64 %440)
          to label %442 unwind label %480

; <label>:442:                                    ; preds = %439
  %443 = bitcast i8* %441 to i64*
  %444 = load i64*, i64** %402, align 8, !tbaa !19
  br label %445

; <label>:445:                                    ; preds = %442, %423
  %446 = phi i64* [ %444, %442 ], [ %434, %423 ]
  %447 = phi i8* [ %441, %442 ], [ null, %423 ]
  %448 = phi i64* [ %443, %442 ], [ null, %423 ]
  %449 = getelementptr inbounds i64, i64* %448, i64 %425
  store i64 %418, i64* %449, align 8, !tbaa !2
  %450 = ptrtoint i64* %446 to i64
  %451 = sub i64 %420, %450
  %452 = ashr exact i64 %451, 3
  %453 = icmp eq i64 %451, 0
  br i1 %453, label %456, label %454

; <label>:454:                                    ; preds = %445
  %455 = bitcast i64* %446 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %447, i8* %455, i64 %451, i32 8, i1 false) #2
  br label %456

; <label>:456:                                    ; preds = %454, %445
  %457 = getelementptr inbounds i64, i64* %448, i64 %452
  %458 = getelementptr inbounds i64, i64* %457, i64 1
  %459 = load i64, i64* %407, align 8, !tbaa !22
  %460 = sub i64 %459, %420
  %461 = ashr exact i64 %460, 3
  %462 = icmp eq i64 %460, 0
  br i1 %462, label %466, label %463

; <label>:463:                                    ; preds = %456
  %464 = bitcast i64* %458 to i8*
  %465 = bitcast i64* %416 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %464, i8* %465, i64 %460, i32 8, i1 false) #2
  br label %466

; <label>:466:                                    ; preds = %463, %456
  %467 = getelementptr inbounds i64, i64* %458, i64 %461
  %468 = icmp eq i64* %446, null
  br i1 %468, label %471, label %469

; <label>:469:                                    ; preds = %466
  %470 = bitcast i64* %446 to i8*
  call void @_ZdlPv(i8* %470) #2
  br label %471

; <label>:471:                                    ; preds = %469, %466
  store i8* %447, i8** %403, align 8, !tbaa !19
  store i64* %467, i64** %399, align 8, !tbaa !22
  %472 = getelementptr inbounds i64, i64* %448, i64 %432
  store i64* %472, i64** %398, align 8, !tbaa !28
  %473 = ptrtoint i8* %447 to i64
  br label %474

; <label>:474:                                    ; preds = %471, %421
  %475 = phi i64 [ %473, %471 ], [ %415, %421 ]
  %476 = phi i64* [ %472, %471 ], [ %416, %421 ]
  %477 = phi i64* [ %467, %471 ], [ %422, %421 ]
  %478 = add nsw i64 %418, -1
  %479 = icmp eq i64 %478, 0
  br i1 %479, label %497, label %414

; <label>:480:                                    ; preds = %439
  %481 = landingpad { i8*, i32 }
          cleanup
  br label %484

; <label>:482:                                    ; preds = %437
  %483 = landingpad { i8*, i32 }
          cleanup
  br label %484

; <label>:484:                                    ; preds = %482, %480
  %485 = phi { i8*, i32 } [ %481, %480 ], [ %483, %482 ]
  %486 = extractvalue { i8*, i32 } %485, 0
  %487 = extractvalue { i8*, i32 } %485, 1
  %488 = load i64*, i64** %402, align 8, !tbaa !19, !alias.scope !29
  %489 = icmp eq i64* %488, null
  br i1 %489, label %492, label %490

; <label>:490:                                    ; preds = %484
  %491 = bitcast i64* %488 to i8*
  call void @_ZdlPv(i8* %491) #2
  br label %492

; <label>:492:                                    ; preds = %490, %484, %410
  %493 = phi i32 [ %413, %410 ], [ %487, %490 ], [ %487, %484 ]
  %494 = phi i8* [ %412, %410 ], [ %486, %490 ], [ %486, %484 ]
  %495 = insertvalue { i8*, i32 } undef, i8* %494, 0
  %496 = insertvalue { i8*, i32 } %495, i32 %493, 1
  br label %1379

; <label>:497:                                    ; preds = %474
  %498 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %499 unwind label %682

; <label>:499:                                    ; preds = %497
  %500 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %501 = load i64*, i64** %402, align 8, !tbaa !23
  %502 = load i64*, i64** %399, align 8, !tbaa !23
  %503 = icmp eq i64* %501, %502
  br i1 %503, label %512, label %504

; <label>:504:                                    ; preds = %499
  %505 = ptrtoint i64* %502 to i64
  %506 = ptrtoint i64* %501 to i64
  %507 = sub i64 %505, %506
  %508 = ashr i64 %507, 4
  %509 = call i64 @llvm.ctlz.i64(i64 %508, i1 false) #2, !range !24
  %510 = trunc i64 %509 to i32
  %511 = sub nsw i32 64, %510
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %501, i64* %502, i32 %511, i1 zeroext true)
          to label %512 unwind label %682

; <label>:512:                                    ; preds = %504, %499
  %513 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %514 = sub nsw i64 %513, %500
  %515 = sitofp i64 %514 to double
  %516 = fdiv double %515, 1.000000e+09
  %517 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %516)
          to label %518 unwind label %682

; <label>:518:                                    ; preds = %512
  %519 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %520 unwind label %682

; <label>:520:                                    ; preds = %518
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %18)
          to label %521 unwind label %682

; <label>:521:                                    ; preds = %520
  %522 = load i64*, i64** %402, align 8, !tbaa !19
  %523 = icmp eq i64* %522, null
  br i1 %523, label %526, label %524

; <label>:524:                                    ; preds = %521
  %525 = bitcast i64* %522 to i8*
  call void @_ZdlPv(i8* %525) #2
  br label %526

; <label>:526:                                    ; preds = %524, %521
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %397) #2
  %527 = bitcast %"class.std::vector"* %19 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %527) #2
  invoke void @_ZN13Int_Generator18reverse_sorted_endEmm(%"class.std::vector"* nonnull sret %19, i64 10000000, i64 1000000)
          to label %528 unwind label %1377

; <label>:528:                                    ; preds = %526
  %529 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %530 unwind label %691

; <label>:530:                                    ; preds = %528
  %531 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %532 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %19, i64 0, i32 0, i32 0, i32 0
  %533 = load i64*, i64** %532, align 8, !tbaa !23
  %534 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %19, i64 0, i32 0, i32 0, i32 1
  %535 = load i64*, i64** %534, align 8, !tbaa !23
  %536 = icmp eq i64* %533, %535
  br i1 %536, label %545, label %537

; <label>:537:                                    ; preds = %530
  %538 = ptrtoint i64* %535 to i64
  %539 = ptrtoint i64* %533 to i64
  %540 = sub i64 %538, %539
  %541 = ashr i64 %540, 4
  %542 = call i64 @llvm.ctlz.i64(i64 %541, i1 false) #2, !range !24
  %543 = trunc i64 %542 to i32
  %544 = sub nsw i32 64, %543
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %533, i64* %535, i32 %544, i1 zeroext true)
          to label %545 unwind label %691

; <label>:545:                                    ; preds = %537, %530
  %546 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %547 = sub nsw i64 %546, %531
  %548 = sitofp i64 %547 to double
  %549 = fdiv double %548, 1.000000e+09
  %550 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %549)
          to label %551 unwind label %691

; <label>:551:                                    ; preds = %545
  %552 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %553 unwind label %691

; <label>:553:                                    ; preds = %551
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %19)
          to label %554 unwind label %691

; <label>:554:                                    ; preds = %553
  %555 = load i64*, i64** %532, align 8, !tbaa !19
  %556 = icmp eq i64* %555, null
  br i1 %556, label %559, label %557

; <label>:557:                                    ; preds = %554
  %558 = bitcast i64* %555 to i8*
  call void @_ZdlPv(i8* %558) #2
  br label %559

; <label>:559:                                    ; preds = %557, %554
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %527) #2
  %560 = bitcast %"class.std::vector"* %20 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %560) #2
  invoke void @_ZN13Int_Generator21reverse_sorted_middleEmm(%"class.std::vector"* nonnull sret %20, i64 10000000, i64 1000000)
          to label %561 unwind label %1377

; <label>:561:                                    ; preds = %559
  %562 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %563 unwind label %701

; <label>:563:                                    ; preds = %561
  %564 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %565 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %20, i64 0, i32 0, i32 0, i32 0
  %566 = load i64*, i64** %565, align 8, !tbaa !23
  %567 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %20, i64 0, i32 0, i32 0, i32 1
  %568 = load i64*, i64** %567, align 8, !tbaa !23
  %569 = icmp eq i64* %566, %568
  br i1 %569, label %578, label %570

; <label>:570:                                    ; preds = %563
  %571 = ptrtoint i64* %568 to i64
  %572 = ptrtoint i64* %566 to i64
  %573 = sub i64 %571, %572
  %574 = ashr i64 %573, 4
  %575 = call i64 @llvm.ctlz.i64(i64 %574, i1 false) #2, !range !24
  %576 = trunc i64 %575 to i32
  %577 = sub nsw i32 64, %576
  invoke void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %566, i64* %568, i32 %577, i1 zeroext true)
          to label %578 unwind label %701

; <label>:578:                                    ; preds = %570, %563
  %579 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %580 = sub nsw i64 %579, %564
  %581 = sitofp i64 %580 to double
  %582 = fdiv double %581, 1.000000e+09
  %583 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %582)
          to label %584 unwind label %701

; <label>:584:                                    ; preds = %578
  %585 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %586 unwind label %701

; <label>:586:                                    ; preds = %584
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %20)
          to label %587 unwind label %701

; <label>:587:                                    ; preds = %586
  %588 = load i64*, i64** %565, align 8, !tbaa !19
  %589 = icmp eq i64* %588, null
  br i1 %589, label %592, label %590

; <label>:590:                                    ; preds = %587
  %591 = bitcast i64* %588 to i8*
  call void @_ZdlPv(i8* %591) #2
  br label %592

; <label>:592:                                    ; preds = %590, %587
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %560) #2
  %593 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %594 = getelementptr i8, i8* %593, i64 -24
  %595 = bitcast i8* %594 to i64*
  %596 = load i64, i64* %595, align 8
  %597 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %596
  %598 = getelementptr inbounds i8, i8* %597, i64 240
  %599 = bitcast i8* %598 to %"class.std::ctype"**
  %600 = load %"class.std::ctype"*, %"class.std::ctype"** %599, align 8, !tbaa !8
  %601 = icmp eq %"class.std::ctype"* %600, null
  br i1 %601, label %602, label %604

; <label>:602:                                    ; preds = %592
  invoke void @_ZSt16__throw_bad_castv() #16
          to label %603 unwind label %1377

; <label>:603:                                    ; preds = %602
  unreachable

; <label>:604:                                    ; preds = %592
  %605 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %600, i64 0, i32 8
  %606 = load i8, i8* %605, align 8, !tbaa !12
  %607 = icmp eq i8 %606, 0
  br i1 %607, label %611, label %608

; <label>:608:                                    ; preds = %604
  %609 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %600, i64 0, i32 9, i64 10
  %610 = load i8, i8* %609, align 1, !tbaa !14
  br label %618

; <label>:611:                                    ; preds = %604
  invoke void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %600)
          to label %612 unwind label %1377

; <label>:612:                                    ; preds = %611
  %613 = bitcast %"class.std::ctype"* %600 to i8 (%"class.std::ctype"*, i8)***
  %614 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %613, align 8, !tbaa !6
  %615 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %614, i64 6
  %616 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %615, align 8
  %617 = invoke signext i8 %616(%"class.std::ctype"* nonnull %600, i8 signext 10)
          to label %618 unwind label %1377

; <label>:618:                                    ; preds = %612, %608
  %619 = phi i8 [ %610, %608 ], [ %617, %612 ]
  %620 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %619)
          to label %621 unwind label %1377

; <label>:621:                                    ; preds = %618
  %622 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %620)
          to label %716 unwind label %1377

; <label>:623:                                    ; preds = %128, %126, %120, %112, %103
  %624 = landingpad { i8*, i32 }
          cleanup
  %625 = extractvalue { i8*, i32 } %624, 0
  %626 = extractvalue { i8*, i32 } %624, 1
  %627 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %12, i64 0, i32 0, i32 0, i32 0
  %628 = load i64*, i64** %627, align 8, !tbaa !19
  %629 = icmp eq i64* %628, null
  br i1 %629, label %632, label %630

; <label>:630:                                    ; preds = %623
  %631 = bitcast i64* %628 to i8*
  call void @_ZdlPv(i8* %631) #2
  br label %632

; <label>:632:                                    ; preds = %630, %623
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %102) #2
  br label %711

; <label>:633:                                    ; preds = %161, %159, %153, %145, %136
  %634 = landingpad { i8*, i32 }
          cleanup
  %635 = extractvalue { i8*, i32 } %634, 0
  %636 = extractvalue { i8*, i32 } %634, 1
  %637 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %13, i64 0, i32 0, i32 0, i32 0
  %638 = load i64*, i64** %637, align 8, !tbaa !19
  %639 = icmp eq i64* %638, null
  br i1 %639, label %642, label %640

; <label>:640:                                    ; preds = %633
  %641 = bitcast i64* %638 to i8*
  call void @_ZdlPv(i8* %641) #2
  br label %642

; <label>:642:                                    ; preds = %640, %633
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %135) #2
  br label %711

; <label>:643:                                    ; preds = %291, %289, %283, %275, %268
  %644 = landingpad { i8*, i32 }
          cleanup
  %645 = extractvalue { i8*, i32 } %644, 0
  %646 = extractvalue { i8*, i32 } %644, 1
  %647 = load i64*, i64** %173, align 8, !tbaa !19
  %648 = icmp eq i64* %647, null
  br i1 %648, label %651, label %649

; <label>:649:                                    ; preds = %643
  %650 = bitcast i64* %647 to i8*
  call void @_ZdlPv(i8* %650) #2
  br label %651

; <label>:651:                                    ; preds = %649, %643
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %168) #2
  br label %711

; <label>:652:                                    ; preds = %324, %322, %316, %308, %299
  %653 = landingpad { i8*, i32 }
          cleanup
  %654 = extractvalue { i8*, i32 } %653, 0
  %655 = extractvalue { i8*, i32 } %653, 1
  %656 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %15, i64 0, i32 0, i32 0, i32 0
  %657 = load i64*, i64** %656, align 8, !tbaa !19
  %658 = icmp eq i64* %657, null
  br i1 %658, label %661, label %659

; <label>:659:                                    ; preds = %652
  %660 = bitcast i64* %657 to i8*
  call void @_ZdlPv(i8* %660) #2
  br label %661

; <label>:661:                                    ; preds = %659, %652
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %298) #2
  br label %711

; <label>:662:                                    ; preds = %357, %355, %349, %341, %332
  %663 = landingpad { i8*, i32 }
          cleanup
  %664 = extractvalue { i8*, i32 } %663, 0
  %665 = extractvalue { i8*, i32 } %663, 1
  %666 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %16, i64 0, i32 0, i32 0, i32 0
  %667 = load i64*, i64** %666, align 8, !tbaa !19
  %668 = icmp eq i64* %667, null
  br i1 %668, label %671, label %669

; <label>:669:                                    ; preds = %662
  %670 = bitcast i64* %667 to i8*
  call void @_ZdlPv(i8* %670) #2
  br label %671

; <label>:671:                                    ; preds = %669, %662
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %331) #2
  br label %711

; <label>:672:                                    ; preds = %390, %388, %382, %374, %365
  %673 = landingpad { i8*, i32 }
          cleanup
  %674 = extractvalue { i8*, i32 } %673, 0
  %675 = extractvalue { i8*, i32 } %673, 1
  %676 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %17, i64 0, i32 0, i32 0, i32 0
  %677 = load i64*, i64** %676, align 8, !tbaa !19
  %678 = icmp eq i64* %677, null
  br i1 %678, label %681, label %679

; <label>:679:                                    ; preds = %672
  %680 = bitcast i64* %677 to i8*
  call void @_ZdlPv(i8* %680) #2
  br label %681

; <label>:681:                                    ; preds = %679, %672
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %364) #2
  br label %711

; <label>:682:                                    ; preds = %520, %518, %512, %504, %497
  %683 = landingpad { i8*, i32 }
          cleanup
  %684 = extractvalue { i8*, i32 } %683, 0
  %685 = extractvalue { i8*, i32 } %683, 1
  %686 = load i64*, i64** %402, align 8, !tbaa !19
  %687 = icmp eq i64* %686, null
  br i1 %687, label %690, label %688

; <label>:688:                                    ; preds = %682
  %689 = bitcast i64* %686 to i8*
  call void @_ZdlPv(i8* %689) #2
  br label %690

; <label>:690:                                    ; preds = %688, %682
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %397) #2
  br label %711

; <label>:691:                                    ; preds = %553, %551, %545, %537, %528
  %692 = landingpad { i8*, i32 }
          cleanup
  %693 = extractvalue { i8*, i32 } %692, 0
  %694 = extractvalue { i8*, i32 } %692, 1
  %695 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %19, i64 0, i32 0, i32 0, i32 0
  %696 = load i64*, i64** %695, align 8, !tbaa !19
  %697 = icmp eq i64* %696, null
  br i1 %697, label %700, label %698

; <label>:698:                                    ; preds = %691
  %699 = bitcast i64* %696 to i8*
  call void @_ZdlPv(i8* %699) #2
  br label %700

; <label>:700:                                    ; preds = %698, %691
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %527) #2
  br label %711

; <label>:701:                                    ; preds = %586, %584, %578, %570, %561
  %702 = landingpad { i8*, i32 }
          cleanup
  %703 = extractvalue { i8*, i32 } %702, 0
  %704 = extractvalue { i8*, i32 } %702, 1
  %705 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %20, i64 0, i32 0, i32 0, i32 0
  %706 = load i64*, i64** %705, align 8, !tbaa !19
  %707 = icmp eq i64* %706, null
  br i1 %707, label %710, label %708

; <label>:708:                                    ; preds = %701
  %709 = bitcast i64* %706 to i8*
  call void @_ZdlPv(i8* %709) #2
  br label %710

; <label>:710:                                    ; preds = %708, %701
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %560) #2
  br label %711

; <label>:711:                                    ; preds = %710, %700, %690, %681, %671, %661, %651, %642, %632
  %712 = phi i32 [ %704, %710 ], [ %694, %700 ], [ %685, %690 ], [ %675, %681 ], [ %665, %671 ], [ %655, %661 ], [ %646, %651 ], [ %636, %642 ], [ %626, %632 ]
  %713 = phi i8* [ %703, %710 ], [ %693, %700 ], [ %684, %690 ], [ %674, %681 ], [ %664, %671 ], [ %654, %661 ], [ %645, %651 ], [ %635, %642 ], [ %625, %632 ]
  %714 = insertvalue { i8*, i32 } undef, i8* %713, 0
  %715 = insertvalue { i8*, i32 } %714, i32 %712, 1
  br label %1379

; <label>:716:                                    ; preds = %621
  %717 = load i8*, i8** %62, align 8, !tbaa !32
  %718 = icmp eq i8* %717, %59
  br i1 %718, label %720, label %719

; <label>:719:                                    ; preds = %716
  call void @_ZdlPv(i8* %717) #2
  br label %720

; <label>:720:                                    ; preds = %719, %716
  %721 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %23, i64 0, i32 2
  %722 = bitcast %"class.std::__cxx11::basic_string"* %23 to %union.anon**
  store %union.anon* %721, %union.anon** %722, align 8, !tbaa !15
  %723 = bitcast %union.anon* %721 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %723, i8* nonnull getelementptr inbounds ([8 x i8], [8 x i8]* @.str.2, i64 0, i64 0), i64 7, i32 1, i1 false) #2
  %724 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %23, i64 0, i32 1
  store i64 7, i64* %724, align 8, !tbaa !17
  %725 = getelementptr inbounds i8, i8* %723, i64 7
  store i8 0, i8* %725, align 1, !tbaa !14
  %726 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %23, i64 0, i32 0, i32 0
  %727 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull %723, i64 7)
          to label %728 unwind label %1386

; <label>:728:                                    ; preds = %720
  %729 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) %727, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i64 1)
          to label %730 unwind label %1386

; <label>:730:                                    ; preds = %728
  %731 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %732 unwind label %1386

; <label>:732:                                    ; preds = %730
  %733 = bitcast %"class.std::vector"* %3 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %733) #2
  invoke void @_ZN13Int_Generator6randomEm(%"class.std::vector"* nonnull sret %3, i64 10000000)
          to label %734 unwind label %1386

; <label>:734:                                    ; preds = %732
  %735 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %736 unwind label %1279

; <label>:736:                                    ; preds = %734
  %737 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %738 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %3, i64 0, i32 0, i32 0, i32 0
  %739 = load i64*, i64** %738, align 8, !tbaa !19
  %740 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %3, i64 0, i32 0, i32 0, i32 1
  %741 = bitcast i64** %740 to i64*
  %742 = load i64, i64* %741, align 8, !tbaa !22
  %743 = ptrtoint i64* %739 to i64
  %744 = sub i64 %742, %743
  %745 = ashr exact i64 %744, 3
  %746 = icmp eq i64 %744, 0
  br i1 %746, label %754, label %.preheader44

.preheader44:                                     ; preds = %736
  br label %747

; <label>:747:                                    ; preds = %.preheader44, %747
  %748 = phi i64 [ %750, %747 ], [ %745, %.preheader44 ]
  %749 = phi i32 [ %752, %747 ], [ 0, %.preheader44 ]
  %750 = lshr i64 %748, 1
  %751 = icmp eq i64 %750, 0
  %752 = add nuw nsw i32 %749, 1
  br i1 %751, label %753, label %747

; <label>:753:                                    ; preds = %747
  invoke void @_Z11pdqsort_recPmmmib(i64* %739, i64 0, i64 %745, i32 %749, i1 zeroext true)
          to label %754 unwind label %1279

; <label>:754:                                    ; preds = %753, %736
  %755 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %756 = sub nsw i64 %755, %737
  %757 = sitofp i64 %756 to double
  %758 = fdiv double %757, 1.000000e+09
  %759 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %758)
          to label %760 unwind label %1279

; <label>:760:                                    ; preds = %754
  %761 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %762 unwind label %1279

; <label>:762:                                    ; preds = %760
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %3)
          to label %763 unwind label %1279

; <label>:763:                                    ; preds = %762
  %764 = load i64*, i64** %738, align 8, !tbaa !19
  %765 = icmp eq i64* %764, null
  br i1 %765, label %768, label %766

; <label>:766:                                    ; preds = %763
  %767 = bitcast i64* %764 to i8*
  call void @_ZdlPv(i8* %767) #2
  br label %768

; <label>:768:                                    ; preds = %766, %763
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %733) #2
  %769 = bitcast %"class.std::vector"* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %769) #2
  invoke void @_ZN13Int_Generator10random_dupEmm(%"class.std::vector"* nonnull sret %4, i64 10000000, i64 10000)
          to label %770 unwind label %1386

; <label>:770:                                    ; preds = %768
  %771 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %772 unwind label %1289

; <label>:772:                                    ; preds = %770
  %773 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %774 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %775 = load i64*, i64** %774, align 8, !tbaa !19
  %776 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %777 = bitcast i64** %776 to i64*
  %778 = load i64, i64* %777, align 8, !tbaa !22
  %779 = ptrtoint i64* %775 to i64
  %780 = sub i64 %778, %779
  %781 = ashr exact i64 %780, 3
  %782 = icmp eq i64 %780, 0
  br i1 %782, label %790, label %.preheader43

.preheader43:                                     ; preds = %772
  br label %783

; <label>:783:                                    ; preds = %.preheader43, %783
  %784 = phi i64 [ %786, %783 ], [ %781, %.preheader43 ]
  %785 = phi i32 [ %788, %783 ], [ 0, %.preheader43 ]
  %786 = lshr i64 %784, 1
  %787 = icmp eq i64 %786, 0
  %788 = add nuw nsw i32 %785, 1
  br i1 %787, label %789, label %783

; <label>:789:                                    ; preds = %783
  invoke void @_Z11pdqsort_recPmmmib(i64* %775, i64 0, i64 %781, i32 %785, i1 zeroext true)
          to label %790 unwind label %1289

; <label>:790:                                    ; preds = %789, %772
  %791 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %792 = sub nsw i64 %791, %773
  %793 = sitofp i64 %792 to double
  %794 = fdiv double %793, 1.000000e+09
  %795 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %794)
          to label %796 unwind label %1289

; <label>:796:                                    ; preds = %790
  %797 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %798 unwind label %1289

; <label>:798:                                    ; preds = %796
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %4)
          to label %799 unwind label %1289

; <label>:799:                                    ; preds = %798
  %800 = load i64*, i64** %774, align 8, !tbaa !19
  %801 = icmp eq i64* %800, null
  br i1 %801, label %804, label %802

; <label>:802:                                    ; preds = %799
  %803 = bitcast i64* %800 to i8*
  call void @_ZdlPv(i8* %803) #2
  br label %804

; <label>:804:                                    ; preds = %802, %799
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %769) #2
  %805 = bitcast %"class.std::vector"* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %805) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %805, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !33
  %806 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %5, i64 0, i32 0, i32 0, i32 2
  %807 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %5, i64 0, i32 0, i32 0, i32 1
  %808 = invoke i8* @_Znwm(i64 800000000)
          to label %809 unwind label %818, !noalias !33

; <label>:809:                                    ; preds = %804
  %810 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %5, i64 0, i32 0, i32 0, i32 0
  %811 = bitcast %"class.std::vector"* %5 to i8**
  store i8* %808, i8** %811, align 8, !tbaa !19, !alias.scope !33
  %812 = getelementptr inbounds i8, i8* %808, i64 800000000
  %813 = bitcast i64** %806 to i8**
  store i8* %812, i8** %813, align 8, !tbaa !28, !alias.scope !33
  %814 = ptrtoint i8* %808 to i64
  %815 = bitcast i64** %807 to i64*
  store i64 %814, i64* %815, align 8, !tbaa !22, !alias.scope !33
  %816 = bitcast i8* %808 to i64*
  %817 = bitcast i8* %812 to i64*
  br label %822

; <label>:818:                                    ; preds = %804
  %819 = landingpad { i8*, i32 }
          cleanup
  %820 = extractvalue { i8*, i32 } %819, 0
  %821 = extractvalue { i8*, i32 } %819, 1
  br label %900

; <label>:822:                                    ; preds = %882, %809
  %823 = phi i64 [ %814, %809 ], [ %883, %882 ]
  %824 = phi i64* [ %817, %809 ], [ %884, %882 ]
  %825 = phi i64* [ %816, %809 ], [ %885, %882 ]
  %826 = phi i64 [ 0, %809 ], [ %886, %882 ]
  %827 = icmp eq i64* %825, %824
  %828 = ptrtoint i64* %825 to i64
  br i1 %827, label %831, label %829

; <label>:829:                                    ; preds = %822
  store i64 %826, i64* %825, align 8, !tbaa !2
  %830 = getelementptr inbounds i64, i64* %825, i64 1
  store i64* %830, i64** %807, align 8, !tbaa !22
  br label %882

; <label>:831:                                    ; preds = %822
  %832 = sub i64 %828, %823
  %833 = ashr exact i64 %832, 3
  %834 = icmp eq i64 %832, 0
  %835 = select i1 %834, i64 1, i64 %833
  %836 = add nsw i64 %835, %833
  %837 = icmp ult i64 %836, %833
  %838 = icmp ugt i64 %836, 2305843009213693951
  %839 = or i1 %837, %838
  %840 = select i1 %839, i64 2305843009213693951, i64 %836
  %841 = icmp eq i64 %840, 0
  %842 = inttoptr i64 %823 to i64*
  br i1 %841, label %853, label %843

; <label>:843:                                    ; preds = %831
  %844 = icmp ugt i64 %840, 2305843009213693951
  br i1 %844, label %845, label %847

; <label>:845:                                    ; preds = %843
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %846 unwind label %890

; <label>:846:                                    ; preds = %845
  unreachable

; <label>:847:                                    ; preds = %843
  %848 = shl i64 %840, 3
  %849 = invoke i8* @_Znwm(i64 %848)
          to label %850 unwind label %888

; <label>:850:                                    ; preds = %847
  %851 = bitcast i8* %849 to i64*
  %852 = load i64*, i64** %810, align 8, !tbaa !19
  br label %853

; <label>:853:                                    ; preds = %850, %831
  %854 = phi i64* [ %852, %850 ], [ %842, %831 ]
  %855 = phi i8* [ %849, %850 ], [ null, %831 ]
  %856 = phi i64* [ %851, %850 ], [ null, %831 ]
  %857 = getelementptr inbounds i64, i64* %856, i64 %833
  store i64 %826, i64* %857, align 8, !tbaa !2
  %858 = ptrtoint i64* %854 to i64
  %859 = sub i64 %828, %858
  %860 = ashr exact i64 %859, 3
  %861 = icmp eq i64 %859, 0
  br i1 %861, label %864, label %862

; <label>:862:                                    ; preds = %853
  %863 = bitcast i64* %854 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %855, i8* %863, i64 %859, i32 8, i1 false) #2
  br label %864

; <label>:864:                                    ; preds = %862, %853
  %865 = getelementptr inbounds i64, i64* %856, i64 %860
  %866 = getelementptr inbounds i64, i64* %865, i64 1
  %867 = load i64, i64* %815, align 8, !tbaa !22
  %868 = sub i64 %867, %828
  %869 = ashr exact i64 %868, 3
  %870 = icmp eq i64 %868, 0
  br i1 %870, label %874, label %871

; <label>:871:                                    ; preds = %864
  %872 = bitcast i64* %866 to i8*
  %873 = bitcast i64* %824 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %872, i8* %873, i64 %868, i32 8, i1 false) #2
  br label %874

; <label>:874:                                    ; preds = %871, %864
  %875 = getelementptr inbounds i64, i64* %866, i64 %869
  %876 = icmp eq i64* %854, null
  br i1 %876, label %879, label %877

; <label>:877:                                    ; preds = %874
  %878 = bitcast i64* %854 to i8*
  call void @_ZdlPv(i8* %878) #2
  br label %879

; <label>:879:                                    ; preds = %877, %874
  store i8* %855, i8** %811, align 8, !tbaa !19
  store i64* %875, i64** %807, align 8, !tbaa !22
  %880 = getelementptr inbounds i64, i64* %856, i64 %840
  store i64* %880, i64** %806, align 8, !tbaa !28
  %881 = ptrtoint i8* %855 to i64
  br label %882

; <label>:882:                                    ; preds = %879, %829
  %883 = phi i64 [ %881, %879 ], [ %823, %829 ]
  %884 = phi i64* [ %880, %879 ], [ %824, %829 ]
  %885 = phi i64* [ %875, %879 ], [ %830, %829 ]
  %886 = add nuw nsw i64 %826, 1
  %887 = icmp ult i64 %886, 100000000
  br i1 %887, label %822, label %905

; <label>:888:                                    ; preds = %847
  %889 = landingpad { i8*, i32 }
          cleanup
  br label %892

; <label>:890:                                    ; preds = %845
  %891 = landingpad { i8*, i32 }
          cleanup
  br label %892

; <label>:892:                                    ; preds = %890, %888
  %893 = phi { i8*, i32 } [ %889, %888 ], [ %891, %890 ]
  %894 = extractvalue { i8*, i32 } %893, 0
  %895 = extractvalue { i8*, i32 } %893, 1
  %896 = load i64*, i64** %810, align 8, !tbaa !19, !alias.scope !33
  %897 = icmp eq i64* %896, null
  br i1 %897, label %900, label %898

; <label>:898:                                    ; preds = %892
  %899 = bitcast i64* %896 to i8*
  call void @_ZdlPv(i8* %899) #2
  br label %900

; <label>:900:                                    ; preds = %898, %892, %818
  %901 = phi i32 [ %821, %818 ], [ %895, %898 ], [ %895, %892 ]
  %902 = phi i8* [ %820, %818 ], [ %894, %898 ], [ %894, %892 ]
  %903 = insertvalue { i8*, i32 } undef, i8* %902, 0
  %904 = insertvalue { i8*, i32 } %903, i32 %901, 1
  br label %1388

; <label>:905:                                    ; preds = %882
  %906 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %907 unwind label %1299

; <label>:907:                                    ; preds = %905
  %908 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %909 = load i64*, i64** %810, align 8, !tbaa !19
  %910 = load i64, i64* %815, align 8, !tbaa !22
  %911 = ptrtoint i64* %909 to i64
  %912 = sub i64 %910, %911
  %913 = ashr exact i64 %912, 3
  %914 = icmp eq i64 %912, 0
  br i1 %914, label %922, label %.preheader42

.preheader42:                                     ; preds = %907
  br label %915

; <label>:915:                                    ; preds = %.preheader42, %915
  %916 = phi i64 [ %918, %915 ], [ %913, %.preheader42 ]
  %917 = phi i32 [ %920, %915 ], [ 0, %.preheader42 ]
  %918 = lshr i64 %916, 1
  %919 = icmp eq i64 %918, 0
  %920 = add nuw nsw i32 %917, 1
  br i1 %919, label %921, label %915

; <label>:921:                                    ; preds = %915
  invoke void @_Z11pdqsort_recPmmmib(i64* %909, i64 0, i64 %913, i32 %917, i1 zeroext true)
          to label %922 unwind label %1299

; <label>:922:                                    ; preds = %921, %907
  %923 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %924 = sub nsw i64 %923, %908
  %925 = sitofp i64 %924 to double
  %926 = fdiv double %925, 1.000000e+09
  %927 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %926)
          to label %928 unwind label %1299

; <label>:928:                                    ; preds = %922
  %929 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %930 unwind label %1299

; <label>:930:                                    ; preds = %928
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %5)
          to label %931 unwind label %1299

; <label>:931:                                    ; preds = %930
  %932 = load i64*, i64** %810, align 8, !tbaa !19
  %933 = icmp eq i64* %932, null
  br i1 %933, label %936, label %934

; <label>:934:                                    ; preds = %931
  %935 = bitcast i64* %932 to i8*
  call void @_ZdlPv(i8* %935) #2
  br label %936

; <label>:936:                                    ; preds = %934, %931
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %805) #2
  %937 = bitcast %"class.std::vector"* %6 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %937) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %6, i64 10000000, i64 100000)
          to label %938 unwind label %1386

; <label>:938:                                    ; preds = %936
  %939 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %940 unwind label %1308

; <label>:940:                                    ; preds = %938
  %941 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %942 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %6, i64 0, i32 0, i32 0, i32 0
  %943 = load i64*, i64** %942, align 8, !tbaa !19
  %944 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %6, i64 0, i32 0, i32 0, i32 1
  %945 = bitcast i64** %944 to i64*
  %946 = load i64, i64* %945, align 8, !tbaa !22
  %947 = ptrtoint i64* %943 to i64
  %948 = sub i64 %946, %947
  %949 = ashr exact i64 %948, 3
  %950 = icmp eq i64 %948, 0
  br i1 %950, label %958, label %.preheader41

.preheader41:                                     ; preds = %940
  br label %951

; <label>:951:                                    ; preds = %.preheader41, %951
  %952 = phi i64 [ %954, %951 ], [ %949, %.preheader41 ]
  %953 = phi i32 [ %956, %951 ], [ 0, %.preheader41 ]
  %954 = lshr i64 %952, 1
  %955 = icmp eq i64 %954, 0
  %956 = add nuw nsw i32 %953, 1
  br i1 %955, label %957, label %951

; <label>:957:                                    ; preds = %951
  invoke void @_Z11pdqsort_recPmmmib(i64* %943, i64 0, i64 %949, i32 %953, i1 zeroext true)
          to label %958 unwind label %1308

; <label>:958:                                    ; preds = %957, %940
  %959 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %960 = sub nsw i64 %959, %941
  %961 = sitofp i64 %960 to double
  %962 = fdiv double %961, 1.000000e+09
  %963 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %962)
          to label %964 unwind label %1308

; <label>:964:                                    ; preds = %958
  %965 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %966 unwind label %1308

; <label>:966:                                    ; preds = %964
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %6)
          to label %967 unwind label %1308

; <label>:967:                                    ; preds = %966
  %968 = load i64*, i64** %942, align 8, !tbaa !19
  %969 = icmp eq i64* %968, null
  br i1 %969, label %972, label %970

; <label>:970:                                    ; preds = %967
  %971 = bitcast i64* %968 to i8*
  call void @_ZdlPv(i8* %971) #2
  br label %972

; <label>:972:                                    ; preds = %970, %967
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %937) #2
  %973 = bitcast %"class.std::vector"* %7 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %973) #2
  invoke void @_ZN13Int_Generator10sorted_endEmm(%"class.std::vector"* nonnull sret %7, i64 10000000, i64 1000000)
          to label %974 unwind label %1386

; <label>:974:                                    ; preds = %972
  %975 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %976 unwind label %1318

; <label>:976:                                    ; preds = %974
  %977 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %978 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %7, i64 0, i32 0, i32 0, i32 0
  %979 = load i64*, i64** %978, align 8, !tbaa !19
  %980 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %7, i64 0, i32 0, i32 0, i32 1
  %981 = bitcast i64** %980 to i64*
  %982 = load i64, i64* %981, align 8, !tbaa !22
  %983 = ptrtoint i64* %979 to i64
  %984 = sub i64 %982, %983
  %985 = ashr exact i64 %984, 3
  %986 = icmp eq i64 %984, 0
  br i1 %986, label %994, label %.preheader40

.preheader40:                                     ; preds = %976
  br label %987

; <label>:987:                                    ; preds = %.preheader40, %987
  %988 = phi i64 [ %990, %987 ], [ %985, %.preheader40 ]
  %989 = phi i32 [ %992, %987 ], [ 0, %.preheader40 ]
  %990 = lshr i64 %988, 1
  %991 = icmp eq i64 %990, 0
  %992 = add nuw nsw i32 %989, 1
  br i1 %991, label %993, label %987

; <label>:993:                                    ; preds = %987
  invoke void @_Z11pdqsort_recPmmmib(i64* %979, i64 0, i64 %985, i32 %989, i1 zeroext true)
          to label %994 unwind label %1318

; <label>:994:                                    ; preds = %993, %976
  %995 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %996 = sub nsw i64 %995, %977
  %997 = sitofp i64 %996 to double
  %998 = fdiv double %997, 1.000000e+09
  %999 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %998)
          to label %1000 unwind label %1318

; <label>:1000:                                   ; preds = %994
  %1001 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1002 unwind label %1318

; <label>:1002:                                   ; preds = %1000
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %7)
          to label %1003 unwind label %1318

; <label>:1003:                                   ; preds = %1002
  %1004 = load i64*, i64** %978, align 8, !tbaa !19
  %1005 = icmp eq i64* %1004, null
  br i1 %1005, label %1008, label %1006

; <label>:1006:                                   ; preds = %1003
  %1007 = bitcast i64* %1004 to i8*
  call void @_ZdlPv(i8* %1007) #2
  br label %1008

; <label>:1008:                                   ; preds = %1006, %1003
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %973) #2
  %1009 = bitcast %"class.std::vector"* %8 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1009) #2
  invoke void @_ZN13Int_Generator13sorted_middleEmm(%"class.std::vector"* nonnull sret %8, i64 10000000, i64 1000000)
          to label %1010 unwind label %1386

; <label>:1010:                                   ; preds = %1008
  %1011 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1012 unwind label %1328

; <label>:1012:                                   ; preds = %1010
  %1013 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1014 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %8, i64 0, i32 0, i32 0, i32 0
  %1015 = load i64*, i64** %1014, align 8, !tbaa !19
  %1016 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %8, i64 0, i32 0, i32 0, i32 1
  %1017 = bitcast i64** %1016 to i64*
  %1018 = load i64, i64* %1017, align 8, !tbaa !22
  %1019 = ptrtoint i64* %1015 to i64
  %1020 = sub i64 %1018, %1019
  %1021 = ashr exact i64 %1020, 3
  %1022 = icmp eq i64 %1020, 0
  br i1 %1022, label %1030, label %.preheader39

.preheader39:                                     ; preds = %1012
  br label %1023

; <label>:1023:                                   ; preds = %.preheader39, %1023
  %1024 = phi i64 [ %1026, %1023 ], [ %1021, %.preheader39 ]
  %1025 = phi i32 [ %1028, %1023 ], [ 0, %.preheader39 ]
  %1026 = lshr i64 %1024, 1
  %1027 = icmp eq i64 %1026, 0
  %1028 = add nuw nsw i32 %1025, 1
  br i1 %1027, label %1029, label %1023

; <label>:1029:                                   ; preds = %1023
  invoke void @_Z11pdqsort_recPmmmib(i64* %1015, i64 0, i64 %1021, i32 %1025, i1 zeroext true)
          to label %1030 unwind label %1328

; <label>:1030:                                   ; preds = %1029, %1012
  %1031 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1032 = sub nsw i64 %1031, %1013
  %1033 = sitofp i64 %1032 to double
  %1034 = fdiv double %1033, 1.000000e+09
  %1035 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1034)
          to label %1036 unwind label %1328

; <label>:1036:                                   ; preds = %1030
  %1037 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1038 unwind label %1328

; <label>:1038:                                   ; preds = %1036
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %8)
          to label %1039 unwind label %1328

; <label>:1039:                                   ; preds = %1038
  %1040 = load i64*, i64** %1014, align 8, !tbaa !19
  %1041 = icmp eq i64* %1040, null
  br i1 %1041, label %1044, label %1042

; <label>:1042:                                   ; preds = %1039
  %1043 = bitcast i64* %1040 to i8*
  call void @_ZdlPv(i8* %1043) #2
  br label %1044

; <label>:1044:                                   ; preds = %1042, %1039
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1009) #2
  %1045 = bitcast %"class.std::vector"* %9 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1045) #2
  call void @llvm.memset.p0i8.i64(i8* nonnull %1045, i8 0, i64 24, i32 8, i1 false) #2, !alias.scope !36
  %1046 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %9, i64 0, i32 0, i32 0, i32 2
  %1047 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %9, i64 0, i32 0, i32 0, i32 1
  %1048 = invoke i8* @_Znwm(i64 800000000)
          to label %1049 unwind label %1058, !noalias !36

; <label>:1049:                                   ; preds = %1044
  %1050 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %9, i64 0, i32 0, i32 0, i32 0
  %1051 = bitcast %"class.std::vector"* %9 to i8**
  store i8* %1048, i8** %1051, align 8, !tbaa !19, !alias.scope !36
  %1052 = getelementptr inbounds i8, i8* %1048, i64 800000000
  %1053 = bitcast i64** %1046 to i8**
  store i8* %1052, i8** %1053, align 8, !tbaa !28, !alias.scope !36
  %1054 = ptrtoint i8* %1048 to i64
  %1055 = bitcast i64** %1047 to i64*
  store i64 %1054, i64* %1055, align 8, !tbaa !22, !alias.scope !36
  %1056 = bitcast i8* %1048 to i64*
  %1057 = bitcast i8* %1052 to i64*
  br label %1062

; <label>:1058:                                   ; preds = %1044
  %1059 = landingpad { i8*, i32 }
          cleanup
  %1060 = extractvalue { i8*, i32 } %1059, 0
  %1061 = extractvalue { i8*, i32 } %1059, 1
  br label %1140

; <label>:1062:                                   ; preds = %1122, %1049
  %1063 = phi i64 [ %1054, %1049 ], [ %1123, %1122 ]
  %1064 = phi i64* [ %1057, %1049 ], [ %1124, %1122 ]
  %1065 = phi i64* [ %1056, %1049 ], [ %1125, %1122 ]
  %1066 = phi i64 [ 100000000, %1049 ], [ %1126, %1122 ]
  %1067 = icmp eq i64* %1065, %1064
  %1068 = ptrtoint i64* %1065 to i64
  br i1 %1067, label %1071, label %1069

; <label>:1069:                                   ; preds = %1062
  store i64 %1066, i64* %1065, align 8, !tbaa !2
  %1070 = getelementptr inbounds i64, i64* %1065, i64 1
  store i64* %1070, i64** %1047, align 8, !tbaa !22
  br label %1122

; <label>:1071:                                   ; preds = %1062
  %1072 = sub i64 %1068, %1063
  %1073 = ashr exact i64 %1072, 3
  %1074 = icmp eq i64 %1072, 0
  %1075 = select i1 %1074, i64 1, i64 %1073
  %1076 = add nsw i64 %1075, %1073
  %1077 = icmp ult i64 %1076, %1073
  %1078 = icmp ugt i64 %1076, 2305843009213693951
  %1079 = or i1 %1077, %1078
  %1080 = select i1 %1079, i64 2305843009213693951, i64 %1076
  %1081 = icmp eq i64 %1080, 0
  %1082 = inttoptr i64 %1063 to i64*
  br i1 %1081, label %1093, label %1083

; <label>:1083:                                   ; preds = %1071
  %1084 = icmp ugt i64 %1080, 2305843009213693951
  br i1 %1084, label %1085, label %1087

; <label>:1085:                                   ; preds = %1083
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %1086 unwind label %1130

; <label>:1086:                                   ; preds = %1085
  unreachable

; <label>:1087:                                   ; preds = %1083
  %1088 = shl i64 %1080, 3
  %1089 = invoke i8* @_Znwm(i64 %1088)
          to label %1090 unwind label %1128

; <label>:1090:                                   ; preds = %1087
  %1091 = bitcast i8* %1089 to i64*
  %1092 = load i64*, i64** %1050, align 8, !tbaa !19
  br label %1093

; <label>:1093:                                   ; preds = %1090, %1071
  %1094 = phi i64* [ %1092, %1090 ], [ %1082, %1071 ]
  %1095 = phi i8* [ %1089, %1090 ], [ null, %1071 ]
  %1096 = phi i64* [ %1091, %1090 ], [ null, %1071 ]
  %1097 = getelementptr inbounds i64, i64* %1096, i64 %1073
  store i64 %1066, i64* %1097, align 8, !tbaa !2
  %1098 = ptrtoint i64* %1094 to i64
  %1099 = sub i64 %1068, %1098
  %1100 = ashr exact i64 %1099, 3
  %1101 = icmp eq i64 %1099, 0
  br i1 %1101, label %1104, label %1102

; <label>:1102:                                   ; preds = %1093
  %1103 = bitcast i64* %1094 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %1095, i8* %1103, i64 %1099, i32 8, i1 false) #2
  br label %1104

; <label>:1104:                                   ; preds = %1102, %1093
  %1105 = getelementptr inbounds i64, i64* %1096, i64 %1100
  %1106 = getelementptr inbounds i64, i64* %1105, i64 1
  %1107 = load i64, i64* %1055, align 8, !tbaa !22
  %1108 = sub i64 %1107, %1068
  %1109 = ashr exact i64 %1108, 3
  %1110 = icmp eq i64 %1108, 0
  br i1 %1110, label %1114, label %1111

; <label>:1111:                                   ; preds = %1104
  %1112 = bitcast i64* %1106 to i8*
  %1113 = bitcast i64* %1064 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %1112, i8* %1113, i64 %1108, i32 8, i1 false) #2
  br label %1114

; <label>:1114:                                   ; preds = %1111, %1104
  %1115 = getelementptr inbounds i64, i64* %1106, i64 %1109
  %1116 = icmp eq i64* %1094, null
  br i1 %1116, label %1119, label %1117

; <label>:1117:                                   ; preds = %1114
  %1118 = bitcast i64* %1094 to i8*
  call void @_ZdlPv(i8* %1118) #2
  br label %1119

; <label>:1119:                                   ; preds = %1117, %1114
  store i8* %1095, i8** %1051, align 8, !tbaa !19
  store i64* %1115, i64** %1047, align 8, !tbaa !22
  %1120 = getelementptr inbounds i64, i64* %1096, i64 %1080
  store i64* %1120, i64** %1046, align 8, !tbaa !28
  %1121 = ptrtoint i8* %1095 to i64
  br label %1122

; <label>:1122:                                   ; preds = %1119, %1069
  %1123 = phi i64 [ %1121, %1119 ], [ %1063, %1069 ]
  %1124 = phi i64* [ %1120, %1119 ], [ %1064, %1069 ]
  %1125 = phi i64* [ %1115, %1119 ], [ %1070, %1069 ]
  %1126 = add nsw i64 %1066, -1
  %1127 = icmp eq i64 %1126, 0
  br i1 %1127, label %1145, label %1062

; <label>:1128:                                   ; preds = %1087
  %1129 = landingpad { i8*, i32 }
          cleanup
  br label %1132

; <label>:1130:                                   ; preds = %1085
  %1131 = landingpad { i8*, i32 }
          cleanup
  br label %1132

; <label>:1132:                                   ; preds = %1130, %1128
  %1133 = phi { i8*, i32 } [ %1129, %1128 ], [ %1131, %1130 ]
  %1134 = extractvalue { i8*, i32 } %1133, 0
  %1135 = extractvalue { i8*, i32 } %1133, 1
  %1136 = load i64*, i64** %1050, align 8, !tbaa !19, !alias.scope !36
  %1137 = icmp eq i64* %1136, null
  br i1 %1137, label %1140, label %1138

; <label>:1138:                                   ; preds = %1132
  %1139 = bitcast i64* %1136 to i8*
  call void @_ZdlPv(i8* %1139) #2
  br label %1140

; <label>:1140:                                   ; preds = %1138, %1132, %1058
  %1141 = phi i32 [ %1061, %1058 ], [ %1135, %1138 ], [ %1135, %1132 ]
  %1142 = phi i8* [ %1060, %1058 ], [ %1134, %1138 ], [ %1134, %1132 ]
  %1143 = insertvalue { i8*, i32 } undef, i8* %1142, 0
  %1144 = insertvalue { i8*, i32 } %1143, i32 %1141, 1
  br label %1388

; <label>:1145:                                   ; preds = %1122
  %1146 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1147 unwind label %1338

; <label>:1147:                                   ; preds = %1145
  %1148 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1149 = load i64*, i64** %1050, align 8, !tbaa !19
  %1150 = load i64, i64* %1055, align 8, !tbaa !22
  %1151 = ptrtoint i64* %1149 to i64
  %1152 = sub i64 %1150, %1151
  %1153 = ashr exact i64 %1152, 3
  %1154 = icmp eq i64 %1152, 0
  br i1 %1154, label %1162, label %.preheader38

.preheader38:                                     ; preds = %1147
  br label %1155

; <label>:1155:                                   ; preds = %.preheader38, %1155
  %1156 = phi i64 [ %1158, %1155 ], [ %1153, %.preheader38 ]
  %1157 = phi i32 [ %1160, %1155 ], [ 0, %.preheader38 ]
  %1158 = lshr i64 %1156, 1
  %1159 = icmp eq i64 %1158, 0
  %1160 = add nuw nsw i32 %1157, 1
  br i1 %1159, label %1161, label %1155

; <label>:1161:                                   ; preds = %1155
  invoke void @_Z11pdqsort_recPmmmib(i64* %1149, i64 0, i64 %1153, i32 %1157, i1 zeroext true)
          to label %1162 unwind label %1338

; <label>:1162:                                   ; preds = %1161, %1147
  %1163 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1164 = sub nsw i64 %1163, %1148
  %1165 = sitofp i64 %1164 to double
  %1166 = fdiv double %1165, 1.000000e+09
  %1167 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1166)
          to label %1168 unwind label %1338

; <label>:1168:                                   ; preds = %1162
  %1169 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1170 unwind label %1338

; <label>:1170:                                   ; preds = %1168
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %9)
          to label %1171 unwind label %1338

; <label>:1171:                                   ; preds = %1170
  %1172 = load i64*, i64** %1050, align 8, !tbaa !19
  %1173 = icmp eq i64* %1172, null
  br i1 %1173, label %1176, label %1174

; <label>:1174:                                   ; preds = %1171
  %1175 = bitcast i64* %1172 to i8*
  call void @_ZdlPv(i8* %1175) #2
  br label %1176

; <label>:1176:                                   ; preds = %1174, %1171
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1045) #2
  %1177 = bitcast %"class.std::vector"* %10 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1177) #2
  invoke void @_ZN13Int_Generator18reverse_sorted_endEmm(%"class.std::vector"* nonnull sret %10, i64 10000000, i64 1000000)
          to label %1178 unwind label %1386

; <label>:1178:                                   ; preds = %1176
  %1179 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1180 unwind label %1347

; <label>:1180:                                   ; preds = %1178
  %1181 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1182 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %10, i64 0, i32 0, i32 0, i32 0
  %1183 = load i64*, i64** %1182, align 8, !tbaa !19
  %1184 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %10, i64 0, i32 0, i32 0, i32 1
  %1185 = bitcast i64** %1184 to i64*
  %1186 = load i64, i64* %1185, align 8, !tbaa !22
  %1187 = ptrtoint i64* %1183 to i64
  %1188 = sub i64 %1186, %1187
  %1189 = ashr exact i64 %1188, 3
  %1190 = icmp eq i64 %1188, 0
  br i1 %1190, label %1198, label %.preheader37

.preheader37:                                     ; preds = %1180
  br label %1191

; <label>:1191:                                   ; preds = %.preheader37, %1191
  %1192 = phi i64 [ %1194, %1191 ], [ %1189, %.preheader37 ]
  %1193 = phi i32 [ %1196, %1191 ], [ 0, %.preheader37 ]
  %1194 = lshr i64 %1192, 1
  %1195 = icmp eq i64 %1194, 0
  %1196 = add nuw nsw i32 %1193, 1
  br i1 %1195, label %1197, label %1191

; <label>:1197:                                   ; preds = %1191
  invoke void @_Z11pdqsort_recPmmmib(i64* %1183, i64 0, i64 %1189, i32 %1193, i1 zeroext true)
          to label %1198 unwind label %1347

; <label>:1198:                                   ; preds = %1197, %1180
  %1199 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1200 = sub nsw i64 %1199, %1181
  %1201 = sitofp i64 %1200 to double
  %1202 = fdiv double %1201, 1.000000e+09
  %1203 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1202)
          to label %1204 unwind label %1347

; <label>:1204:                                   ; preds = %1198
  %1205 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1206 unwind label %1347

; <label>:1206:                                   ; preds = %1204
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %10)
          to label %1207 unwind label %1347

; <label>:1207:                                   ; preds = %1206
  %1208 = load i64*, i64** %1182, align 8, !tbaa !19
  %1209 = icmp eq i64* %1208, null
  br i1 %1209, label %1212, label %1210

; <label>:1210:                                   ; preds = %1207
  %1211 = bitcast i64* %1208 to i8*
  call void @_ZdlPv(i8* %1211) #2
  br label %1212

; <label>:1212:                                   ; preds = %1210, %1207
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1177) #2
  %1213 = bitcast %"class.std::vector"* %11 to i8*
  call void @llvm.lifetime.start.p0i8(i64 24, i8* nonnull %1213) #2
  invoke void @_ZN13Int_Generator21reverse_sorted_middleEmm(%"class.std::vector"* nonnull sret %11, i64 10000000, i64 1000000)
          to label %1214 unwind label %1386

; <label>:1214:                                   ; preds = %1212
  %1215 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([2 x i8], [2 x i8]* @.str.12, i64 0, i64 0), i64 1)
          to label %1216 unwind label %1357

; <label>:1216:                                   ; preds = %1214
  %1217 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1218 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %11, i64 0, i32 0, i32 0, i32 0
  %1219 = load i64*, i64** %1218, align 8, !tbaa !19
  %1220 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %11, i64 0, i32 0, i32 0, i32 1
  %1221 = bitcast i64** %1220 to i64*
  %1222 = load i64, i64* %1221, align 8, !tbaa !22
  %1223 = ptrtoint i64* %1219 to i64
  %1224 = sub i64 %1222, %1223
  %1225 = ashr exact i64 %1224, 3
  %1226 = icmp eq i64 %1224, 0
  br i1 %1226, label %1234, label %.preheader

.preheader:                                       ; preds = %1216
  br label %1227

; <label>:1227:                                   ; preds = %.preheader, %1227
  %1228 = phi i64 [ %1230, %1227 ], [ %1225, %.preheader ]
  %1229 = phi i32 [ %1232, %1227 ], [ 0, %.preheader ]
  %1230 = lshr i64 %1228, 1
  %1231 = icmp eq i64 %1230, 0
  %1232 = add nuw nsw i32 %1229, 1
  br i1 %1231, label %1233, label %1227

; <label>:1233:                                   ; preds = %1227
  invoke void @_Z11pdqsort_recPmmmib(i64* %1219, i64 0, i64 %1225, i32 %1229, i1 zeroext true)
          to label %1234 unwind label %1357

; <label>:1234:                                   ; preds = %1233, %1216
  %1235 = call i64 @_ZNSt6chrono3_V212steady_clock3nowEv() #2
  %1236 = sub nsw i64 %1235, %1217
  %1237 = sitofp i64 %1236 to double
  %1238 = fdiv double %1237, 1.000000e+09
  %1239 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"* nonnull @_ZSt4cout, double %1238)
          to label %1240 unwind label %1357

; <label>:1240:                                   ; preds = %1234
  %1241 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull @_ZSt4cout)
          to label %1242 unwind label %1357

; <label>:1242:                                   ; preds = %1240
  invoke void @_Z11test_sortedImEvRSt6vectorIT_SaIS1_EE(%"class.std::vector"* nonnull dereferenceable(24) %11)
          to label %1243 unwind label %1357

; <label>:1243:                                   ; preds = %1242
  %1244 = load i64*, i64** %1218, align 8, !tbaa !19
  %1245 = icmp eq i64* %1244, null
  br i1 %1245, label %1248, label %1246

; <label>:1246:                                   ; preds = %1243
  %1247 = bitcast i64* %1244 to i8*
  call void @_ZdlPv(i8* %1247) #2
  br label %1248

; <label>:1248:                                   ; preds = %1246, %1243
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1213) #2
  %1249 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %1250 = getelementptr i8, i8* %1249, i64 -24
  %1251 = bitcast i8* %1250 to i64*
  %1252 = load i64, i64* %1251, align 8
  %1253 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %1252
  %1254 = getelementptr inbounds i8, i8* %1253, i64 240
  %1255 = bitcast i8* %1254 to %"class.std::ctype"**
  %1256 = load %"class.std::ctype"*, %"class.std::ctype"** %1255, align 8, !tbaa !8
  %1257 = icmp eq %"class.std::ctype"* %1256, null
  br i1 %1257, label %1258, label %1260

; <label>:1258:                                   ; preds = %1248
  invoke void @_ZSt16__throw_bad_castv() #16
          to label %1259 unwind label %1386

; <label>:1259:                                   ; preds = %1258
  unreachable

; <label>:1260:                                   ; preds = %1248
  %1261 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %1256, i64 0, i32 8
  %1262 = load i8, i8* %1261, align 8, !tbaa !12
  %1263 = icmp eq i8 %1262, 0
  br i1 %1263, label %1267, label %1264

; <label>:1264:                                   ; preds = %1260
  %1265 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %1256, i64 0, i32 9, i64 10
  %1266 = load i8, i8* %1265, align 1, !tbaa !14
  br label %1274

; <label>:1267:                                   ; preds = %1260
  invoke void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %1256)
          to label %1268 unwind label %1386

; <label>:1268:                                   ; preds = %1267
  %1269 = bitcast %"class.std::ctype"* %1256 to i8 (%"class.std::ctype"*, i8)***
  %1270 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %1269, align 8, !tbaa !6
  %1271 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %1270, i64 6
  %1272 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %1271, align 8
  %1273 = invoke signext i8 %1272(%"class.std::ctype"* nonnull %1256, i8 signext 10)
          to label %1274 unwind label %1386

; <label>:1274:                                   ; preds = %1268, %1264
  %1275 = phi i8 [ %1266, %1264 ], [ %1273, %1268 ]
  %1276 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %1275)
          to label %1277 unwind label %1386

; <label>:1277:                                   ; preds = %1274
  %1278 = invoke dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %1276)
          to label %1372 unwind label %1386

; <label>:1279:                                   ; preds = %762, %760, %754, %753, %734
  %1280 = landingpad { i8*, i32 }
          cleanup
  %1281 = extractvalue { i8*, i32 } %1280, 0
  %1282 = extractvalue { i8*, i32 } %1280, 1
  %1283 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %3, i64 0, i32 0, i32 0, i32 0
  %1284 = load i64*, i64** %1283, align 8, !tbaa !19
  %1285 = icmp eq i64* %1284, null
  br i1 %1285, label %1288, label %1286

; <label>:1286:                                   ; preds = %1279
  %1287 = bitcast i64* %1284 to i8*
  call void @_ZdlPv(i8* %1287) #2
  br label %1288

; <label>:1288:                                   ; preds = %1286, %1279
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %733) #2
  br label %1367

; <label>:1289:                                   ; preds = %798, %796, %790, %789, %770
  %1290 = landingpad { i8*, i32 }
          cleanup
  %1291 = extractvalue { i8*, i32 } %1290, 0
  %1292 = extractvalue { i8*, i32 } %1290, 1
  %1293 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %1294 = load i64*, i64** %1293, align 8, !tbaa !19
  %1295 = icmp eq i64* %1294, null
  br i1 %1295, label %1298, label %1296

; <label>:1296:                                   ; preds = %1289
  %1297 = bitcast i64* %1294 to i8*
  call void @_ZdlPv(i8* %1297) #2
  br label %1298

; <label>:1298:                                   ; preds = %1296, %1289
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %769) #2
  br label %1367

; <label>:1299:                                   ; preds = %930, %928, %922, %921, %905
  %1300 = landingpad { i8*, i32 }
          cleanup
  %1301 = extractvalue { i8*, i32 } %1300, 0
  %1302 = extractvalue { i8*, i32 } %1300, 1
  %1303 = load i64*, i64** %810, align 8, !tbaa !19
  %1304 = icmp eq i64* %1303, null
  br i1 %1304, label %1307, label %1305

; <label>:1305:                                   ; preds = %1299
  %1306 = bitcast i64* %1303 to i8*
  call void @_ZdlPv(i8* %1306) #2
  br label %1307

; <label>:1307:                                   ; preds = %1305, %1299
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %805) #2
  br label %1367

; <label>:1308:                                   ; preds = %966, %964, %958, %957, %938
  %1309 = landingpad { i8*, i32 }
          cleanup
  %1310 = extractvalue { i8*, i32 } %1309, 0
  %1311 = extractvalue { i8*, i32 } %1309, 1
  %1312 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %6, i64 0, i32 0, i32 0, i32 0
  %1313 = load i64*, i64** %1312, align 8, !tbaa !19
  %1314 = icmp eq i64* %1313, null
  br i1 %1314, label %1317, label %1315

; <label>:1315:                                   ; preds = %1308
  %1316 = bitcast i64* %1313 to i8*
  call void @_ZdlPv(i8* %1316) #2
  br label %1317

; <label>:1317:                                   ; preds = %1315, %1308
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %937) #2
  br label %1367

; <label>:1318:                                   ; preds = %1002, %1000, %994, %993, %974
  %1319 = landingpad { i8*, i32 }
          cleanup
  %1320 = extractvalue { i8*, i32 } %1319, 0
  %1321 = extractvalue { i8*, i32 } %1319, 1
  %1322 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %7, i64 0, i32 0, i32 0, i32 0
  %1323 = load i64*, i64** %1322, align 8, !tbaa !19
  %1324 = icmp eq i64* %1323, null
  br i1 %1324, label %1327, label %1325

; <label>:1325:                                   ; preds = %1318
  %1326 = bitcast i64* %1323 to i8*
  call void @_ZdlPv(i8* %1326) #2
  br label %1327

; <label>:1327:                                   ; preds = %1325, %1318
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %973) #2
  br label %1367

; <label>:1328:                                   ; preds = %1038, %1036, %1030, %1029, %1010
  %1329 = landingpad { i8*, i32 }
          cleanup
  %1330 = extractvalue { i8*, i32 } %1329, 0
  %1331 = extractvalue { i8*, i32 } %1329, 1
  %1332 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %8, i64 0, i32 0, i32 0, i32 0
  %1333 = load i64*, i64** %1332, align 8, !tbaa !19
  %1334 = icmp eq i64* %1333, null
  br i1 %1334, label %1337, label %1335

; <label>:1335:                                   ; preds = %1328
  %1336 = bitcast i64* %1333 to i8*
  call void @_ZdlPv(i8* %1336) #2
  br label %1337

; <label>:1337:                                   ; preds = %1335, %1328
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1009) #2
  br label %1367

; <label>:1338:                                   ; preds = %1170, %1168, %1162, %1161, %1145
  %1339 = landingpad { i8*, i32 }
          cleanup
  %1340 = extractvalue { i8*, i32 } %1339, 0
  %1341 = extractvalue { i8*, i32 } %1339, 1
  %1342 = load i64*, i64** %1050, align 8, !tbaa !19
  %1343 = icmp eq i64* %1342, null
  br i1 %1343, label %1346, label %1344

; <label>:1344:                                   ; preds = %1338
  %1345 = bitcast i64* %1342 to i8*
  call void @_ZdlPv(i8* %1345) #2
  br label %1346

; <label>:1346:                                   ; preds = %1344, %1338
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1045) #2
  br label %1367

; <label>:1347:                                   ; preds = %1206, %1204, %1198, %1197, %1178
  %1348 = landingpad { i8*, i32 }
          cleanup
  %1349 = extractvalue { i8*, i32 } %1348, 0
  %1350 = extractvalue { i8*, i32 } %1348, 1
  %1351 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %10, i64 0, i32 0, i32 0, i32 0
  %1352 = load i64*, i64** %1351, align 8, !tbaa !19
  %1353 = icmp eq i64* %1352, null
  br i1 %1353, label %1356, label %1354

; <label>:1354:                                   ; preds = %1347
  %1355 = bitcast i64* %1352 to i8*
  call void @_ZdlPv(i8* %1355) #2
  br label %1356

; <label>:1356:                                   ; preds = %1354, %1347
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1177) #2
  br label %1367

; <label>:1357:                                   ; preds = %1242, %1240, %1234, %1233, %1214
  %1358 = landingpad { i8*, i32 }
          cleanup
  %1359 = extractvalue { i8*, i32 } %1358, 0
  %1360 = extractvalue { i8*, i32 } %1358, 1
  %1361 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %11, i64 0, i32 0, i32 0, i32 0
  %1362 = load i64*, i64** %1361, align 8, !tbaa !19
  %1363 = icmp eq i64* %1362, null
  br i1 %1363, label %1366, label %1364

; <label>:1364:                                   ; preds = %1357
  %1365 = bitcast i64* %1362 to i8*
  call void @_ZdlPv(i8* %1365) #2
  br label %1366

; <label>:1366:                                   ; preds = %1364, %1357
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %1213) #2
  br label %1367

; <label>:1367:                                   ; preds = %1366, %1356, %1346, %1337, %1327, %1317, %1307, %1298, %1288
  %1368 = phi i32 [ %1360, %1366 ], [ %1350, %1356 ], [ %1341, %1346 ], [ %1331, %1337 ], [ %1321, %1327 ], [ %1311, %1317 ], [ %1302, %1307 ], [ %1292, %1298 ], [ %1282, %1288 ]
  %1369 = phi i8* [ %1359, %1366 ], [ %1349, %1356 ], [ %1340, %1346 ], [ %1330, %1337 ], [ %1320, %1327 ], [ %1310, %1317 ], [ %1301, %1307 ], [ %1291, %1298 ], [ %1281, %1288 ]
  %1370 = insertvalue { i8*, i32 } undef, i8* %1369, 0
  %1371 = insertvalue { i8*, i32 } %1370, i32 %1368, 1
  br label %1388

; <label>:1372:                                   ; preds = %1277
  %1373 = load i8*, i8** %726, align 8, !tbaa !32
  %1374 = icmp eq i8* %1373, %723
  br i1 %1374, label %1376, label %1375

; <label>:1375:                                   ; preds = %1372
  call void @_ZdlPv(i8* %1373) #2
  br label %1376

; <label>:1376:                                   ; preds = %1375, %1372
  ret i32 0

; <label>:1377:                                   ; preds = %621, %618, %612, %611, %602, %559, %526, %363, %330, %297, %134, %101, %99, %97, %56
  %1378 = landingpad { i8*, i32 }
          cleanup
  br label %1379

; <label>:1379:                                   ; preds = %1377, %711, %492, %263
  %1380 = phi { i8*, i32 } [ %1378, %1377 ], [ %267, %263 ], [ %496, %492 ], [ %715, %711 ]
  %1381 = extractvalue { i8*, i32 } %1380, 0
  %1382 = extractvalue { i8*, i32 } %1380, 1
  %1383 = load i8*, i8** %62, align 8, !tbaa !32
  %1384 = icmp eq i8* %1383, %59
  br i1 %1384, label %1395, label %1385

; <label>:1385:                                   ; preds = %1379
  call void @_ZdlPv(i8* %1383) #2
  br label %1395

; <label>:1386:                                   ; preds = %1277, %1274, %1268, %1267, %1258, %1212, %1176, %1008, %972, %936, %768, %732, %730, %728, %720
  %1387 = landingpad { i8*, i32 }
          cleanup
  br label %1388

; <label>:1388:                                   ; preds = %1386, %1367, %1140, %900
  %1389 = phi { i8*, i32 } [ %1387, %1386 ], [ %904, %900 ], [ %1144, %1140 ], [ %1371, %1367 ]
  %1390 = extractvalue { i8*, i32 } %1389, 0
  %1391 = extractvalue { i8*, i32 } %1389, 1
  %1392 = load i8*, i8** %726, align 8, !tbaa !32
  %1393 = icmp eq i8* %1392, %723
  br i1 %1393, label %1395, label %1394

; <label>:1394:                                   ; preds = %1388
  call void @_ZdlPv(i8* %1392) #2
  br label %1395

; <label>:1395:                                   ; preds = %1394, %1388, %1385, %1379, %96
  %1396 = phi i8* [ %90, %96 ], [ %1381, %1379 ], [ %1381, %1385 ], [ %1390, %1388 ], [ %1390, %1394 ]
  %1397 = phi i32 [ %91, %96 ], [ %1382, %1379 ], [ %1382, %1385 ], [ %1391, %1388 ], [ %1391, %1394 ]
  %1398 = insertvalue { i8*, i32 } undef, i8* %1396, 0
  %1399 = insertvalue { i8*, i32 } %1398, i32 %1397, 1
  resume { i8*, i32 } %1399
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

; <label>:27:                                     ; preds = %22, %8
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

; <label>:41:                                     ; preds = %40, %36
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

; <label>:63:                                     ; preds = %61, %55
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
  br i1 %6, label %.loopexit, label %7

; <label>:7:                                      ; preds = %1
  %8 = getelementptr inbounds i64, i64* %3, i64 1
  %9 = icmp eq i64* %8, %5
  br i1 %9, label %.loopexit1, label %10

; <label>:10:                                     ; preds = %7
  %11 = load i64, i64* %3, align 8, !tbaa !2
  br label %15

; <label>:12:                                     ; preds = %15
  %13 = getelementptr inbounds i64, i64* %17, i64 1
  %14 = icmp eq i64* %13, %5
  br i1 %14, label %.loopexit1, label %15

; <label>:15:                                     ; preds = %12, %10
  %16 = phi i64 [ %11, %10 ], [ %18, %12 ]
  %17 = phi i64* [ %8, %10 ], [ %13, %12 ]
  %18 = load i64, i64* %17, align 8, !tbaa !2
  %19 = icmp ult i64 %18, %16
  br i1 %19, label %.loopexit, label %12

.loopexit:                                        ; preds = %15, %1
  %20 = phi i64* [ %3, %1 ], [ %17, %15 ]
  %21 = icmp eq i64* %20, %5
  br i1 %21, label %.loopexit1, label %22

; <label>:22:                                     ; preds = %.loopexit
  %23 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l(%"class.std::basic_ostream"* nonnull dereferenceable(272) @_ZSt4cout, i8* nonnull getelementptr inbounds ([20 x i8], [20 x i8]* @.str.10, i64 0, i64 0), i64 19)
  %24 = load i8*, i8** bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8**), align 8, !tbaa !6
  %25 = getelementptr i8, i8* %24, i64 -24
  %26 = bitcast i8* %25 to i64*
  %27 = load i64, i64* %26, align 8
  %28 = getelementptr inbounds i8, i8* bitcast (%"class.std::basic_ostream"* @_ZSt4cout to i8*), i64 %27
  %29 = getelementptr inbounds i8, i8* %28, i64 240
  %30 = bitcast i8* %29 to %"class.std::ctype"**
  %31 = load %"class.std::ctype"*, %"class.std::ctype"** %30, align 8, !tbaa !8
  %32 = icmp eq %"class.std::ctype"* %31, null
  br i1 %32, label %33, label %34

; <label>:33:                                     ; preds = %22
  tail call void @_ZSt16__throw_bad_castv() #16
  unreachable

; <label>:34:                                     ; preds = %22
  %35 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %31, i64 0, i32 8
  %36 = load i8, i8* %35, align 8, !tbaa !12
  %37 = icmp eq i8 %36, 0
  br i1 %37, label %41, label %38

; <label>:38:                                     ; preds = %34
  %39 = getelementptr inbounds %"class.std::ctype", %"class.std::ctype"* %31, i64 0, i32 9, i64 10
  %40 = load i8, i8* %39, align 1, !tbaa !14
  br label %47

; <label>:41:                                     ; preds = %34
  tail call void @_ZNKSt5ctypeIcE13_M_widen_initEv(%"class.std::ctype"* nonnull %31)
  %42 = bitcast %"class.std::ctype"* %31 to i8 (%"class.std::ctype"*, i8)***
  %43 = load i8 (%"class.std::ctype"*, i8)**, i8 (%"class.std::ctype"*, i8)*** %42, align 8, !tbaa !6
  %44 = getelementptr inbounds i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %43, i64 6
  %45 = load i8 (%"class.std::ctype"*, i8)*, i8 (%"class.std::ctype"*, i8)** %44, align 8
  %46 = tail call signext i8 %45(%"class.std::ctype"* nonnull %31, i8 signext 10)
  br label %47

; <label>:47:                                     ; preds = %41, %38
  %48 = phi i8 [ %40, %38 ], [ %46, %41 ]
  %49 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo3putEc(%"class.std::basic_ostream"* nonnull @_ZSt4cout, i8 signext %48)
  %50 = tail call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo5flushEv(%"class.std::basic_ostream"* nonnull %49)
  br label %.loopexit1

.loopexit1:                                       ; preds = %12, %47, %.loopexit, %7
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
          to label %143 unwind label %32

; <label>:28:                                     ; preds = %40
  %29 = landingpad { i8*, i32 }
          cleanup
  %30 = extractvalue { i8*, i32 } %29, 0
  %31 = extractvalue { i8*, i32 } %29, 1
  br label %138

; <label>:32:                                     ; preds = %27
  %33 = landingpad { i8*, i32 }
          cleanup
  %34 = extractvalue { i8*, i32 } %33, 0
  %35 = extractvalue { i8*, i32 } %33, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %23) #2
  br label %138

; <label>:36:                                     ; preds = %20
  %37 = landingpad { i8*, i32 }
          cleanup
  %38 = extractvalue { i8*, i32 } %37, 0
  %39 = extractvalue { i8*, i32 } %37, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %23) #2
  call void @__cxa_free_exception(i8* %21) #2
  br label %138

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
          to label %143 unwind label %61

; <label>:57:                                     ; preds = %43
  %58 = landingpad { i8*, i32 }
          cleanup
  %59 = extractvalue { i8*, i32 } %58, 0
  %60 = extractvalue { i8*, i32 } %58, 1
  br label %138

; <label>:61:                                     ; preds = %56
  %62 = landingpad { i8*, i32 }
          cleanup
  %63 = extractvalue { i8*, i32 } %62, 0
  %64 = extractvalue { i8*, i32 } %62, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %52) #2
  br label %138

; <label>:65:                                     ; preds = %49
  %66 = landingpad { i8*, i32 }
          cleanup
  %67 = extractvalue { i8*, i32 } %66, 0
  %68 = extractvalue { i8*, i32 } %66, 1
  call void @llvm.lifetime.end.p0i8(i64 16, i8* nonnull %52) #2
  call void @__cxa_free_exception(i8* %50) #2
  br label %138

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
          to label %76 unwind label %118

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
          to label %87 unwind label %118

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
          to label %101 unwind label %122

; <label>:101:                                    ; preds = %98
  %102 = icmp eq i64 %2, 0
  br i1 %102, label %.loopexit, label %.preheader

.preheader:                                       ; preds = %101
  br label %124

.loopexit:                                        ; preds = %128, %101
  %103 = getelementptr inbounds %"class.std::basic_ifstream", %"class.std::basic_ifstream"* %4, i64 0, i32 1
  %104 = invoke %"class.std::basic_filebuf"* @_ZNSt13basic_filebufIcSt11char_traitsIcEE5closeEv(%"class.std::basic_filebuf"* nonnull %103)
          to label %105 unwind label %122

; <label>:105:                                    ; preds = %.loopexit
  %106 = icmp eq %"class.std::basic_filebuf"* %104, null
  br i1 %106, label %107, label %133

; <label>:107:                                    ; preds = %105
  %108 = load i8*, i8** %9, align 8, !tbaa !6
  %109 = getelementptr i8, i8* %108, i64 -24
  %110 = bitcast i8* %109 to i64*
  %111 = load i64, i64* %110, align 8
  %112 = getelementptr inbounds i8, i8* %8, i64 %111
  %113 = bitcast i8* %112 to %"class.std::basic_ios"*
  %114 = getelementptr inbounds i8, i8* %112, i64 32
  %115 = bitcast i8* %114 to i32*
  %116 = load i32, i32* %115, align 8, !tbaa !39
  %117 = or i32 %116, 4
  invoke void @_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate(%"class.std::basic_ios"* %113, i32 %117)
          to label %133 unwind label %122

; <label>:118:                                    ; preds = %84, %75
  %119 = landingpad { i8*, i32 }
          cleanup
  %120 = extractvalue { i8*, i32 } %119, 0
  %121 = extractvalue { i8*, i32 } %119, 1
  br label %138

; <label>:122:                                    ; preds = %107, %.loopexit, %98
  %123 = landingpad { i8*, i32 }
          cleanup
  br label %134

; <label>:124:                                    ; preds = %.preheader, %128
  %125 = phi i64 [ %129, %128 ], [ 0, %.preheader ]
  %126 = invoke dereferenceable(280) %"class.std::basic_istream"* @_ZNSi4readEPcl(%"class.std::basic_istream"* nonnull %41, i8* nonnull %99, i64 8)
          to label %127 unwind label %131

; <label>:127:                                    ; preds = %124
  invoke void @_ZNSt6vectorImSaImEE9push_backERKm(%"class.std::vector"* nonnull %1, i64* nonnull dereferenceable(8) %7)
          to label %128 unwind label %131

; <label>:128:                                    ; preds = %127
  %129 = add nuw i64 %125, 1
  %130 = icmp ult i64 %129, %2
  br i1 %130, label %124, label %.loopexit

; <label>:131:                                    ; preds = %127, %124
  %132 = landingpad { i8*, i32 }
          cleanup
  br label %134

; <label>:133:                                    ; preds = %107, %105
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %99) #2
  call void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEED1Ev(%"class.std::basic_ifstream"* nonnull %4) #2
  call void @llvm.lifetime.end.p0i8(i64 520, i8* nonnull %8) #2
  ret void

; <label>:134:                                    ; preds = %131, %122
  %135 = phi { i8*, i32 } [ %132, %131 ], [ %123, %122 ]
  %136 = extractvalue { i8*, i32 } %135, 0
  %137 = extractvalue { i8*, i32 } %135, 1
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %99) #2
  br label %138

; <label>:138:                                    ; preds = %134, %118, %65, %61, %57, %36, %32, %28
  %139 = phi i32 [ %39, %36 ], [ %35, %32 ], [ %31, %28 ], [ %60, %57 ], [ %68, %65 ], [ %64, %61 ], [ %137, %134 ], [ %121, %118 ]
  %140 = phi i8* [ %38, %36 ], [ %34, %32 ], [ %30, %28 ], [ %59, %57 ], [ %67, %65 ], [ %63, %61 ], [ %136, %134 ], [ %120, %118 ]
  call void @_ZNSt14basic_ifstreamIcSt11char_traitsIcEED1Ev(%"class.std::basic_ifstream"* nonnull %4) #2
  call void @llvm.lifetime.end.p0i8(i64 520, i8* nonnull %8) #2
  %141 = insertvalue { i8*, i32 } undef, i8* %140, 0
  %142 = insertvalue { i8*, i32 } %141, i32 %139, 1
  resume { i8*, i32 } %142

; <label>:143:                                    ; preds = %56, %27
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

; <label>:63:                                     ; preds = %61, %58
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

; Function Attrs: norecurse uwtable
define linkonce_odr void @_ZSt11__make_heapIPmN9__gnu_cxx5__ops15_Iter_comp_iterISt4lessImEEEEvT_S7_RT0_(i64*, i64*, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* dereferenceable(1)) local_unnamed_addr #10 comdat {
  %4 = ptrtoint i64* %1 to i64
  %5 = ptrtoint i64* %0 to i64
  %6 = sub i64 %4, %5
  %7 = ashr exact i64 %6, 3
  %8 = icmp slt i64 %6, 16
  br i1 %8, label %.loopexit2, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 8
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %16, label %.preheader30

.preheader30:                                     ; preds = %9
  br label %62

; <label>:16:                                     ; preds = %9
  %17 = shl nsw i64 %11, 1
  %18 = or i64 %17, 1
  %19 = getelementptr inbounds i64, i64* %0, i64 %18
  %20 = getelementptr inbounds i64, i64* %0, i64 %11
  br label %21

; <label>:21:                                     ; preds = %.loopexit, %16
  %22 = phi i64 [ %11, %16 ], [ %61, %.loopexit ]
  %23 = getelementptr inbounds i64, i64* %0, i64 %22
  %24 = load i64, i64* %23, align 8, !tbaa !2
  %25 = icmp sgt i64 %13, %22
  br i1 %25, label %.preheader26, label %.loopexit1

.preheader26:                                     ; preds = %21
  br label %26

; <label>:26:                                     ; preds = %.preheader26, %26
  %27 = phi i64 [ %36, %26 ], [ %22, %.preheader26 ]
  %28 = shl i64 %27, 1
  %29 = add i64 %28, 2
  %30 = getelementptr inbounds i64, i64* %0, i64 %29
  %31 = or i64 %28, 1
  %32 = getelementptr inbounds i64, i64* %0, i64 %31
  %33 = load i64, i64* %30, align 8, !tbaa !2
  %34 = load i64, i64* %32, align 8, !tbaa !2
  %35 = icmp ult i64 %33, %34
  %36 = select i1 %35, i64 %31, i64 %29
  %37 = getelementptr inbounds i64, i64* %0, i64 %36
  %38 = load i64, i64* %37, align 8, !tbaa !2
  %39 = getelementptr inbounds i64, i64* %0, i64 %27
  store i64 %38, i64* %39, align 8, !tbaa !2
  %40 = icmp slt i64 %36, %13
  br i1 %40, label %26, label %.loopexit1

.loopexit1:                                       ; preds = %26, %21
  %41 = phi i64 [ %22, %21 ], [ %36, %26 ]
  %42 = icmp eq i64 %41, %11
  br i1 %42, label %43, label %45

; <label>:43:                                     ; preds = %.loopexit1
  %44 = load i64, i64* %19, align 8, !tbaa !2
  store i64 %44, i64* %20, align 8, !tbaa !2
  br label %45

; <label>:45:                                     ; preds = %43, %.loopexit1
  %46 = phi i64 [ %18, %43 ], [ %41, %.loopexit1 ]
  %47 = icmp sgt i64 %46, %22
  br i1 %47, label %.preheader, label %.loopexit

.preheader:                                       ; preds = %45
  br label %48

; <label>:48:                                     ; preds = %.preheader, %55
  %49 = phi i64 [ %51, %55 ], [ %46, %.preheader ]
  %50 = add nsw i64 %49, -1
  %51 = sdiv i64 %50, 2
  %52 = getelementptr inbounds i64, i64* %0, i64 %51
  %53 = load i64, i64* %52, align 8, !tbaa !2
  %54 = icmp ult i64 %53, %24
  br i1 %54, label %55, label %.loopexit

; <label>:55:                                     ; preds = %48
  %56 = getelementptr inbounds i64, i64* %0, i64 %49
  store i64 %53, i64* %56, align 8, !tbaa !2
  %57 = icmp sgt i64 %51, %22
  br i1 %57, label %48, label %.loopexit

.loopexit:                                        ; preds = %55, %48, %45
  %58 = phi i64 [ %46, %45 ], [ %49, %48 ], [ %51, %55 ]
  %59 = getelementptr inbounds i64, i64* %0, i64 %58
  store i64 %24, i64* %59, align 8, !tbaa !2
  %60 = icmp eq i64 %22, 0
  %61 = add nsw i64 %22, -1
  br i1 %60, label %.loopexit2, label %21

; <label>:62:                                     ; preds = %.preheader30, %.loopexit3
  %63 = phi i64 [ %97, %.loopexit3 ], [ %11, %.preheader30 ]
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  %65 = load i64, i64* %64, align 8, !tbaa !2
  %66 = icmp sgt i64 %13, %63
  br i1 %66, label %.preheader29, label %.loopexit3

.preheader29:                                     ; preds = %62
  br label %67

; <label>:67:                                     ; preds = %.preheader29, %67
  %68 = phi i64 [ %77, %67 ], [ %63, %.preheader29 ]
  %69 = shl i64 %68, 1
  %70 = add i64 %69, 2
  %71 = getelementptr inbounds i64, i64* %0, i64 %70
  %72 = or i64 %69, 1
  %73 = getelementptr inbounds i64, i64* %0, i64 %72
  %74 = load i64, i64* %71, align 8, !tbaa !2
  %75 = load i64, i64* %73, align 8, !tbaa !2
  %76 = icmp ult i64 %74, %75
  %77 = select i1 %76, i64 %72, i64 %70
  %78 = getelementptr inbounds i64, i64* %0, i64 %77
  %79 = load i64, i64* %78, align 8, !tbaa !2
  %80 = getelementptr inbounds i64, i64* %0, i64 %68
  store i64 %79, i64* %80, align 8, !tbaa !2
  %81 = icmp slt i64 %77, %13
  br i1 %81, label %67, label %82

; <label>:82:                                     ; preds = %67
  %83 = getelementptr inbounds i64, i64* %0, i64 %77
  %84 = icmp sgt i64 %77, %63
  br i1 %84, label %.preheader27, label %.loopexit3

.preheader27:                                     ; preds = %82
  br label %85

; <label>:85:                                     ; preds = %.preheader27, %93
  %86 = phi i64 [ %88, %93 ], [ %77, %.preheader27 ]
  %87 = add nsw i64 %86, -1
  %88 = sdiv i64 %87, 2
  %89 = getelementptr inbounds i64, i64* %0, i64 %88
  %90 = load i64, i64* %89, align 8, !tbaa !2
  %91 = icmp ult i64 %90, %65
  %92 = getelementptr inbounds i64, i64* %0, i64 %86
  br i1 %91, label %93, label %.loopexit3

; <label>:93:                                     ; preds = %85
  store i64 %90, i64* %92, align 8, !tbaa !2
  %94 = icmp sgt i64 %88, %63
  br i1 %94, label %85, label %.loopexit3.loopexit

.loopexit3.loopexit:                              ; preds = %93
  %95 = getelementptr inbounds i64, i64* %0, i64 %88
  br label %.loopexit3

.loopexit3:                                       ; preds = %85, %.loopexit3.loopexit, %82, %62
  %.pre-phi = phi i64* [ %83, %82 ], [ %64, %62 ], [ %95, %.loopexit3.loopexit ], [ %92, %85 ]
  store i64 %65, i64* %.pre-phi, align 8, !tbaa !2
  %96 = icmp eq i64 %63, 0
  %97 = add nsw i64 %63, -1
  br i1 %96, label %.loopexit2, label %62

.loopexit2:                                       ; preds = %.loopexit3, %.loopexit, %3
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

; <label>:29:                                     ; preds = %24, %9
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

; <label>:43:                                     ; preds = %42, %38
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %32) #2
  %44 = load i64, i64* %31, align 8, !tbaa !22
  %45 = load i64, i64* %11, align 8, !tbaa !19
  %46 = icmp eq i64 %44, %45
  %47 = inttoptr i64 %45 to i64*
  br i1 %46, label %.loopexit, label %48

; <label>:48:                                     ; preds = %43
  %49 = sub i64 %44, %45
  %50 = ashr exact i64 %49, 3
  br label %64

; <label>:51:                                     ; preds = %14, %7
  %52 = landingpad { i8*, i32 }
          cleanup
  %53 = extractvalue { i8*, i32 } %52, 0
  %54 = extractvalue { i8*, i32 } %52, 1
  br label %71

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
  br label %71

; <label>:64:                                     ; preds = %64, %48
  %65 = phi i64 [ 0, %48 ], [ %69, %64 ]
  %66 = getelementptr inbounds i64, i64* %47, i64 %65
  %67 = load i64, i64* %66, align 8, !tbaa !2
  %68 = urem i64 %67, %2
  store i64 %68, i64* %66, align 8, !tbaa !2
  %69 = add nuw i64 %65, 1
  %70 = icmp ult i64 %69, %50
  br i1 %70, label %64, label %.loopexit

.loopexit:                                        ; preds = %64, %43
  ret void

; <label>:71:                                     ; preds = %63, %51
  %72 = phi i8* [ %53, %51 ], [ %57, %63 ]
  %73 = phi i32 [ %54, %51 ], [ %58, %63 ]
  %74 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %75 = load i64*, i64** %74, align 8, !tbaa !19
  %76 = icmp eq i64* %75, null
  br i1 %76, label %79, label %77

; <label>:77:                                     ; preds = %71
  %78 = bitcast i64* %75 to i8*
  call void @_ZdlPv(i8* %78) #2
  br label %79

; <label>:79:                                     ; preds = %77, %71
  %80 = insertvalue { i8*, i32 } undef, i8* %72, 0
  %81 = insertvalue { i8*, i32 } %80, i32 %73, 1
  resume { i8*, i32 } %81
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
          to label %8 unwind label %54

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
          to label %16 unwind label %54

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

; <label>:28:                                     ; preds = %23, %9
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
          to label %38 unwind label %58

; <label>:38:                                     ; preds = %28
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %40 = load i8*, i8** %39, align 8, !tbaa !32
  %41 = icmp eq i8* %40, %34
  br i1 %41, label %43, label %42

; <label>:42:                                     ; preds = %38
  call void @_ZdlPv(i8* %40) #2
  br label %43

; <label>:43:                                     ; preds = %42, %38
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  %44 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %45 = load i64*, i64** %44, align 8, !tbaa !23
  %46 = getelementptr inbounds i64, i64* %45, i64 %1
  br i1 %11, label %67, label %47

; <label>:47:                                     ; preds = %43
  %48 = shl nuw i64 %1, 3
  %49 = ashr exact i64 %48, 3
  %50 = call i64 @llvm.ctlz.i64(i64 %49, i1 true) #2, !range !24
  %51 = shl nuw nsw i64 %50, 1
  %52 = xor i64 %51, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %45, i64* %46, i64 %52)
          to label %53 unwind label %54

; <label>:53:                                     ; preds = %47
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %45, i64* %46)
          to label %67 unwind label %54

; <label>:54:                                     ; preds = %53, %47, %13, %7
  %55 = landingpad { i8*, i32 }
          cleanup
  %56 = extractvalue { i8*, i32 } %55, 0
  %57 = extractvalue { i8*, i32 } %55, 1
  br label %68

; <label>:58:                                     ; preds = %28
  %59 = landingpad { i8*, i32 }
          cleanup
  %60 = extractvalue { i8*, i32 } %59, 0
  %61 = extractvalue { i8*, i32 } %59, 1
  %62 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %63 = load i8*, i8** %62, align 8, !tbaa !32
  %64 = icmp eq i8* %63, %34
  br i1 %64, label %66, label %65

; <label>:65:                                     ; preds = %58
  call void @_ZdlPv(i8* %63) #2
  br label %66

; <label>:66:                                     ; preds = %65, %58
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  br label %68

; <label>:67:                                     ; preds = %53, %43
  ret void

; <label>:68:                                     ; preds = %66, %54
  %69 = phi i32 [ %57, %54 ], [ %61, %66 ]
  %70 = phi i8* [ %56, %54 ], [ %60, %66 ]
  %71 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %72 = load i64*, i64** %71, align 8, !tbaa !19
  %73 = icmp eq i64* %72, null
  br i1 %73, label %76, label %74

; <label>:74:                                     ; preds = %68
  %75 = bitcast i64* %72 to i8*
  call void @_ZdlPv(i8* %75) #2
  br label %76

; <label>:76:                                     ; preds = %74, %68
  %77 = insertvalue { i8*, i32 } undef, i8* %70, 0
  %78 = insertvalue { i8*, i32 } %77, i32 %69, 1
  resume { i8*, i32 } %78
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
          to label %10 unwind label %53

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
          to label %19 unwind label %53

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

; <label>:31:                                     ; preds = %26, %11
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
          to label %41 unwind label %58

; <label>:41:                                     ; preds = %31
  %42 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %43 = load i8*, i8** %42, align 8, !tbaa !32
  %44 = icmp eq i8* %43, %37
  br i1 %44, label %46, label %45

; <label>:45:                                     ; preds = %41
  call void @_ZdlPv(i8* %43) #2
  br label %46

; <label>:46:                                     ; preds = %45, %41
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  %47 = load i64, i64* %33, align 8, !tbaa !22
  %48 = load i64, i64* %13, align 8, !tbaa !19
  %49 = sub i64 %47, %48
  %50 = ashr exact i64 %49, 3
  %51 = icmp ugt i64 %50, %1
  %52 = inttoptr i64 %48 to i64*
  br i1 %51, label %.preheader51, label %.loopexit4

.preheader51:                                     ; preds = %46
  br label %84

; <label>:53:                                     ; preds = %183, %175, %75, %16, %9
  %54 = phi i64 [ 0, %9 ], [ %72, %183 ], [ %72, %175 ], [ %72, %75 ], [ 0, %16 ]
  %55 = landingpad { i8*, i32 }
          cleanup
  %56 = extractvalue { i8*, i32 } %55, 0
  %57 = extractvalue { i8*, i32 } %55, 1
  br label %475

; <label>:58:                                     ; preds = %31
  %59 = landingpad { i8*, i32 }
          cleanup
  %60 = extractvalue { i8*, i32 } %59, 0
  %61 = extractvalue { i8*, i32 } %59, 1
  %62 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %63 = load i8*, i8** %62, align 8, !tbaa !32
  %64 = icmp eq i8* %63, %37
  br i1 %64, label %66, label %65

; <label>:65:                                     ; preds = %58
  call void @_ZdlPv(i8* %63) #2
  br label %66

; <label>:66:                                     ; preds = %65, %58
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  br label %475

.loopexit4.loopexit:                              ; preds = %137
  %67 = ptrtoint i64* %146 to i64
  br label %.loopexit4

.loopexit4:                                       ; preds = %.loopexit4.loopexit, %46
  %68 = phi i64* [ %52, %46 ], [ %138, %.loopexit4.loopexit ]
  %69 = phi i64* [ %52, %46 ], [ %139, %.loopexit4.loopexit ]
  %70 = phi i64* [ %52, %46 ], [ %140, %.loopexit4.loopexit ]
  %71 = phi i64 [ 0, %46 ], [ %67, %.loopexit4.loopexit ]
  %72 = phi i64 [ 0, %46 ], [ %144, %.loopexit4.loopexit ]
  %73 = phi i64 [ %50, %46 ], [ %150, %.loopexit4.loopexit ]
  %74 = icmp ult i64 %73, %1
  br i1 %74, label %75, label %80

; <label>:75:                                     ; preds = %.loopexit4
  %76 = sub i64 %1, %73
  invoke void @_ZNSt6vectorImSaImEE17_M_default_appendEm(%"class.std::vector"* nonnull %0, i64 %76)
          to label %77 unwind label %53

; <label>:77:                                     ; preds = %75
  %78 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %79 = load i64*, i64** %78, align 8, !tbaa !23
  br label %160

; <label>:80:                                     ; preds = %.loopexit4
  %81 = icmp ugt i64 %73, %1
  br i1 %81, label %82, label %160

; <label>:82:                                     ; preds = %80
  %83 = getelementptr inbounds i64, i64* %68, i64 %1
  store i64* %83, i64** %15, align 8, !tbaa !22
  br label %160

; <label>:84:                                     ; preds = %.preheader51, %137
  %85 = phi i64* [ %139, %137 ], [ %52, %.preheader51 ]
  %86 = phi i64* [ %140, %137 ], [ %52, %.preheader51 ]
  %87 = phi i64 [ %141, %137 ], [ %48, %.preheader51 ]
  %88 = phi i64 [ %142, %137 ], [ %47, %.preheader51 ]
  %89 = phi i64* [ %138, %137 ], [ %52, %.preheader51 ]
  %90 = phi i64 [ %148, %137 ], [ %1, %.preheader51 ]
  %91 = phi i64* [ %145, %137 ], [ null, %.preheader51 ]
  %92 = phi i64 [ %144, %137 ], [ 0, %.preheader51 ]
  %93 = phi i64 [ %147, %137 ], [ 0, %.preheader51 ]
  %94 = getelementptr inbounds i64, i64* %89, i64 %90
  %95 = inttoptr i64 %93 to i64*
  %96 = icmp eq i64* %91, %95
  br i1 %96, label %100, label %97

; <label>:97:                                     ; preds = %84
  %98 = load i64, i64* %94, align 8, !tbaa !2
  store i64 %98, i64* %95, align 8, !tbaa !2
  %99 = inttoptr i64 %87 to i64*
  br label %137

; <label>:100:                                    ; preds = %84
  %101 = sub i64 %93, %92
  %102 = ashr exact i64 %101, 3
  %103 = icmp eq i64 %101, 0
  %104 = select i1 %103, i64 1, i64 %102
  %105 = add nsw i64 %104, %102
  %106 = icmp ult i64 %105, %102
  %107 = icmp ugt i64 %105, 2305843009213693951
  %108 = or i1 %106, %107
  %109 = select i1 %108, i64 2305843009213693951, i64 %105
  %110 = icmp eq i64 %109, 0
  br i1 %110, label %120, label %111

; <label>:111:                                    ; preds = %100
  %112 = icmp ugt i64 %109, 2305843009213693951
  br i1 %112, label %113, label %115

; <label>:113:                                    ; preds = %111
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %114 unwind label %154

; <label>:114:                                    ; preds = %113
  unreachable

; <label>:115:                                    ; preds = %111
  %116 = shl i64 %109, 3
  %117 = invoke i8* @_Znwm(i64 %116)
          to label %118 unwind label %152

; <label>:118:                                    ; preds = %115
  %119 = bitcast i8* %117 to i64*
  br label %120

; <label>:120:                                    ; preds = %118, %100
  %121 = phi i8* [ %117, %118 ], [ null, %100 ]
  %122 = phi i64* [ %119, %118 ], [ null, %100 ]
  %123 = getelementptr inbounds i64, i64* %122, i64 %102
  %124 = load i64, i64* %94, align 8, !tbaa !2
  store i64 %124, i64* %123, align 8, !tbaa !2
  br i1 %103, label %127, label %125

; <label>:125:                                    ; preds = %120
  %126 = inttoptr i64 %92 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %121, i8* %126, i64 %101, i32 8, i1 false) #2
  br label %127

; <label>:127:                                    ; preds = %125, %120
  %128 = icmp eq i64 %92, 0
  br i1 %128, label %131, label %129

; <label>:129:                                    ; preds = %127
  %130 = inttoptr i64 %92 to i8*
  call void @_ZdlPv(i8* %130) #2
  br label %131

; <label>:131:                                    ; preds = %129, %127
  %132 = ptrtoint i8* %121 to i64
  %133 = getelementptr inbounds i64, i64* %122, i64 %109
  %134 = load i64, i64* %33, align 8, !tbaa !22
  %135 = load i64, i64* %13, align 8, !tbaa !19
  %136 = inttoptr i64 %135 to i64*
  br label %137

; <label>:137:                                    ; preds = %131, %97
  %138 = phi i64* [ %136, %131 ], [ %99, %97 ]
  %139 = phi i64* [ %136, %131 ], [ %85, %97 ]
  %140 = phi i64* [ %136, %131 ], [ %86, %97 ]
  %141 = phi i64 [ %135, %131 ], [ %87, %97 ]
  %142 = phi i64 [ %134, %131 ], [ %88, %97 ]
  %143 = phi i64* [ %123, %131 ], [ %95, %97 ]
  %144 = phi i64 [ %132, %131 ], [ %92, %97 ]
  %145 = phi i64* [ %133, %131 ], [ %91, %97 ]
  %146 = getelementptr inbounds i64, i64* %143, i64 1
  %147 = ptrtoint i64* %146 to i64
  %148 = add nuw i64 %90, 1
  %149 = sub i64 %142, %141
  %150 = ashr exact i64 %149, 3
  %151 = icmp ult i64 %148, %150
  br i1 %151, label %84, label %.loopexit4.loopexit

; <label>:152:                                    ; preds = %115
  %153 = landingpad { i8*, i32 }
          cleanup
  br label %156

; <label>:154:                                    ; preds = %113
  %155 = landingpad { i8*, i32 }
          cleanup
  br label %156

; <label>:156:                                    ; preds = %154, %152
  %157 = phi { i8*, i32 } [ %153, %152 ], [ %155, %154 ]
  %158 = extractvalue { i8*, i32 } %157, 0
  %159 = extractvalue { i8*, i32 } %157, 1
  br label %475

; <label>:160:                                    ; preds = %82, %80, %77
  %161 = phi i64* [ %79, %77 ], [ %69, %82 ], [ %69, %80 ]
  %162 = phi i64* [ %79, %77 ], [ %70, %82 ], [ %70, %80 ]
  %163 = lshr i64 %1, 1
  %164 = icmp eq i64 %163, 0
  %165 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  br i1 %164, label %.loopexit3, label %166

; <label>:166:                                    ; preds = %160
  %167 = add i64 %1, -1
  %168 = getelementptr inbounds i64, i64* %162, i64 %167
  %169 = load i64, i64* %162, align 8, !tbaa !2
  %170 = load i64, i64* %168, align 8, !tbaa !2
  store i64 %170, i64* %162, align 8, !tbaa !2
  store i64 %169, i64* %168, align 8, !tbaa !2
  %171 = icmp eq i64 %163, 1
  br i1 %171, label %.loopexit3, label %.preheader50

.preheader50:                                     ; preds = %166
  br label %184

.loopexit3:                                       ; preds = %184, %166, %160
  %172 = phi i64* [ %162, %160 ], [ %161, %166 ], [ %161, %184 ]
  %173 = load i64*, i64** %15, align 8, !tbaa !23
  %174 = icmp eq i64* %172, %173
  br i1 %174, label %193, label %175

; <label>:175:                                    ; preds = %.loopexit3
  %176 = ptrtoint i64* %173 to i64
  %177 = ptrtoint i64* %172 to i64
  %178 = sub i64 %176, %177
  %179 = ashr exact i64 %178, 3
  %180 = call i64 @llvm.ctlz.i64(i64 %179, i1 true) #2, !range !24
  %181 = shl nuw nsw i64 %180, 1
  %182 = xor i64 %181, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %172, i64* %173, i64 %182)
          to label %183 unwind label %53

; <label>:183:                                    ; preds = %175
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %172, i64* %173)
          to label %193 unwind label %53

; <label>:184:                                    ; preds = %.preheader50, %184
  %185 = phi i64 [ %191, %184 ], [ 1, %.preheader50 ]
  %186 = getelementptr inbounds i64, i64* %161, i64 %185
  %187 = sub i64 %167, %185
  %188 = getelementptr inbounds i64, i64* %161, i64 %187
  %189 = load i64, i64* %186, align 8, !tbaa !2
  %190 = load i64, i64* %188, align 8, !tbaa !2
  store i64 %190, i64* %186, align 8, !tbaa !2
  store i64 %189, i64* %188, align 8, !tbaa !2
  %191 = add nuw nsw i64 %185, 1
  %192 = icmp eq i64 %191, %163
  br i1 %192, label %.loopexit3, label %184, !llvm.loop !46

; <label>:193:                                    ; preds = %183, %.loopexit3
  %194 = udiv i64 %1, %2
  %195 = add i64 %194, 1
  %196 = sub i64 %71, %72
  %197 = ashr exact i64 %196, 3
  %198 = icmp eq i64 %196, 0
  br i1 %198, label %.loopexit2, label %199

; <label>:199:                                    ; preds = %193
  %200 = inttoptr i64 %72 to i64*
  %201 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %202 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %203 = bitcast i64** %201 to i64*
  %204 = bitcast %"class.std::vector"* %4 to i64*
  %205 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %206 = icmp eq i64 %195, 0
  %207 = bitcast %"class.std::vector"* %4 to i8**
  %208 = load i64*, i64** %201, align 8, !tbaa !22
  %.pre = load i64*, i64** %202, align 8, !tbaa !28
  br label %223

.loopexit2:                                       ; preds = %.loopexit1, %193
  %209 = phi i64 [ 0, %193 ], [ %292, %.loopexit1 ]
  %210 = load i64, i64* %33, align 8, !tbaa !22
  %211 = load i64, i64* %13, align 8, !tbaa !19
  %212 = sub i64 %210, %211
  %213 = ashr exact i64 %212, 3
  %214 = icmp ult i64 %209, %213
  br i1 %214, label %215, label %.loopexit

; <label>:215:                                    ; preds = %.loopexit2
  %216 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %217 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %218 = bitcast i64** %216 to i64*
  %219 = bitcast %"class.std::vector"* %4 to i64*
  %220 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %221 = bitcast %"class.std::vector"* %4 to i8**
  %222 = load i64*, i64** %216, align 8, !tbaa !22
  %.pre26 = load i64*, i64** %217, align 8, !tbaa !28
  br label %379

; <label>:223:                                    ; preds = %.loopexit1, %199
  %224 = phi i64* [ %.pre, %199 ], [ %289, %.loopexit1 ]
  %225 = phi i64* [ %208, %199 ], [ %290, %.loopexit1 ]
  %226 = phi i64 [ 0, %199 ], [ %291, %.loopexit1 ]
  %227 = phi i64 [ 0, %199 ], [ %292, %.loopexit1 ]
  %228 = getelementptr inbounds i64, i64* %200, i64 %226
  %229 = icmp eq i64* %225, %224
  %230 = ptrtoint i64* %225 to i64
  br i1 %229, label %234, label %231

; <label>:231:                                    ; preds = %223
  %232 = load i64, i64* %228, align 8, !tbaa !2
  store i64 %232, i64* %225, align 8, !tbaa !2
  %233 = getelementptr inbounds i64, i64* %225, i64 1
  store i64* %233, i64** %201, align 8, !tbaa !22
  br label %286

; <label>:234:                                    ; preds = %223
  %235 = load i64, i64* %204, align 8, !tbaa !23
  %236 = sub i64 %230, %235
  %237 = ashr exact i64 %236, 3
  %238 = icmp eq i64 %236, 0
  %239 = select i1 %238, i64 1, i64 %237
  %240 = add nsw i64 %239, %237
  %241 = icmp ult i64 %240, %237
  %242 = icmp ugt i64 %240, 2305843009213693951
  %243 = or i1 %241, %242
  %244 = select i1 %243, i64 2305843009213693951, i64 %240
  %245 = icmp eq i64 %244, 0
  %246 = inttoptr i64 %235 to i64*
  br i1 %245, label %257, label %247

; <label>:247:                                    ; preds = %234
  %248 = icmp ugt i64 %244, 2305843009213693951
  br i1 %248, label %249, label %251

; <label>:249:                                    ; preds = %247
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %250 unwind label %296

; <label>:250:                                    ; preds = %249
  unreachable

; <label>:251:                                    ; preds = %247
  %252 = shl i64 %244, 3
  %253 = invoke i8* @_Znwm(i64 %252)
          to label %254 unwind label %294

; <label>:254:                                    ; preds = %251
  %255 = bitcast i8* %253 to i64*
  %256 = load i64*, i64** %205, align 8, !tbaa !19
  br label %257

; <label>:257:                                    ; preds = %254, %234
  %258 = phi i64* [ %256, %254 ], [ %246, %234 ]
  %259 = phi i8* [ %253, %254 ], [ null, %234 ]
  %260 = phi i64* [ %255, %254 ], [ null, %234 ]
  %261 = getelementptr inbounds i64, i64* %260, i64 %237
  %262 = load i64, i64* %228, align 8, !tbaa !2
  store i64 %262, i64* %261, align 8, !tbaa !2
  %263 = ptrtoint i64* %258 to i64
  %264 = sub i64 %230, %263
  %265 = ashr exact i64 %264, 3
  %266 = icmp eq i64 %264, 0
  br i1 %266, label %269, label %267

; <label>:267:                                    ; preds = %257
  %268 = bitcast i64* %258 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %259, i8* %268, i64 %264, i32 8, i1 false) #2
  br label %269

; <label>:269:                                    ; preds = %267, %257
  %270 = getelementptr inbounds i64, i64* %260, i64 %265
  %271 = getelementptr inbounds i64, i64* %270, i64 1
  %272 = load i64, i64* %203, align 8, !tbaa !22
  %273 = sub i64 %272, %230
  %274 = ashr exact i64 %273, 3
  %275 = icmp eq i64 %273, 0
  br i1 %275, label %279, label %276

; <label>:276:                                    ; preds = %269
  %277 = bitcast i64* %271 to i8*
  %278 = bitcast i64* %224 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %277, i8* %278, i64 %273, i32 8, i1 false) #2
  br label %279

; <label>:279:                                    ; preds = %276, %269
  %280 = getelementptr inbounds i64, i64* %271, i64 %274
  %281 = icmp eq i64* %258, null
  br i1 %281, label %284, label %282

; <label>:282:                                    ; preds = %279
  %283 = bitcast i64* %258 to i8*
  call void @_ZdlPv(i8* %283) #2
  br label %284

; <label>:284:                                    ; preds = %282, %279
  store i8* %259, i8** %207, align 8, !tbaa !19
  store i64* %280, i64** %201, align 8, !tbaa !22
  %285 = getelementptr inbounds i64, i64* %260, i64 %244
  store i64* %285, i64** %202, align 8, !tbaa !28
  br label %286

; <label>:286:                                    ; preds = %284, %231
  %287 = phi i64* [ %285, %284 ], [ %224, %231 ]
  %288 = phi i64* [ %280, %284 ], [ %233, %231 ]
  br i1 %206, label %.loopexit1, label %.preheader

.preheader:                                       ; preds = %286
  br label %302

.loopexit1:                                       ; preds = %366, %286
  %289 = phi i64* [ %287, %286 ], [ %367, %366 ]
  %290 = phi i64* [ %288, %286 ], [ %368, %366 ]
  %291 = add nuw i64 %226, 1
  %292 = add i64 %227, %195
  %293 = icmp ult i64 %291, %197
  br i1 %293, label %223, label %.loopexit2

; <label>:294:                                    ; preds = %251
  %295 = landingpad { i8*, i32 }
          cleanup
  br label %298

; <label>:296:                                    ; preds = %249
  %297 = landingpad { i8*, i32 }
          cleanup
  br label %298

; <label>:298:                                    ; preds = %296, %294
  %299 = phi { i8*, i32 } [ %295, %294 ], [ %297, %296 ]
  %300 = extractvalue { i8*, i32 } %299, 0
  %301 = extractvalue { i8*, i32 } %299, 1
  br label %475

; <label>:302:                                    ; preds = %.preheader, %366
  %303 = phi i64* [ %367, %366 ], [ %287, %.preheader ]
  %304 = phi i64* [ %368, %366 ], [ %288, %.preheader ]
  %305 = phi i64 [ %369, %366 ], [ 0, %.preheader ]
  %306 = add i64 %305, %227
  %307 = load i64*, i64** %165, align 8, !tbaa !19
  %308 = getelementptr inbounds i64, i64* %307, i64 %306
  %309 = icmp eq i64* %304, %303
  %310 = ptrtoint i64* %304 to i64
  br i1 %309, label %314, label %311

; <label>:311:                                    ; preds = %302
  %312 = load i64, i64* %308, align 8, !tbaa !2
  store i64 %312, i64* %304, align 8, !tbaa !2
  %313 = getelementptr inbounds i64, i64* %304, i64 1
  store i64* %313, i64** %201, align 8, !tbaa !22
  br label %366

; <label>:314:                                    ; preds = %302
  %315 = load i64, i64* %204, align 8, !tbaa !23
  %316 = sub i64 %310, %315
  %317 = ashr exact i64 %316, 3
  %318 = icmp eq i64 %316, 0
  %319 = select i1 %318, i64 1, i64 %317
  %320 = add nsw i64 %319, %317
  %321 = icmp ult i64 %320, %317
  %322 = icmp ugt i64 %320, 2305843009213693951
  %323 = or i1 %321, %322
  %324 = select i1 %323, i64 2305843009213693951, i64 %320
  %325 = icmp eq i64 %324, 0
  %326 = inttoptr i64 %315 to i64*
  br i1 %325, label %337, label %327

; <label>:327:                                    ; preds = %314
  %328 = icmp ugt i64 %324, 2305843009213693951
  br i1 %328, label %329, label %331

; <label>:329:                                    ; preds = %327
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %330 unwind label %373

; <label>:330:                                    ; preds = %329
  unreachable

; <label>:331:                                    ; preds = %327
  %332 = shl i64 %324, 3
  %333 = invoke i8* @_Znwm(i64 %332)
          to label %334 unwind label %371

; <label>:334:                                    ; preds = %331
  %335 = bitcast i8* %333 to i64*
  %336 = load i64*, i64** %205, align 8, !tbaa !19
  br label %337

; <label>:337:                                    ; preds = %334, %314
  %338 = phi i64* [ %336, %334 ], [ %326, %314 ]
  %339 = phi i8* [ %333, %334 ], [ null, %314 ]
  %340 = phi i64* [ %335, %334 ], [ null, %314 ]
  %341 = getelementptr inbounds i64, i64* %340, i64 %317
  %342 = load i64, i64* %308, align 8, !tbaa !2
  store i64 %342, i64* %341, align 8, !tbaa !2
  %343 = ptrtoint i64* %338 to i64
  %344 = sub i64 %310, %343
  %345 = ashr exact i64 %344, 3
  %346 = icmp eq i64 %344, 0
  br i1 %346, label %349, label %347

; <label>:347:                                    ; preds = %337
  %348 = bitcast i64* %338 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %339, i8* %348, i64 %344, i32 8, i1 false) #2
  br label %349

; <label>:349:                                    ; preds = %347, %337
  %350 = getelementptr inbounds i64, i64* %340, i64 %345
  %351 = getelementptr inbounds i64, i64* %350, i64 1
  %352 = load i64, i64* %203, align 8, !tbaa !22
  %353 = sub i64 %352, %310
  %354 = ashr exact i64 %353, 3
  %355 = icmp eq i64 %353, 0
  br i1 %355, label %359, label %356

; <label>:356:                                    ; preds = %349
  %357 = bitcast i64* %351 to i8*
  %358 = bitcast i64* %303 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %357, i8* %358, i64 %353, i32 8, i1 false) #2
  br label %359

; <label>:359:                                    ; preds = %356, %349
  %360 = getelementptr inbounds i64, i64* %351, i64 %354
  %361 = icmp eq i64* %338, null
  br i1 %361, label %364, label %362

; <label>:362:                                    ; preds = %359
  %363 = bitcast i64* %338 to i8*
  call void @_ZdlPv(i8* %363) #2
  br label %364

; <label>:364:                                    ; preds = %362, %359
  store i8* %339, i8** %207, align 8, !tbaa !19
  store i64* %360, i64** %201, align 8, !tbaa !22
  %365 = getelementptr inbounds i64, i64* %340, i64 %324
  store i64* %365, i64** %202, align 8, !tbaa !28
  br label %366

; <label>:366:                                    ; preds = %364, %311
  %367 = phi i64* [ %365, %364 ], [ %303, %311 ]
  %368 = phi i64* [ %360, %364 ], [ %313, %311 ]
  %369 = add nuw i64 %305, 1
  %370 = icmp ult i64 %369, %195
  br i1 %370, label %302, label %.loopexit1

; <label>:371:                                    ; preds = %331
  %372 = landingpad { i8*, i32 }
          cleanup
  br label %375

; <label>:373:                                    ; preds = %329
  %374 = landingpad { i8*, i32 }
          cleanup
  br label %375

; <label>:375:                                    ; preds = %373, %371
  %376 = phi { i8*, i32 } [ %372, %371 ], [ %374, %373 ]
  %377 = extractvalue { i8*, i32 } %376, 0
  %378 = extractvalue { i8*, i32 } %376, 1
  br label %475

; <label>:379:                                    ; preds = %446, %215
  %380 = phi i64* [ %.pre26, %215 ], [ %447, %446 ]
  %381 = phi i64 [ %211, %215 ], [ %448, %446 ]
  %382 = phi i64 [ %210, %215 ], [ %449, %446 ]
  %383 = phi i64* [ %222, %215 ], [ %450, %446 ]
  %384 = phi i64 [ %209, %215 ], [ %451, %446 ]
  %385 = inttoptr i64 %381 to i64*
  %386 = getelementptr inbounds i64, i64* %385, i64 %384
  %387 = icmp eq i64* %383, %380
  %388 = ptrtoint i64* %383 to i64
  br i1 %387, label %392, label %389

; <label>:389:                                    ; preds = %379
  %390 = load i64, i64* %386, align 8, !tbaa !2
  store i64 %390, i64* %383, align 8, !tbaa !2
  %391 = getelementptr inbounds i64, i64* %383, i64 1
  store i64* %391, i64** %216, align 8, !tbaa !22
  br label %446

; <label>:392:                                    ; preds = %379
  %393 = load i64, i64* %219, align 8, !tbaa !23
  %394 = sub i64 %388, %393
  %395 = ashr exact i64 %394, 3
  %396 = icmp eq i64 %394, 0
  %397 = select i1 %396, i64 1, i64 %395
  %398 = add nsw i64 %397, %395
  %399 = icmp ult i64 %398, %395
  %400 = icmp ugt i64 %398, 2305843009213693951
  %401 = or i1 %399, %400
  %402 = select i1 %401, i64 2305843009213693951, i64 %398
  %403 = icmp eq i64 %402, 0
  %404 = inttoptr i64 %393 to i64*
  br i1 %403, label %415, label %405

; <label>:405:                                    ; preds = %392
  %406 = icmp ugt i64 %402, 2305843009213693951
  br i1 %406, label %407, label %409

; <label>:407:                                    ; preds = %405
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %408 unwind label %457

; <label>:408:                                    ; preds = %407
  unreachable

; <label>:409:                                    ; preds = %405
  %410 = shl i64 %402, 3
  %411 = invoke i8* @_Znwm(i64 %410)
          to label %412 unwind label %455

; <label>:412:                                    ; preds = %409
  %413 = bitcast i8* %411 to i64*
  %414 = load i64*, i64** %220, align 8, !tbaa !19
  br label %415

; <label>:415:                                    ; preds = %412, %392
  %416 = phi i64* [ %414, %412 ], [ %404, %392 ]
  %417 = phi i8* [ %411, %412 ], [ null, %392 ]
  %418 = phi i64* [ %413, %412 ], [ null, %392 ]
  %419 = getelementptr inbounds i64, i64* %418, i64 %395
  %420 = load i64, i64* %386, align 8, !tbaa !2
  store i64 %420, i64* %419, align 8, !tbaa !2
  %421 = ptrtoint i64* %416 to i64
  %422 = sub i64 %388, %421
  %423 = ashr exact i64 %422, 3
  %424 = icmp eq i64 %422, 0
  br i1 %424, label %427, label %425

; <label>:425:                                    ; preds = %415
  %426 = bitcast i64* %416 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %417, i8* %426, i64 %422, i32 8, i1 false) #2
  br label %427

; <label>:427:                                    ; preds = %425, %415
  %428 = getelementptr inbounds i64, i64* %418, i64 %423
  %429 = getelementptr inbounds i64, i64* %428, i64 1
  %430 = load i64, i64* %218, align 8, !tbaa !22
  %431 = sub i64 %430, %388
  %432 = ashr exact i64 %431, 3
  %433 = icmp eq i64 %431, 0
  br i1 %433, label %437, label %434

; <label>:434:                                    ; preds = %427
  %435 = bitcast i64* %429 to i8*
  %436 = bitcast i64* %380 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %435, i8* %436, i64 %431, i32 8, i1 false) #2
  br label %437

; <label>:437:                                    ; preds = %434, %427
  %438 = getelementptr inbounds i64, i64* %429, i64 %432
  %439 = icmp eq i64* %416, null
  br i1 %439, label %442, label %440

; <label>:440:                                    ; preds = %437
  %441 = bitcast i64* %416 to i8*
  call void @_ZdlPv(i8* %441) #2
  br label %442

; <label>:442:                                    ; preds = %440, %437
  store i8* %417, i8** %221, align 8, !tbaa !19
  store i64* %438, i64** %216, align 8, !tbaa !22
  %443 = getelementptr inbounds i64, i64* %418, i64 %402
  store i64* %443, i64** %217, align 8, !tbaa !28
  %444 = load i64, i64* %33, align 8, !tbaa !22
  %445 = load i64, i64* %13, align 8, !tbaa !19
  br label %446

; <label>:446:                                    ; preds = %442, %389
  %447 = phi i64* [ %443, %442 ], [ %380, %389 ]
  %448 = phi i64 [ %445, %442 ], [ %381, %389 ]
  %449 = phi i64 [ %444, %442 ], [ %382, %389 ]
  %450 = phi i64* [ %438, %442 ], [ %391, %389 ]
  %451 = add nuw i64 %384, 1
  %452 = sub i64 %449, %448
  %453 = ashr exact i64 %452, 3
  %454 = icmp ult i64 %451, %453
  br i1 %454, label %379, label %.loopexit

; <label>:455:                                    ; preds = %409
  %456 = landingpad { i8*, i32 }
          cleanup
  br label %459

; <label>:457:                                    ; preds = %.loopexit, %407
  %458 = landingpad { i8*, i32 }
          cleanup
  br label %459

; <label>:459:                                    ; preds = %457, %455
  %460 = phi { i8*, i32 } [ %456, %455 ], [ %458, %457 ]
  %461 = extractvalue { i8*, i32 } %460, 0
  %462 = extractvalue { i8*, i32 } %460, 1
  br label %475

.loopexit:                                        ; preds = %446, %.loopexit2
  %463 = invoke dereferenceable(24) %"class.std::vector"* @_ZNSt6vectorImSaImEEaSERKS1_(%"class.std::vector"* nonnull %0, %"class.std::vector"* nonnull dereferenceable(24) %4)
          to label %464 unwind label %457

; <label>:464:                                    ; preds = %.loopexit
  %465 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %466 = load i64*, i64** %465, align 8, !tbaa !19
  %467 = icmp eq i64* %466, null
  br i1 %467, label %470, label %468

; <label>:468:                                    ; preds = %464
  %469 = bitcast i64* %466 to i8*
  call void @_ZdlPv(i8* %469) #2
  br label %470

; <label>:470:                                    ; preds = %468, %464
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %471 = icmp eq i64 %72, 0
  br i1 %471, label %474, label %472

; <label>:472:                                    ; preds = %470
  %473 = inttoptr i64 %72 to i8*
  call void @_ZdlPv(i8* %473) #2
  br label %474

; <label>:474:                                    ; preds = %472, %470
  ret void

; <label>:475:                                    ; preds = %459, %375, %298, %156, %66, %53
  %476 = phi i64 [ %54, %53 ], [ %92, %156 ], [ %72, %375 ], [ %72, %298 ], [ %72, %459 ], [ 0, %66 ]
  %477 = phi i32 [ %57, %53 ], [ %159, %156 ], [ %378, %375 ], [ %301, %298 ], [ %462, %459 ], [ %61, %66 ]
  %478 = phi i8* [ %56, %53 ], [ %158, %156 ], [ %377, %375 ], [ %300, %298 ], [ %461, %459 ], [ %60, %66 ]
  %479 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %480 = load i64*, i64** %479, align 8, !tbaa !19
  %481 = icmp eq i64* %480, null
  br i1 %481, label %484, label %482

; <label>:482:                                    ; preds = %475
  %483 = bitcast i64* %480 to i8*
  call void @_ZdlPv(i8* %483) #2
  br label %484

; <label>:484:                                    ; preds = %482, %475
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %485 = icmp eq i64 %476, 0
  br i1 %485, label %488, label %486

; <label>:486:                                    ; preds = %484
  %487 = inttoptr i64 %476 to i8*
  call void @_ZdlPv(i8* %487) #2
  br label %488

; <label>:488:                                    ; preds = %486, %484
  %489 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %490 = load i64*, i64** %489, align 8, !tbaa !19
  %491 = icmp eq i64* %490, null
  br i1 %491, label %494, label %492

; <label>:492:                                    ; preds = %488
  %493 = bitcast i64* %490 to i8*
  call void @_ZdlPv(i8* %493) #2
  br label %494

; <label>:494:                                    ; preds = %492, %488
  %495 = insertvalue { i8*, i32 } undef, i8* %478, 0
  %496 = insertvalue { i8*, i32 } %495, i32 %477, 1
  resume { i8*, i32 } %496
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
          to label %8 unwind label %54

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
          to label %16 unwind label %54

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

; <label>:28:                                     ; preds = %23, %9
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
          to label %38 unwind label %58

; <label>:38:                                     ; preds = %28
  %39 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %40 = load i8*, i8** %39, align 8, !tbaa !32
  %41 = icmp eq i8* %40, %34
  br i1 %41, label %43, label %42

; <label>:42:                                     ; preds = %38
  call void @_ZdlPv(i8* %40) #2
  br label %43

; <label>:43:                                     ; preds = %42, %38
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  %44 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %45 = load i64*, i64** %44, align 8, !tbaa !23
  %46 = getelementptr inbounds i64, i64* %45, i64 %1
  br i1 %11, label %102, label %47

; <label>:47:                                     ; preds = %43
  %48 = shl nuw i64 %1, 3
  %49 = ashr exact i64 %48, 3
  %50 = call i64 @llvm.ctlz.i64(i64 %49, i1 true) #2, !range !24
  %51 = shl nuw nsw i64 %50, 1
  %52 = xor i64 %51, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %45, i64* %46, i64 %52)
          to label %53 unwind label %54

; <label>:53:                                     ; preds = %47
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %45, i64* %46)
          to label %67 unwind label %54

; <label>:54:                                     ; preds = %53, %47, %13, %7
  %55 = landingpad { i8*, i32 }
          cleanup
  %56 = extractvalue { i8*, i32 } %55, 0
  %57 = extractvalue { i8*, i32 } %55, 1
  br label %103

; <label>:58:                                     ; preds = %28
  %59 = landingpad { i8*, i32 }
          cleanup
  %60 = extractvalue { i8*, i32 } %59, 0
  %61 = extractvalue { i8*, i32 } %59, 1
  %62 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %4, i64 0, i32 0, i32 0
  %63 = load i8*, i8** %62, align 8, !tbaa !32
  %64 = icmp eq i8* %63, %34
  br i1 %64, label %66, label %65

; <label>:65:                                     ; preds = %58
  call void @_ZdlPv(i8* %63) #2
  br label %66

; <label>:66:                                     ; preds = %65, %58
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %31) #2
  br label %103

; <label>:67:                                     ; preds = %53
  %68 = lshr i64 %1, 1
  %69 = icmp eq i64 %68, 0
  br i1 %69, label %102, label %70

; <label>:70:                                     ; preds = %67
  %71 = load i64*, i64** %44, align 8, !tbaa !19
  %72 = add i64 %1, -1
  %73 = and i64 %68, 1
  %74 = icmp eq i64 %68, 1
  br i1 %74, label %.thread, label %75

; <label>:75:                                     ; preds = %70
  %76 = sub nsw i64 %68, %73
  br label %77

; <label>:77:                                     ; preds = %77, %75
  %78 = phi i64 [ 0, %75 ], [ %91, %77 ]
  %79 = phi i64 [ %76, %75 ], [ %92, %77 ]
  %80 = getelementptr inbounds i64, i64* %71, i64 %78
  %81 = sub i64 %72, %78
  %82 = getelementptr inbounds i64, i64* %71, i64 %81
  %83 = load i64, i64* %80, align 8, !tbaa !2
  %84 = load i64, i64* %82, align 8, !tbaa !2
  store i64 %84, i64* %80, align 8, !tbaa !2
  store i64 %83, i64* %82, align 8, !tbaa !2
  %85 = or i64 %78, 1
  %86 = getelementptr inbounds i64, i64* %71, i64 %85
  %87 = sub i64 %72, %85
  %88 = getelementptr inbounds i64, i64* %71, i64 %87
  %89 = load i64, i64* %86, align 8, !tbaa !2
  %90 = load i64, i64* %88, align 8, !tbaa !2
  store i64 %90, i64* %86, align 8, !tbaa !2
  store i64 %89, i64* %88, align 8, !tbaa !2
  %91 = add nuw nsw i64 %78, 2
  %92 = add i64 %79, -2
  %93 = icmp eq i64 %92, 0
  br i1 %93, label %94, label %77

; <label>:94:                                     ; preds = %77
  %95 = icmp eq i64 %73, 0
  br i1 %95, label %102, label %.thread

.thread:                                          ; preds = %70, %94
  %96 = phi i64 [ %91, %94 ], [ 0, %70 ]
  %97 = getelementptr inbounds i64, i64* %71, i64 %96
  %98 = sub i64 %72, %96
  %99 = getelementptr inbounds i64, i64* %71, i64 %98
  %100 = load i64, i64* %97, align 8, !tbaa !2
  %101 = load i64, i64* %99, align 8, !tbaa !2
  store i64 %101, i64* %97, align 8, !tbaa !2
  store i64 %100, i64* %99, align 8, !tbaa !2
  br label %102

; <label>:102:                                    ; preds = %.thread, %94, %67, %43
  ret void

; <label>:103:                                    ; preds = %66, %54
  %104 = phi i32 [ %57, %54 ], [ %61, %66 ]
  %105 = phi i8* [ %56, %54 ], [ %60, %66 ]
  %106 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %107 = load i64*, i64** %106, align 8, !tbaa !19
  %108 = icmp eq i64* %107, null
  br i1 %108, label %111, label %109

; <label>:109:                                    ; preds = %103
  %110 = bitcast i64* %107 to i8*
  call void @_ZdlPv(i8* %110) #2
  br label %111

; <label>:111:                                    ; preds = %109, %103
  %112 = insertvalue { i8*, i32 } undef, i8* %105, 0
  %113 = insertvalue { i8*, i32 } %112, i32 %104, 1
  resume { i8*, i32 } %113
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
          to label %10 unwind label %53

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
          to label %19 unwind label %53

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

; <label>:31:                                     ; preds = %26, %11
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
          to label %41 unwind label %58

; <label>:41:                                     ; preds = %31
  %42 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %43 = load i8*, i8** %42, align 8, !tbaa !32
  %44 = icmp eq i8* %43, %37
  br i1 %44, label %46, label %45

; <label>:45:                                     ; preds = %41
  call void @_ZdlPv(i8* %43) #2
  br label %46

; <label>:46:                                     ; preds = %45, %41
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  %47 = load i64, i64* %33, align 8, !tbaa !22
  %48 = load i64, i64* %13, align 8, !tbaa !19
  %49 = sub i64 %47, %48
  %50 = ashr exact i64 %49, 3
  %51 = icmp ugt i64 %50, %1
  %52 = inttoptr i64 %48 to i64*
  br i1 %51, label %.preheader51, label %.loopexit4

.preheader51:                                     ; preds = %46
  br label %84

; <label>:53:                                     ; preds = %183, %175, %75, %16, %9
  %54 = phi i64 [ 0, %9 ], [ %72, %183 ], [ %72, %175 ], [ %72, %75 ], [ 0, %16 ]
  %55 = landingpad { i8*, i32 }
          cleanup
  %56 = extractvalue { i8*, i32 } %55, 0
  %57 = extractvalue { i8*, i32 } %55, 1
  br label %475

; <label>:58:                                     ; preds = %31
  %59 = landingpad { i8*, i32 }
          cleanup
  %60 = extractvalue { i8*, i32 } %59, 0
  %61 = extractvalue { i8*, i32 } %59, 1
  %62 = getelementptr inbounds %"class.std::__cxx11::basic_string", %"class.std::__cxx11::basic_string"* %5, i64 0, i32 0, i32 0
  %63 = load i8*, i8** %62, align 8, !tbaa !32
  %64 = icmp eq i8* %63, %37
  br i1 %64, label %66, label %65

; <label>:65:                                     ; preds = %58
  call void @_ZdlPv(i8* %63) #2
  br label %66

; <label>:66:                                     ; preds = %65, %58
  call void @llvm.lifetime.end.p0i8(i64 32, i8* nonnull %34) #2
  br label %475

.loopexit4.loopexit:                              ; preds = %137
  %67 = ptrtoint i64* %146 to i64
  br label %.loopexit4

.loopexit4:                                       ; preds = %.loopexit4.loopexit, %46
  %68 = phi i64* [ %52, %46 ], [ %138, %.loopexit4.loopexit ]
  %69 = phi i64* [ %52, %46 ], [ %139, %.loopexit4.loopexit ]
  %70 = phi i64* [ %52, %46 ], [ %140, %.loopexit4.loopexit ]
  %71 = phi i64 [ 0, %46 ], [ %67, %.loopexit4.loopexit ]
  %72 = phi i64 [ 0, %46 ], [ %144, %.loopexit4.loopexit ]
  %73 = phi i64 [ %50, %46 ], [ %150, %.loopexit4.loopexit ]
  %74 = icmp ult i64 %73, %1
  br i1 %74, label %75, label %80

; <label>:75:                                     ; preds = %.loopexit4
  %76 = sub i64 %1, %73
  invoke void @_ZNSt6vectorImSaImEE17_M_default_appendEm(%"class.std::vector"* nonnull %0, i64 %76)
          to label %77 unwind label %53

; <label>:77:                                     ; preds = %75
  %78 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %79 = load i64*, i64** %78, align 8, !tbaa !23
  br label %160

; <label>:80:                                     ; preds = %.loopexit4
  %81 = icmp ugt i64 %73, %1
  br i1 %81, label %82, label %160

; <label>:82:                                     ; preds = %80
  %83 = getelementptr inbounds i64, i64* %68, i64 %1
  store i64* %83, i64** %15, align 8, !tbaa !22
  br label %160

; <label>:84:                                     ; preds = %.preheader51, %137
  %85 = phi i64* [ %139, %137 ], [ %52, %.preheader51 ]
  %86 = phi i64* [ %140, %137 ], [ %52, %.preheader51 ]
  %87 = phi i64 [ %141, %137 ], [ %48, %.preheader51 ]
  %88 = phi i64 [ %142, %137 ], [ %47, %.preheader51 ]
  %89 = phi i64* [ %138, %137 ], [ %52, %.preheader51 ]
  %90 = phi i64 [ %148, %137 ], [ %1, %.preheader51 ]
  %91 = phi i64* [ %145, %137 ], [ null, %.preheader51 ]
  %92 = phi i64 [ %144, %137 ], [ 0, %.preheader51 ]
  %93 = phi i64 [ %147, %137 ], [ 0, %.preheader51 ]
  %94 = getelementptr inbounds i64, i64* %89, i64 %90
  %95 = inttoptr i64 %93 to i64*
  %96 = icmp eq i64* %91, %95
  br i1 %96, label %100, label %97

; <label>:97:                                     ; preds = %84
  %98 = load i64, i64* %94, align 8, !tbaa !2
  store i64 %98, i64* %95, align 8, !tbaa !2
  %99 = inttoptr i64 %87 to i64*
  br label %137

; <label>:100:                                    ; preds = %84
  %101 = sub i64 %93, %92
  %102 = ashr exact i64 %101, 3
  %103 = icmp eq i64 %101, 0
  %104 = select i1 %103, i64 1, i64 %102
  %105 = add nsw i64 %104, %102
  %106 = icmp ult i64 %105, %102
  %107 = icmp ugt i64 %105, 2305843009213693951
  %108 = or i1 %106, %107
  %109 = select i1 %108, i64 2305843009213693951, i64 %105
  %110 = icmp eq i64 %109, 0
  br i1 %110, label %120, label %111

; <label>:111:                                    ; preds = %100
  %112 = icmp ugt i64 %109, 2305843009213693951
  br i1 %112, label %113, label %115

; <label>:113:                                    ; preds = %111
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %114 unwind label %154

; <label>:114:                                    ; preds = %113
  unreachable

; <label>:115:                                    ; preds = %111
  %116 = shl i64 %109, 3
  %117 = invoke i8* @_Znwm(i64 %116)
          to label %118 unwind label %152

; <label>:118:                                    ; preds = %115
  %119 = bitcast i8* %117 to i64*
  br label %120

; <label>:120:                                    ; preds = %118, %100
  %121 = phi i8* [ %117, %118 ], [ null, %100 ]
  %122 = phi i64* [ %119, %118 ], [ null, %100 ]
  %123 = getelementptr inbounds i64, i64* %122, i64 %102
  %124 = load i64, i64* %94, align 8, !tbaa !2
  store i64 %124, i64* %123, align 8, !tbaa !2
  br i1 %103, label %127, label %125

; <label>:125:                                    ; preds = %120
  %126 = inttoptr i64 %92 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %121, i8* %126, i64 %101, i32 8, i1 false) #2
  br label %127

; <label>:127:                                    ; preds = %125, %120
  %128 = icmp eq i64 %92, 0
  br i1 %128, label %131, label %129

; <label>:129:                                    ; preds = %127
  %130 = inttoptr i64 %92 to i8*
  call void @_ZdlPv(i8* %130) #2
  br label %131

; <label>:131:                                    ; preds = %129, %127
  %132 = ptrtoint i8* %121 to i64
  %133 = getelementptr inbounds i64, i64* %122, i64 %109
  %134 = load i64, i64* %33, align 8, !tbaa !22
  %135 = load i64, i64* %13, align 8, !tbaa !19
  %136 = inttoptr i64 %135 to i64*
  br label %137

; <label>:137:                                    ; preds = %131, %97
  %138 = phi i64* [ %136, %131 ], [ %99, %97 ]
  %139 = phi i64* [ %136, %131 ], [ %85, %97 ]
  %140 = phi i64* [ %136, %131 ], [ %86, %97 ]
  %141 = phi i64 [ %135, %131 ], [ %87, %97 ]
  %142 = phi i64 [ %134, %131 ], [ %88, %97 ]
  %143 = phi i64* [ %123, %131 ], [ %95, %97 ]
  %144 = phi i64 [ %132, %131 ], [ %92, %97 ]
  %145 = phi i64* [ %133, %131 ], [ %91, %97 ]
  %146 = getelementptr inbounds i64, i64* %143, i64 1
  %147 = ptrtoint i64* %146 to i64
  %148 = add nuw i64 %90, 1
  %149 = sub i64 %142, %141
  %150 = ashr exact i64 %149, 3
  %151 = icmp ult i64 %148, %150
  br i1 %151, label %84, label %.loopexit4.loopexit

; <label>:152:                                    ; preds = %115
  %153 = landingpad { i8*, i32 }
          cleanup
  br label %156

; <label>:154:                                    ; preds = %113
  %155 = landingpad { i8*, i32 }
          cleanup
  br label %156

; <label>:156:                                    ; preds = %154, %152
  %157 = phi { i8*, i32 } [ %153, %152 ], [ %155, %154 ]
  %158 = extractvalue { i8*, i32 } %157, 0
  %159 = extractvalue { i8*, i32 } %157, 1
  br label %475

; <label>:160:                                    ; preds = %82, %80, %77
  %161 = phi i64* [ %79, %77 ], [ %69, %82 ], [ %69, %80 ]
  %162 = phi i64* [ %79, %77 ], [ %70, %82 ], [ %70, %80 ]
  %163 = lshr i64 %1, 1
  %164 = icmp eq i64 %163, 0
  %165 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  br i1 %164, label %.loopexit3, label %166

; <label>:166:                                    ; preds = %160
  %167 = add i64 %1, -1
  %168 = getelementptr inbounds i64, i64* %162, i64 %167
  %169 = load i64, i64* %162, align 8, !tbaa !2
  %170 = load i64, i64* %168, align 8, !tbaa !2
  store i64 %170, i64* %162, align 8, !tbaa !2
  store i64 %169, i64* %168, align 8, !tbaa !2
  %171 = icmp eq i64 %163, 1
  br i1 %171, label %.loopexit3, label %.preheader50

.preheader50:                                     ; preds = %166
  br label %184

.loopexit3:                                       ; preds = %184, %166, %160
  %172 = phi i64* [ %162, %160 ], [ %161, %166 ], [ %161, %184 ]
  %173 = load i64*, i64** %15, align 8, !tbaa !23
  %174 = icmp eq i64* %172, %173
  br i1 %174, label %193, label %175

; <label>:175:                                    ; preds = %.loopexit3
  %176 = ptrtoint i64* %173 to i64
  %177 = ptrtoint i64* %172 to i64
  %178 = sub i64 %176, %177
  %179 = ashr exact i64 %178, 3
  %180 = call i64 @llvm.ctlz.i64(i64 %179, i1 true) #2, !range !24
  %181 = shl nuw nsw i64 %180, 1
  %182 = xor i64 %181, 126
  invoke void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %172, i64* %173, i64 %182)
          to label %183 unwind label %53

; <label>:183:                                    ; preds = %175
  invoke void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64* %172, i64* %173)
          to label %193 unwind label %53

; <label>:184:                                    ; preds = %.preheader50, %184
  %185 = phi i64 [ %191, %184 ], [ 1, %.preheader50 ]
  %186 = getelementptr inbounds i64, i64* %161, i64 %185
  %187 = sub i64 %167, %185
  %188 = getelementptr inbounds i64, i64* %161, i64 %187
  %189 = load i64, i64* %186, align 8, !tbaa !2
  %190 = load i64, i64* %188, align 8, !tbaa !2
  store i64 %190, i64* %186, align 8, !tbaa !2
  store i64 %189, i64* %188, align 8, !tbaa !2
  %191 = add nuw nsw i64 %185, 1
  %192 = icmp eq i64 %191, %163
  br i1 %192, label %.loopexit3, label %184, !llvm.loop !48

; <label>:193:                                    ; preds = %183, %.loopexit3
  %194 = udiv i64 %1, %2
  %195 = add i64 %194, 1
  %196 = sub i64 %71, %72
  %197 = ashr exact i64 %196, 3
  %198 = icmp eq i64 %196, 0
  br i1 %198, label %.loopexit2, label %199

; <label>:199:                                    ; preds = %193
  %200 = inttoptr i64 %72 to i64*
  %201 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %202 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %203 = bitcast i64** %201 to i64*
  %204 = bitcast %"class.std::vector"* %4 to i64*
  %205 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %206 = icmp eq i64 %195, 0
  %207 = bitcast %"class.std::vector"* %4 to i8**
  %208 = load i64*, i64** %201, align 8, !tbaa !22
  %.pre = load i64*, i64** %202, align 8, !tbaa !28
  br label %223

.loopexit2:                                       ; preds = %.loopexit1, %193
  %209 = phi i64 [ 0, %193 ], [ %292, %.loopexit1 ]
  %210 = load i64, i64* %33, align 8, !tbaa !22
  %211 = load i64, i64* %13, align 8, !tbaa !19
  %212 = sub i64 %210, %211
  %213 = ashr exact i64 %212, 3
  %214 = icmp ult i64 %209, %213
  br i1 %214, label %215, label %.loopexit

; <label>:215:                                    ; preds = %.loopexit2
  %216 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 1
  %217 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 2
  %218 = bitcast i64** %216 to i64*
  %219 = bitcast %"class.std::vector"* %4 to i64*
  %220 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %221 = bitcast %"class.std::vector"* %4 to i8**
  %222 = load i64*, i64** %216, align 8, !tbaa !22
  %.pre26 = load i64*, i64** %217, align 8, !tbaa !28
  br label %379

; <label>:223:                                    ; preds = %.loopexit1, %199
  %224 = phi i64* [ %.pre, %199 ], [ %289, %.loopexit1 ]
  %225 = phi i64* [ %208, %199 ], [ %290, %.loopexit1 ]
  %226 = phi i64 [ 0, %199 ], [ %291, %.loopexit1 ]
  %227 = phi i64 [ 0, %199 ], [ %292, %.loopexit1 ]
  %228 = getelementptr inbounds i64, i64* %200, i64 %226
  %229 = icmp eq i64* %225, %224
  %230 = ptrtoint i64* %225 to i64
  br i1 %229, label %234, label %231

; <label>:231:                                    ; preds = %223
  %232 = load i64, i64* %228, align 8, !tbaa !2
  store i64 %232, i64* %225, align 8, !tbaa !2
  %233 = getelementptr inbounds i64, i64* %225, i64 1
  store i64* %233, i64** %201, align 8, !tbaa !22
  br label %286

; <label>:234:                                    ; preds = %223
  %235 = load i64, i64* %204, align 8, !tbaa !23
  %236 = sub i64 %230, %235
  %237 = ashr exact i64 %236, 3
  %238 = icmp eq i64 %236, 0
  %239 = select i1 %238, i64 1, i64 %237
  %240 = add nsw i64 %239, %237
  %241 = icmp ult i64 %240, %237
  %242 = icmp ugt i64 %240, 2305843009213693951
  %243 = or i1 %241, %242
  %244 = select i1 %243, i64 2305843009213693951, i64 %240
  %245 = icmp eq i64 %244, 0
  %246 = inttoptr i64 %235 to i64*
  br i1 %245, label %257, label %247

; <label>:247:                                    ; preds = %234
  %248 = icmp ugt i64 %244, 2305843009213693951
  br i1 %248, label %249, label %251

; <label>:249:                                    ; preds = %247
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %250 unwind label %296

; <label>:250:                                    ; preds = %249
  unreachable

; <label>:251:                                    ; preds = %247
  %252 = shl i64 %244, 3
  %253 = invoke i8* @_Znwm(i64 %252)
          to label %254 unwind label %294

; <label>:254:                                    ; preds = %251
  %255 = bitcast i8* %253 to i64*
  %256 = load i64*, i64** %205, align 8, !tbaa !19
  br label %257

; <label>:257:                                    ; preds = %254, %234
  %258 = phi i64* [ %256, %254 ], [ %246, %234 ]
  %259 = phi i8* [ %253, %254 ], [ null, %234 ]
  %260 = phi i64* [ %255, %254 ], [ null, %234 ]
  %261 = getelementptr inbounds i64, i64* %260, i64 %237
  %262 = load i64, i64* %228, align 8, !tbaa !2
  store i64 %262, i64* %261, align 8, !tbaa !2
  %263 = ptrtoint i64* %258 to i64
  %264 = sub i64 %230, %263
  %265 = ashr exact i64 %264, 3
  %266 = icmp eq i64 %264, 0
  br i1 %266, label %269, label %267

; <label>:267:                                    ; preds = %257
  %268 = bitcast i64* %258 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %259, i8* %268, i64 %264, i32 8, i1 false) #2
  br label %269

; <label>:269:                                    ; preds = %267, %257
  %270 = getelementptr inbounds i64, i64* %260, i64 %265
  %271 = getelementptr inbounds i64, i64* %270, i64 1
  %272 = load i64, i64* %203, align 8, !tbaa !22
  %273 = sub i64 %272, %230
  %274 = ashr exact i64 %273, 3
  %275 = icmp eq i64 %273, 0
  br i1 %275, label %279, label %276

; <label>:276:                                    ; preds = %269
  %277 = bitcast i64* %271 to i8*
  %278 = bitcast i64* %224 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %277, i8* %278, i64 %273, i32 8, i1 false) #2
  br label %279

; <label>:279:                                    ; preds = %276, %269
  %280 = getelementptr inbounds i64, i64* %271, i64 %274
  %281 = icmp eq i64* %258, null
  br i1 %281, label %284, label %282

; <label>:282:                                    ; preds = %279
  %283 = bitcast i64* %258 to i8*
  call void @_ZdlPv(i8* %283) #2
  br label %284

; <label>:284:                                    ; preds = %282, %279
  store i8* %259, i8** %207, align 8, !tbaa !19
  store i64* %280, i64** %201, align 8, !tbaa !22
  %285 = getelementptr inbounds i64, i64* %260, i64 %244
  store i64* %285, i64** %202, align 8, !tbaa !28
  br label %286

; <label>:286:                                    ; preds = %284, %231
  %287 = phi i64* [ %285, %284 ], [ %224, %231 ]
  %288 = phi i64* [ %280, %284 ], [ %233, %231 ]
  br i1 %206, label %.loopexit1, label %.preheader

.preheader:                                       ; preds = %286
  br label %302

.loopexit1:                                       ; preds = %366, %286
  %289 = phi i64* [ %287, %286 ], [ %367, %366 ]
  %290 = phi i64* [ %288, %286 ], [ %368, %366 ]
  %291 = add nuw i64 %226, 1
  %292 = add i64 %227, %195
  %293 = icmp ult i64 %291, %197
  br i1 %293, label %223, label %.loopexit2

; <label>:294:                                    ; preds = %251
  %295 = landingpad { i8*, i32 }
          cleanup
  br label %298

; <label>:296:                                    ; preds = %249
  %297 = landingpad { i8*, i32 }
          cleanup
  br label %298

; <label>:298:                                    ; preds = %296, %294
  %299 = phi { i8*, i32 } [ %295, %294 ], [ %297, %296 ]
  %300 = extractvalue { i8*, i32 } %299, 0
  %301 = extractvalue { i8*, i32 } %299, 1
  br label %475

; <label>:302:                                    ; preds = %.preheader, %366
  %303 = phi i64* [ %367, %366 ], [ %287, %.preheader ]
  %304 = phi i64* [ %368, %366 ], [ %288, %.preheader ]
  %305 = phi i64 [ %369, %366 ], [ 0, %.preheader ]
  %306 = add i64 %305, %227
  %307 = load i64*, i64** %165, align 8, !tbaa !19
  %308 = getelementptr inbounds i64, i64* %307, i64 %306
  %309 = icmp eq i64* %304, %303
  %310 = ptrtoint i64* %304 to i64
  br i1 %309, label %314, label %311

; <label>:311:                                    ; preds = %302
  %312 = load i64, i64* %308, align 8, !tbaa !2
  store i64 %312, i64* %304, align 8, !tbaa !2
  %313 = getelementptr inbounds i64, i64* %304, i64 1
  store i64* %313, i64** %201, align 8, !tbaa !22
  br label %366

; <label>:314:                                    ; preds = %302
  %315 = load i64, i64* %204, align 8, !tbaa !23
  %316 = sub i64 %310, %315
  %317 = ashr exact i64 %316, 3
  %318 = icmp eq i64 %316, 0
  %319 = select i1 %318, i64 1, i64 %317
  %320 = add nsw i64 %319, %317
  %321 = icmp ult i64 %320, %317
  %322 = icmp ugt i64 %320, 2305843009213693951
  %323 = or i1 %321, %322
  %324 = select i1 %323, i64 2305843009213693951, i64 %320
  %325 = icmp eq i64 %324, 0
  %326 = inttoptr i64 %315 to i64*
  br i1 %325, label %337, label %327

; <label>:327:                                    ; preds = %314
  %328 = icmp ugt i64 %324, 2305843009213693951
  br i1 %328, label %329, label %331

; <label>:329:                                    ; preds = %327
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %330 unwind label %373

; <label>:330:                                    ; preds = %329
  unreachable

; <label>:331:                                    ; preds = %327
  %332 = shl i64 %324, 3
  %333 = invoke i8* @_Znwm(i64 %332)
          to label %334 unwind label %371

; <label>:334:                                    ; preds = %331
  %335 = bitcast i8* %333 to i64*
  %336 = load i64*, i64** %205, align 8, !tbaa !19
  br label %337

; <label>:337:                                    ; preds = %334, %314
  %338 = phi i64* [ %336, %334 ], [ %326, %314 ]
  %339 = phi i8* [ %333, %334 ], [ null, %314 ]
  %340 = phi i64* [ %335, %334 ], [ null, %314 ]
  %341 = getelementptr inbounds i64, i64* %340, i64 %317
  %342 = load i64, i64* %308, align 8, !tbaa !2
  store i64 %342, i64* %341, align 8, !tbaa !2
  %343 = ptrtoint i64* %338 to i64
  %344 = sub i64 %310, %343
  %345 = ashr exact i64 %344, 3
  %346 = icmp eq i64 %344, 0
  br i1 %346, label %349, label %347

; <label>:347:                                    ; preds = %337
  %348 = bitcast i64* %338 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %339, i8* %348, i64 %344, i32 8, i1 false) #2
  br label %349

; <label>:349:                                    ; preds = %347, %337
  %350 = getelementptr inbounds i64, i64* %340, i64 %345
  %351 = getelementptr inbounds i64, i64* %350, i64 1
  %352 = load i64, i64* %203, align 8, !tbaa !22
  %353 = sub i64 %352, %310
  %354 = ashr exact i64 %353, 3
  %355 = icmp eq i64 %353, 0
  br i1 %355, label %359, label %356

; <label>:356:                                    ; preds = %349
  %357 = bitcast i64* %351 to i8*
  %358 = bitcast i64* %303 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %357, i8* %358, i64 %353, i32 8, i1 false) #2
  br label %359

; <label>:359:                                    ; preds = %356, %349
  %360 = getelementptr inbounds i64, i64* %351, i64 %354
  %361 = icmp eq i64* %338, null
  br i1 %361, label %364, label %362

; <label>:362:                                    ; preds = %359
  %363 = bitcast i64* %338 to i8*
  call void @_ZdlPv(i8* %363) #2
  br label %364

; <label>:364:                                    ; preds = %362, %359
  store i8* %339, i8** %207, align 8, !tbaa !19
  store i64* %360, i64** %201, align 8, !tbaa !22
  %365 = getelementptr inbounds i64, i64* %340, i64 %324
  store i64* %365, i64** %202, align 8, !tbaa !28
  br label %366

; <label>:366:                                    ; preds = %364, %311
  %367 = phi i64* [ %365, %364 ], [ %303, %311 ]
  %368 = phi i64* [ %360, %364 ], [ %313, %311 ]
  %369 = add nuw i64 %305, 1
  %370 = icmp ult i64 %369, %195
  br i1 %370, label %302, label %.loopexit1

; <label>:371:                                    ; preds = %331
  %372 = landingpad { i8*, i32 }
          cleanup
  br label %375

; <label>:373:                                    ; preds = %329
  %374 = landingpad { i8*, i32 }
          cleanup
  br label %375

; <label>:375:                                    ; preds = %373, %371
  %376 = phi { i8*, i32 } [ %372, %371 ], [ %374, %373 ]
  %377 = extractvalue { i8*, i32 } %376, 0
  %378 = extractvalue { i8*, i32 } %376, 1
  br label %475

; <label>:379:                                    ; preds = %446, %215
  %380 = phi i64* [ %.pre26, %215 ], [ %447, %446 ]
  %381 = phi i64 [ %211, %215 ], [ %448, %446 ]
  %382 = phi i64 [ %210, %215 ], [ %449, %446 ]
  %383 = phi i64* [ %222, %215 ], [ %450, %446 ]
  %384 = phi i64 [ %209, %215 ], [ %451, %446 ]
  %385 = inttoptr i64 %381 to i64*
  %386 = getelementptr inbounds i64, i64* %385, i64 %384
  %387 = icmp eq i64* %383, %380
  %388 = ptrtoint i64* %383 to i64
  br i1 %387, label %392, label %389

; <label>:389:                                    ; preds = %379
  %390 = load i64, i64* %386, align 8, !tbaa !2
  store i64 %390, i64* %383, align 8, !tbaa !2
  %391 = getelementptr inbounds i64, i64* %383, i64 1
  store i64* %391, i64** %216, align 8, !tbaa !22
  br label %446

; <label>:392:                                    ; preds = %379
  %393 = load i64, i64* %219, align 8, !tbaa !23
  %394 = sub i64 %388, %393
  %395 = ashr exact i64 %394, 3
  %396 = icmp eq i64 %394, 0
  %397 = select i1 %396, i64 1, i64 %395
  %398 = add nsw i64 %397, %395
  %399 = icmp ult i64 %398, %395
  %400 = icmp ugt i64 %398, 2305843009213693951
  %401 = or i1 %399, %400
  %402 = select i1 %401, i64 2305843009213693951, i64 %398
  %403 = icmp eq i64 %402, 0
  %404 = inttoptr i64 %393 to i64*
  br i1 %403, label %415, label %405

; <label>:405:                                    ; preds = %392
  %406 = icmp ugt i64 %402, 2305843009213693951
  br i1 %406, label %407, label %409

; <label>:407:                                    ; preds = %405
  invoke void @_ZSt17__throw_bad_allocv() #16
          to label %408 unwind label %457

; <label>:408:                                    ; preds = %407
  unreachable

; <label>:409:                                    ; preds = %405
  %410 = shl i64 %402, 3
  %411 = invoke i8* @_Znwm(i64 %410)
          to label %412 unwind label %455

; <label>:412:                                    ; preds = %409
  %413 = bitcast i8* %411 to i64*
  %414 = load i64*, i64** %220, align 8, !tbaa !19
  br label %415

; <label>:415:                                    ; preds = %412, %392
  %416 = phi i64* [ %414, %412 ], [ %404, %392 ]
  %417 = phi i8* [ %411, %412 ], [ null, %392 ]
  %418 = phi i64* [ %413, %412 ], [ null, %392 ]
  %419 = getelementptr inbounds i64, i64* %418, i64 %395
  %420 = load i64, i64* %386, align 8, !tbaa !2
  store i64 %420, i64* %419, align 8, !tbaa !2
  %421 = ptrtoint i64* %416 to i64
  %422 = sub i64 %388, %421
  %423 = ashr exact i64 %422, 3
  %424 = icmp eq i64 %422, 0
  br i1 %424, label %427, label %425

; <label>:425:                                    ; preds = %415
  %426 = bitcast i64* %416 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* %417, i8* %426, i64 %422, i32 8, i1 false) #2
  br label %427

; <label>:427:                                    ; preds = %425, %415
  %428 = getelementptr inbounds i64, i64* %418, i64 %423
  %429 = getelementptr inbounds i64, i64* %428, i64 1
  %430 = load i64, i64* %218, align 8, !tbaa !22
  %431 = sub i64 %430, %388
  %432 = ashr exact i64 %431, 3
  %433 = icmp eq i64 %431, 0
  br i1 %433, label %437, label %434

; <label>:434:                                    ; preds = %427
  %435 = bitcast i64* %429 to i8*
  %436 = bitcast i64* %380 to i8*
  call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %435, i8* %436, i64 %431, i32 8, i1 false) #2
  br label %437

; <label>:437:                                    ; preds = %434, %427
  %438 = getelementptr inbounds i64, i64* %429, i64 %432
  %439 = icmp eq i64* %416, null
  br i1 %439, label %442, label %440

; <label>:440:                                    ; preds = %437
  %441 = bitcast i64* %416 to i8*
  call void @_ZdlPv(i8* %441) #2
  br label %442

; <label>:442:                                    ; preds = %440, %437
  store i8* %417, i8** %221, align 8, !tbaa !19
  store i64* %438, i64** %216, align 8, !tbaa !22
  %443 = getelementptr inbounds i64, i64* %418, i64 %402
  store i64* %443, i64** %217, align 8, !tbaa !28
  %444 = load i64, i64* %33, align 8, !tbaa !22
  %445 = load i64, i64* %13, align 8, !tbaa !19
  br label %446

; <label>:446:                                    ; preds = %442, %389
  %447 = phi i64* [ %443, %442 ], [ %380, %389 ]
  %448 = phi i64 [ %445, %442 ], [ %381, %389 ]
  %449 = phi i64 [ %444, %442 ], [ %382, %389 ]
  %450 = phi i64* [ %438, %442 ], [ %391, %389 ]
  %451 = add nuw i64 %384, 1
  %452 = sub i64 %449, %448
  %453 = ashr exact i64 %452, 3
  %454 = icmp ult i64 %451, %453
  br i1 %454, label %379, label %.loopexit

; <label>:455:                                    ; preds = %409
  %456 = landingpad { i8*, i32 }
          cleanup
  br label %459

; <label>:457:                                    ; preds = %.loopexit, %407
  %458 = landingpad { i8*, i32 }
          cleanup
  br label %459

; <label>:459:                                    ; preds = %457, %455
  %460 = phi { i8*, i32 } [ %456, %455 ], [ %458, %457 ]
  %461 = extractvalue { i8*, i32 } %460, 0
  %462 = extractvalue { i8*, i32 } %460, 1
  br label %475

.loopexit:                                        ; preds = %446, %.loopexit2
  %463 = invoke dereferenceable(24) %"class.std::vector"* @_ZNSt6vectorImSaImEEaSERKS1_(%"class.std::vector"* nonnull %0, %"class.std::vector"* nonnull dereferenceable(24) %4)
          to label %464 unwind label %457

; <label>:464:                                    ; preds = %.loopexit
  %465 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %466 = load i64*, i64** %465, align 8, !tbaa !19
  %467 = icmp eq i64* %466, null
  br i1 %467, label %470, label %468

; <label>:468:                                    ; preds = %464
  %469 = bitcast i64* %466 to i8*
  call void @_ZdlPv(i8* %469) #2
  br label %470

; <label>:470:                                    ; preds = %468, %464
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %471 = icmp eq i64 %72, 0
  br i1 %471, label %474, label %472

; <label>:472:                                    ; preds = %470
  %473 = inttoptr i64 %72 to i8*
  call void @_ZdlPv(i8* %473) #2
  br label %474

; <label>:474:                                    ; preds = %472, %470
  ret void

; <label>:475:                                    ; preds = %459, %375, %298, %156, %66, %53
  %476 = phi i64 [ %54, %53 ], [ %92, %156 ], [ %72, %375 ], [ %72, %298 ], [ %72, %459 ], [ 0, %66 ]
  %477 = phi i32 [ %57, %53 ], [ %159, %156 ], [ %378, %375 ], [ %301, %298 ], [ %462, %459 ], [ %61, %66 ]
  %478 = phi i8* [ %56, %53 ], [ %158, %156 ], [ %377, %375 ], [ %300, %298 ], [ %461, %459 ], [ %60, %66 ]
  %479 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %4, i64 0, i32 0, i32 0, i32 0
  %480 = load i64*, i64** %479, align 8, !tbaa !19
  %481 = icmp eq i64* %480, null
  br i1 %481, label %484, label %482

; <label>:482:                                    ; preds = %475
  %483 = bitcast i64* %480 to i8*
  call void @_ZdlPv(i8* %483) #2
  br label %484

; <label>:484:                                    ; preds = %482, %475
  call void @llvm.lifetime.end.p0i8(i64 24, i8* nonnull %7) #2
  %485 = icmp eq i64 %476, 0
  br i1 %485, label %488, label %486

; <label>:486:                                    ; preds = %484
  %487 = inttoptr i64 %476 to i8*
  call void @_ZdlPv(i8* %487) #2
  br label %488

; <label>:488:                                    ; preds = %486, %484
  %489 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %490 = load i64*, i64** %489, align 8, !tbaa !19
  %491 = icmp eq i64* %490, null
  br i1 %491, label %494, label %492

; <label>:492:                                    ; preds = %488
  %493 = bitcast i64* %490 to i8*
  call void @_ZdlPv(i8* %493) #2
  br label %494

; <label>:494:                                    ; preds = %492, %488
  %495 = insertvalue { i8*, i32 } undef, i8* %478, 0
  %496 = insertvalue { i8*, i32 } %495, i32 %477, 1
  resume { i8*, i32 } %496
}

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZNSo9_M_insertIdEERSoT_(%"class.std::basic_ostream"*, double) local_unnamed_addr #0

; Function Attrs: inlinehint uwtable
define linkonce_odr void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64*, i64*, i32, i1 zeroext) local_unnamed_addr #14 comdat {
  %5 = ptrtoint i64* %0 to i64
  %6 = alloca %"struct.__gnu_cxx::__ops::_Iter_comp_iter", align 1
  %7 = ptrtoint i64* %1 to i64
  %8 = sub i64 %7, %5
  %9 = icmp slt i64 %8, 192
  br i1 %9, label %21, label %10

; <label>:10:                                     ; preds = %4
  %11 = getelementptr inbounds i64, i64* %1, i64 -1
  %12 = getelementptr inbounds i64, i64* %1, i64 -2
  %13 = getelementptr inbounds i64, i64* %1, i64 -3
  br label %14

; <label>:14:                                     ; preds = %.loopexit9, %10
  %15 = phi i64 [ %8, %10 ], [ %321, %.loopexit9 ]
  %16 = phi i32 [ %2, %10 ], [ %537, %.loopexit9 ]
  %17 = phi i1 [ %3, %10 ], [ false, %.loopexit9 ]
  %18 = phi i64 [ %5, %10 ], [ %320, %.loopexit9 ]
  br label %117

.loopexit17:                                      ; preds = %.loopexit9, %.loopexit6, %424
  %19 = phi i64* [ %319, %424 ], [ %533, %.loopexit6 ], [ %319, %.loopexit9 ]
  %20 = icmp eq i64* %19, %1
  br i1 %20, label %.loopexit, label %67

; <label>:21:                                     ; preds = %4
  %22 = icmp eq i64* %0, %1
  br i1 %3, label %23, label %66

; <label>:23:                                     ; preds = %21
  br i1 %22, label %.loopexit, label %24

; <label>:24:                                     ; preds = %23
  %25 = getelementptr inbounds i64, i64* %0, i64 1
  %26 = icmp eq i64* %25, %1
  br i1 %26, label %.loopexit, label %27

; <label>:27:                                     ; preds = %24
  %28 = getelementptr i64, i64* %1, i64 -2
  %29 = ptrtoint i64* %28 to i64
  %30 = sub i64 %29, %5
  %31 = and i64 %30, 8
  %32 = icmp eq i64 %31, 0
  br i1 %32, label %33, label %39

; <label>:33:                                     ; preds = %27
  %34 = load i64, i64* %25, align 8, !tbaa !2
  %35 = load i64, i64* %0, align 8, !tbaa !2
  %36 = icmp ult i64 %34, %35
  br i1 %36, label %.preheader337, label %37

.preheader337:                                    ; preds = %33
  store i64 %35, i64* %25, align 8, !tbaa !2
  store i64 %34, i64* %0, align 8, !tbaa !2
  br label %37

; <label>:37:                                     ; preds = %.preheader337, %33
  %38 = getelementptr inbounds i64, i64* %0, i64 2
  br label %39

; <label>:39:                                     ; preds = %37, %27
  %40 = phi i64* [ %25, %27 ], [ %38, %37 ]
  %41 = phi i64* [ %0, %27 ], [ %25, %37 ]
  %42 = icmp ult i64 %30, 8
  br i1 %42, label %.loopexit, label %.preheader336

.preheader336:                                    ; preds = %39
  br label %43

; <label>:43:                                     ; preds = %.preheader336, %551
  %44 = phi i64* [ %552, %551 ], [ %40, %.preheader336 ]
  %45 = phi i64* [ %63, %551 ], [ %41, %.preheader336 ]
  %46 = load i64, i64* %44, align 8, !tbaa !2
  %47 = load i64, i64* %45, align 8, !tbaa !2
  %48 = icmp ult i64 %46, %47
  br i1 %48, label %.preheader335, label %61

.preheader335:                                    ; preds = %43
  br label %49

; <label>:49:                                     ; preds = %.preheader335, %55
  %50 = phi i64 [ %57, %55 ], [ %47, %.preheader335 ]
  %51 = phi i64* [ %56, %55 ], [ %45, %.preheader335 ]
  %52 = phi i64* [ %53, %55 ], [ %44, %.preheader335 ]
  %53 = getelementptr inbounds i64, i64* %52, i64 -1
  store i64 %50, i64* %52, align 8, !tbaa !2
  %54 = icmp eq i64* %53, %0
  br i1 %54, label %59, label %55

; <label>:55:                                     ; preds = %49
  %56 = getelementptr inbounds i64, i64* %51, i64 -1
  %57 = load i64, i64* %56, align 8, !tbaa !2
  %58 = icmp ult i64 %46, %57
  br i1 %58, label %49, label %59

; <label>:59:                                     ; preds = %55, %49
  %60 = phi i64* [ %0, %49 ], [ %53, %55 ]
  store i64 %46, i64* %60, align 8, !tbaa !2
  %.pre173 = load i64, i64* %44, align 8, !tbaa !2
  br label %61

; <label>:61:                                     ; preds = %59, %43
  %62 = phi i64 [ %.pre173, %59 ], [ %46, %43 ]
  %63 = getelementptr inbounds i64, i64* %44, i64 1
  %64 = load i64, i64* %63, align 8, !tbaa !2
  %65 = icmp ult i64 %64, %62
  br i1 %65, label %.preheader, label %551

.preheader:                                       ; preds = %61
  br label %539

; <label>:66:                                     ; preds = %21
  br i1 %22, label %.loopexit, label %67

; <label>:67:                                     ; preds = %66, %.loopexit17
  %68 = phi i64* [ %19, %.loopexit17 ], [ %0, %66 ]
  %69 = getelementptr inbounds i64, i64* %68, i64 1
  %70 = icmp eq i64* %69, %1
  br i1 %70, label %.loopexit, label %71

; <label>:71:                                     ; preds = %67
  %72 = ptrtoint i64* %68 to i64
  %73 = getelementptr i64, i64* %1, i64 -2
  %74 = ptrtoint i64* %73 to i64
  %75 = sub i64 %74, %72
  %76 = and i64 %75, 8
  %77 = icmp eq i64 %76, 0
  br i1 %77, label %78, label %93

; <label>:78:                                     ; preds = %71
  %79 = load i64, i64* %69, align 8, !tbaa !2
  %80 = load i64, i64* %68, align 8, !tbaa !2
  %81 = icmp ult i64 %79, %80
  br i1 %81, label %.preheader342, label %91

.preheader342:                                    ; preds = %78
  br label %82

; <label>:82:                                     ; preds = %.preheader342, %82
  %83 = phi i64 [ %88, %82 ], [ %80, %.preheader342 ]
  %84 = phi i64* [ %87, %82 ], [ %68, %.preheader342 ]
  %85 = phi i64* [ %86, %82 ], [ %69, %.preheader342 ]
  %86 = getelementptr inbounds i64, i64* %85, i64 -1
  store i64 %83, i64* %85, align 8, !tbaa !2
  %87 = getelementptr inbounds i64, i64* %84, i64 -1
  %88 = load i64, i64* %87, align 8, !tbaa !2
  %89 = icmp ult i64 %79, %88
  br i1 %89, label %82, label %90

; <label>:90:                                     ; preds = %82
  store i64 %79, i64* %86, align 8, !tbaa !2
  br label %91

; <label>:91:                                     ; preds = %90, %78
  %92 = getelementptr inbounds i64, i64* %68, i64 2
  br label %93

; <label>:93:                                     ; preds = %91, %71
  %94 = phi i64* [ %69, %71 ], [ %92, %91 ]
  %95 = phi i64* [ %68, %71 ], [ %69, %91 ]
  %96 = icmp ult i64 %75, 8
  br i1 %96, label %.loopexit, label %.preheader340

.preheader340:                                    ; preds = %93
  br label %97

; <label>:97:                                     ; preds = %.preheader340, %563
  %98 = phi i64* [ %564, %563 ], [ %94, %.preheader340 ]
  %99 = phi i64* [ %114, %563 ], [ %95, %.preheader340 ]
  %100 = load i64, i64* %98, align 8, !tbaa !2
  %101 = load i64, i64* %99, align 8, !tbaa !2
  %102 = icmp ult i64 %100, %101
  br i1 %102, label %.preheader339, label %112

.preheader339:                                    ; preds = %97
  br label %103

; <label>:103:                                    ; preds = %.preheader339, %103
  %104 = phi i64 [ %109, %103 ], [ %101, %.preheader339 ]
  %105 = phi i64* [ %108, %103 ], [ %99, %.preheader339 ]
  %106 = phi i64* [ %107, %103 ], [ %98, %.preheader339 ]
  %107 = getelementptr inbounds i64, i64* %106, i64 -1
  store i64 %104, i64* %106, align 8, !tbaa !2
  %108 = getelementptr inbounds i64, i64* %105, i64 -1
  %109 = load i64, i64* %108, align 8, !tbaa !2
  %110 = icmp ult i64 %100, %109
  br i1 %110, label %103, label %111

; <label>:111:                                    ; preds = %103
  store i64 %100, i64* %107, align 8, !tbaa !2
  %.pre = load i64, i64* %98, align 8, !tbaa !2
  br label %112

; <label>:112:                                    ; preds = %111, %97
  %113 = phi i64 [ %.pre, %111 ], [ %100, %97 ]
  %114 = getelementptr inbounds i64, i64* %98, i64 1
  %115 = load i64, i64* %114, align 8, !tbaa !2
  %116 = icmp ult i64 %115, %113
  br i1 %116, label %.preheader338, label %563

.preheader338:                                    ; preds = %112
  br label %554

; <label>:117:                                    ; preds = %.loopexit6, %14
  %118 = phi i64 [ %15, %14 ], [ %535, %.loopexit6 ]
  %119 = phi i64 [ %18, %14 ], [ %534, %.loopexit6 ]
  %120 = lshr i64 %118, 4
  %121 = icmp sgt i64 %118, 1024
  %122 = inttoptr i64 %119 to i64*
  %123 = getelementptr inbounds i64, i64* %122, i64 %120
  br i1 %121, label %124, label %196

; <label>:124:                                    ; preds = %117
  %125 = load i64, i64* %123, align 8, !tbaa !2
  %126 = load i64, i64* %122, align 8, !tbaa !2
  %127 = icmp ult i64 %125, %126
  br i1 %127, label %128, label %129

; <label>:128:                                    ; preds = %124
  store i64 %125, i64* %122, align 8, !tbaa !2
  store i64 %126, i64* %123, align 8, !tbaa !2
  br label %129

; <label>:129:                                    ; preds = %128, %124
  %130 = phi i64 [ %125, %124 ], [ %126, %128 ]
  %131 = load i64, i64* %11, align 8, !tbaa !2
  %132 = icmp ult i64 %131, %130
  br i1 %132, label %133, label %135

; <label>:133:                                    ; preds = %129
  store i64 %131, i64* %123, align 8, !tbaa !2
  store i64 %130, i64* %11, align 8, !tbaa !2
  %134 = load i64, i64* %123, align 8, !tbaa !2
  br label %135

; <label>:135:                                    ; preds = %133, %129
  %136 = phi i64 [ %130, %129 ], [ %134, %133 ]
  %137 = load i64, i64* %122, align 8, !tbaa !2
  %138 = icmp ult i64 %136, %137
  br i1 %138, label %139, label %140

; <label>:139:                                    ; preds = %135
  store i64 %136, i64* %122, align 8, !tbaa !2
  store i64 %137, i64* %123, align 8, !tbaa !2
  br label %140

; <label>:140:                                    ; preds = %139, %135
  %141 = getelementptr inbounds i64, i64* %122, i64 1
  %142 = add nsw i64 %120, -1
  %143 = getelementptr inbounds i64, i64* %122, i64 %142
  %144 = load i64, i64* %143, align 8, !tbaa !2
  %145 = load i64, i64* %141, align 8, !tbaa !2
  %146 = icmp ult i64 %144, %145
  br i1 %146, label %147, label %148

; <label>:147:                                    ; preds = %140
  store i64 %144, i64* %141, align 8, !tbaa !2
  store i64 %145, i64* %143, align 8, !tbaa !2
  br label %148

; <label>:148:                                    ; preds = %147, %140
  %149 = phi i64 [ %144, %140 ], [ %145, %147 ]
  %150 = load i64, i64* %12, align 8, !tbaa !2
  %151 = icmp ult i64 %150, %149
  br i1 %151, label %152, label %154

; <label>:152:                                    ; preds = %148
  store i64 %150, i64* %143, align 8, !tbaa !2
  store i64 %149, i64* %12, align 8, !tbaa !2
  %153 = load i64, i64* %143, align 8, !tbaa !2
  br label %154

; <label>:154:                                    ; preds = %152, %148
  %155 = phi i64 [ %149, %148 ], [ %153, %152 ]
  %156 = load i64, i64* %141, align 8, !tbaa !2
  %157 = icmp ult i64 %155, %156
  br i1 %157, label %158, label %159

; <label>:158:                                    ; preds = %154
  store i64 %155, i64* %141, align 8, !tbaa !2
  store i64 %156, i64* %143, align 8, !tbaa !2
  br label %159

; <label>:159:                                    ; preds = %158, %154
  %160 = getelementptr inbounds i64, i64* %122, i64 2
  %161 = add nuw nsw i64 %120, 1
  %162 = getelementptr inbounds i64, i64* %122, i64 %161
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
  %169 = load i64, i64* %13, align 8, !tbaa !2
  %170 = icmp ult i64 %169, %168
  br i1 %170, label %171, label %173

; <label>:171:                                    ; preds = %167
  store i64 %169, i64* %162, align 8, !tbaa !2
  store i64 %168, i64* %13, align 8, !tbaa !2
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

; <label>:178:                                    ; preds = %177, %173
  %179 = phi i64 [ %174, %173 ], [ %175, %177 ]
  %180 = load i64, i64* %123, align 8, !tbaa !2
  %181 = load i64, i64* %143, align 8, !tbaa !2
  %182 = icmp ult i64 %180, %181
  br i1 %182, label %183, label %184

; <label>:183:                                    ; preds = %178
  store i64 %180, i64* %143, align 8, !tbaa !2
  store i64 %181, i64* %123, align 8, !tbaa !2
  br label %184

; <label>:184:                                    ; preds = %183, %178
  %185 = phi i64 [ %181, %178 ], [ %180, %183 ]
  %186 = phi i64 [ %180, %178 ], [ %181, %183 ]
  %187 = icmp ult i64 %179, %186
  br i1 %187, label %188, label %189

; <label>:188:                                    ; preds = %184
  store i64 %179, i64* %123, align 8, !tbaa !2
  store i64 %186, i64* %162, align 8, !tbaa !2
  br label %189

; <label>:189:                                    ; preds = %188, %184
  %190 = phi i64 [ %186, %184 ], [ %179, %188 ]
  %191 = icmp ult i64 %190, %185
  br i1 %191, label %192, label %193

; <label>:192:                                    ; preds = %189
  store i64 %190, i64* %143, align 8, !tbaa !2
  store i64 %185, i64* %123, align 8, !tbaa !2
  br label %193

; <label>:193:                                    ; preds = %192, %189
  %194 = phi i64 [ %190, %189 ], [ %185, %192 ]
  %195 = load i64, i64* %122, align 8, !tbaa !2
  store i64 %194, i64* %122, align 8, !tbaa !2
  store i64 %195, i64* %123, align 8, !tbaa !2
  br label %212

; <label>:196:                                    ; preds = %117
  %197 = load i64, i64* %122, align 8, !tbaa !2
  %198 = load i64, i64* %123, align 8, !tbaa !2
  %199 = icmp ult i64 %197, %198
  br i1 %199, label %200, label %201

; <label>:200:                                    ; preds = %196
  store i64 %197, i64* %123, align 8, !tbaa !2
  store i64 %198, i64* %122, align 8, !tbaa !2
  br label %201

; <label>:201:                                    ; preds = %200, %196
  %202 = phi i64 [ %197, %196 ], [ %198, %200 ]
  %203 = load i64, i64* %11, align 8, !tbaa !2
  %204 = icmp ult i64 %203, %202
  br i1 %204, label %205, label %207

; <label>:205:                                    ; preds = %201
  store i64 %203, i64* %122, align 8, !tbaa !2
  store i64 %202, i64* %11, align 8, !tbaa !2
  %206 = load i64, i64* %122, align 8, !tbaa !2
  br label %207

; <label>:207:                                    ; preds = %205, %201
  %208 = phi i64 [ %202, %201 ], [ %206, %205 ]
  %209 = load i64, i64* %123, align 8, !tbaa !2
  %210 = icmp ult i64 %208, %209
  br i1 %210, label %211, label %212

; <label>:211:                                    ; preds = %207
  store i64 %208, i64* %123, align 8, !tbaa !2
  store i64 %209, i64* %122, align 8, !tbaa !2
  br label %212

; <label>:212:                                    ; preds = %211, %207, %193
  br i1 %17, label %213, label %216

; <label>:213:                                    ; preds = %212
  %214 = inttoptr i64 %119 to i64*
  %215 = load i64, i64* %214, align 8, !tbaa !2
  br label %.loopexit16

; <label>:216:                                    ; preds = %212
  %217 = getelementptr inbounds i64, i64* %122, i64 -1
  %218 = load i64, i64* %217, align 8, !tbaa !2
  %219 = load i64, i64* %122, align 8, !tbaa !2
  %220 = icmp ult i64 %218, %219
  br i1 %220, label %.loopexit16.loopexit, label %.preheader354

.preheader354:                                    ; preds = %216
  br label %221

; <label>:221:                                    ; preds = %.preheader354, %221
  %222 = phi i64* [ %223, %221 ], [ %1, %.preheader354 ]
  %223 = getelementptr inbounds i64, i64* %222, i64 -1
  %224 = load i64, i64* %223, align 8, !tbaa !2
  %225 = icmp ult i64 %219, %224
  br i1 %225, label %221, label %226

; <label>:226:                                    ; preds = %221
  %227 = icmp eq i64* %222, %1
  br i1 %227, label %228, label %.preheader352

.preheader352:                                    ; preds = %226
  br label %237

; <label>:228:                                    ; preds = %226
  %229 = icmp ugt i64* %223, %122
  br i1 %229, label %.preheader351, label %.loopexit7

.preheader351:                                    ; preds = %228
  br label %230

; <label>:230:                                    ; preds = %.preheader351, %230
  %231 = phi i64* [ %232, %230 ], [ %122, %.preheader351 ]
  %232 = getelementptr inbounds i64, i64* %231, i64 1
  %233 = load i64, i64* %232, align 8, !tbaa !2
  %234 = icmp uge i64 %219, %233
  %235 = icmp ugt i64* %223, %232
  %236 = and i1 %234, %235
  br i1 %236, label %230, label %.loopexit7

; <label>:237:                                    ; preds = %.preheader352, %237
  %238 = phi i64* [ %239, %237 ], [ %122, %.preheader352 ]
  %239 = getelementptr inbounds i64, i64* %238, i64 1
  %240 = load i64, i64* %239, align 8, !tbaa !2
  %241 = icmp ult i64 %219, %240
  br i1 %241, label %.loopexit7, label %237

.loopexit7:                                       ; preds = %237, %230, %228
  %242 = phi i64 [ %219, %228 ], [ %233, %230 ], [ %240, %237 ]
  %243 = phi i64* [ %122, %228 ], [ %232, %230 ], [ %239, %237 ]
  %244 = icmp ugt i64* %223, %243
  br i1 %244, label %.preheader350, label %.loopexit6

.preheader350:                                    ; preds = %.loopexit7
  br label %245

; <label>:245:                                    ; preds = %.preheader350, %260
  %246 = phi i64 [ %253, %260 ], [ %224, %.preheader350 ]
  %247 = phi i64 [ %258, %260 ], [ %242, %.preheader350 ]
  %248 = phi i64* [ %257, %260 ], [ %243, %.preheader350 ]
  %249 = phi i64* [ %252, %260 ], [ %223, %.preheader350 ]
  store i64 %246, i64* %248, align 8, !tbaa !2
  store i64 %247, i64* %249, align 8, !tbaa !2
  br label %250

; <label>:250:                                    ; preds = %250, %245
  %251 = phi i64* [ %249, %245 ], [ %252, %250 ]
  %252 = getelementptr inbounds i64, i64* %251, i64 -1
  %253 = load i64, i64* %252, align 8, !tbaa !2
  %254 = icmp ult i64 %219, %253
  br i1 %254, label %250, label %.preheader347

.preheader347:                                    ; preds = %250
  br label %255

; <label>:255:                                    ; preds = %.preheader347, %255
  %256 = phi i64* [ %257, %255 ], [ %248, %.preheader347 ]
  %257 = getelementptr inbounds i64, i64* %256, i64 1
  %258 = load i64, i64* %257, align 8, !tbaa !2
  %259 = icmp ult i64 %219, %258
  br i1 %259, label %260, label %255

; <label>:260:                                    ; preds = %255
  %261 = icmp ugt i64* %252, %257
  br i1 %261, label %245, label %.loopexit6

.loopexit16.loopexit:                             ; preds = %216
  %262 = inttoptr i64 %119 to i64*
  br label %.loopexit16

.loopexit16:                                      ; preds = %.loopexit16.loopexit, %213
  %263 = phi i64* [ %214, %213 ], [ %262, %.loopexit16.loopexit ]
  %264 = phi i64 [ %215, %213 ], [ %219, %.loopexit16.loopexit ]
  br label %265

; <label>:265:                                    ; preds = %265, %.loopexit16
  %266 = phi i64 [ 0, %.loopexit16 ], [ %267, %265 ]
  %267 = add nuw nsw i64 %266, 1
  %268 = getelementptr inbounds i64, i64* %263, i64 %267
  %269 = load i64, i64* %268, align 8, !tbaa !2
  %270 = icmp ult i64 %269, %264
  br i1 %270, label %265, label %271

; <label>:271:                                    ; preds = %265
  %272 = getelementptr inbounds i64, i64* %263, i64 %267
  %273 = icmp eq i64 %266, 0
  br i1 %273, label %274, label %.preheader359

.preheader359:                                    ; preds = %271
  br label %283

; <label>:274:                                    ; preds = %271
  %275 = icmp ult i64* %272, %1
  br i1 %275, label %.preheader358, label %.loopexit14

.preheader358:                                    ; preds = %274
  br label %276

; <label>:276:                                    ; preds = %.preheader358, %276
  %277 = phi i64* [ %278, %276 ], [ %1, %.preheader358 ]
  %278 = getelementptr inbounds i64, i64* %277, i64 -1
  %279 = load i64, i64* %278, align 8, !tbaa !2
  %280 = icmp uge i64 %279, %264
  %281 = icmp ult i64* %272, %278
  %282 = and i1 %280, %281
  br i1 %282, label %276, label %.loopexit14

; <label>:283:                                    ; preds = %.preheader359, %283
  %284 = phi i64* [ %285, %283 ], [ %1, %.preheader359 ]
  %285 = getelementptr inbounds i64, i64* %284, i64 -1
  %286 = load i64, i64* %285, align 8, !tbaa !2
  %287 = icmp ult i64 %286, %264
  br i1 %287, label %.loopexit14, label %283

.loopexit14:                                      ; preds = %283, %276, %274
  %288 = phi i64* [ %1, %274 ], [ %278, %276 ], [ %285, %283 ]
  %289 = icmp ult i64* %272, %288
  br i1 %289, label %290, label %.loopexit13

; <label>:290:                                    ; preds = %.loopexit14
  %291 = load i64, i64* %288, align 8, !tbaa !2
  br label %292

; <label>:292:                                    ; preds = %311, %290
  %293 = phi i64 [ %291, %290 ], [ %309, %311 ]
  %294 = phi i64 [ %269, %290 ], [ %302, %311 ]
  %295 = phi i64 [ %267, %290 ], [ %300, %311 ]
  %296 = phi i64* [ %288, %290 ], [ %308, %311 ]
  %297 = getelementptr inbounds i64, i64* %263, i64 %295
  store i64 %293, i64* %297, align 8, !tbaa !2
  store i64 %294, i64* %296, align 8, !tbaa !2
  br label %298

; <label>:298:                                    ; preds = %298, %292
  %299 = phi i64 [ %295, %292 ], [ %300, %298 ]
  %300 = add nsw i64 %299, 1
  %301 = getelementptr inbounds i64, i64* %263, i64 %300
  %302 = load i64, i64* %301, align 8, !tbaa !2
  %303 = icmp ult i64 %302, %264
  br i1 %303, label %298, label %304

; <label>:304:                                    ; preds = %298
  %305 = getelementptr inbounds i64, i64* %263, i64 %300
  br label %306

; <label>:306:                                    ; preds = %306, %304
  %307 = phi i64* [ %296, %304 ], [ %308, %306 ]
  %308 = getelementptr inbounds i64, i64* %307, i64 -1
  %309 = load i64, i64* %308, align 8, !tbaa !2
  %310 = icmp ult i64 %309, %264
  br i1 %310, label %311, label %306

; <label>:311:                                    ; preds = %306
  %312 = icmp ugt i64* %308, %305
  br i1 %312, label %292, label %.loopexit13

.loopexit13:                                      ; preds = %311, %.loopexit14
  %313 = phi i64 [ %266, %.loopexit14 ], [ %299, %311 ]
  %314 = getelementptr inbounds i64, i64* %263, i64 %313
  %315 = load i64, i64* %314, align 8, !tbaa !2
  store i64 %315, i64* %263, align 8, !tbaa !2
  store i64 %264, i64* %314, align 8, !tbaa !2
  %316 = ptrtoint i64* %314 to i64
  %317 = sub i64 %316, %119
  %318 = ashr exact i64 %317, 3
  %319 = getelementptr inbounds i64, i64* %314, i64 1
  %320 = ptrtoint i64* %319 to i64
  %321 = sub i64 %7, %320
  %322 = ashr exact i64 %321, 3
  %323 = lshr i64 %118, 6
  %324 = icmp slt i64 %318, %323
  %325 = icmp slt i64 %322, %323
  %326 = or i1 %324, %325
  br i1 %326, label %327, label %455

; <label>:327:                                    ; preds = %.loopexit13
  %328 = add nsw i32 %16, -1
  %329 = icmp eq i32 %328, 0
  br i1 %329, label %330, label %388

; <label>:330:                                    ; preds = %327
  %331 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_comp_iter", %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* %6, i64 0, i32 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %331) #2
  call void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_comp_iterISt4lessImEEEEvT_SC_RT0_(i64* nonnull %263, i64* %1, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* nonnull dereferenceable(1) %6)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %331) #2
  %332 = icmp sgt i64 %118, 8
  br i1 %332, label %.preheader345, label %.loopexit

.preheader345:                                    ; preds = %330
  br label %333

; <label>:333:                                    ; preds = %.preheader345, %.loopexit2
  %334 = phi i64* [ %335, %.loopexit2 ], [ %1, %.preheader345 ]
  %335 = getelementptr inbounds i64, i64* %334, i64 -1
  %336 = ptrtoint i64* %335 to i64
  %337 = load i64, i64* %335, align 8, !tbaa !2
  %338 = load i64, i64* %263, align 8, !tbaa !2
  store i64 %338, i64* %335, align 8, !tbaa !2
  %339 = sub i64 %336, %119
  %340 = ashr exact i64 %339, 3
  %341 = add nsw i64 %340, -1
  %342 = sdiv i64 %341, 2
  %343 = icmp sgt i64 %339, 16
  br i1 %343, label %.preheader344, label %.loopexit3

.preheader344:                                    ; preds = %333
  br label %344

; <label>:344:                                    ; preds = %.preheader344, %344
  %345 = phi i64 [ %354, %344 ], [ 0, %.preheader344 ]
  %346 = shl i64 %345, 1
  %347 = add i64 %346, 2
  %348 = getelementptr inbounds i64, i64* %263, i64 %347
  %349 = or i64 %346, 1
  %350 = getelementptr inbounds i64, i64* %263, i64 %349
  %351 = load i64, i64* %348, align 8, !tbaa !2
  %352 = load i64, i64* %350, align 8, !tbaa !2
  %353 = icmp ult i64 %351, %352
  %354 = select i1 %353, i64 %349, i64 %347
  %355 = getelementptr inbounds i64, i64* %263, i64 %354
  %356 = load i64, i64* %355, align 8, !tbaa !2
  %357 = getelementptr inbounds i64, i64* %263, i64 %345
  store i64 %356, i64* %357, align 8, !tbaa !2
  %358 = icmp slt i64 %354, %342
  br i1 %358, label %344, label %.loopexit3

.loopexit3:                                       ; preds = %344, %333
  %359 = phi i64 [ 0, %333 ], [ %354, %344 ]
  %360 = and i64 %339, 8
  %361 = icmp eq i64 %360, 0
  br i1 %361, label %362, label %372

; <label>:362:                                    ; preds = %.loopexit3
  %363 = add nsw i64 %340, -2
  %364 = sdiv i64 %363, 2
  %365 = icmp eq i64 %359, %364
  br i1 %365, label %366, label %372

; <label>:366:                                    ; preds = %362
  %367 = shl i64 %359, 1
  %368 = or i64 %367, 1
  %369 = getelementptr inbounds i64, i64* %263, i64 %368
  %370 = load i64, i64* %369, align 8, !tbaa !2
  %371 = getelementptr inbounds i64, i64* %263, i64 %359
  store i64 %370, i64* %371, align 8, !tbaa !2
  br label %372

; <label>:372:                                    ; preds = %366, %362, %.loopexit3
  %373 = phi i64 [ %368, %366 ], [ %359, %362 ], [ %359, %.loopexit3 ]
  %374 = icmp sgt i64 %373, 0
  br i1 %374, label %.preheader343, label %.loopexit2

.preheader343:                                    ; preds = %372
  br label %375

; <label>:375:                                    ; preds = %.preheader343, %382
  %376 = phi i64 [ %378, %382 ], [ %373, %.preheader343 ]
  %377 = add nsw i64 %376, -1
  %378 = sdiv i64 %377, 2
  %379 = getelementptr inbounds i64, i64* %263, i64 %378
  %380 = load i64, i64* %379, align 8, !tbaa !2
  %381 = icmp ult i64 %380, %337
  br i1 %381, label %382, label %.loopexit2

; <label>:382:                                    ; preds = %375
  %383 = getelementptr inbounds i64, i64* %263, i64 %376
  store i64 %380, i64* %383, align 8, !tbaa !2
  %384 = icmp sgt i64 %376, 2
  br i1 %384, label %375, label %.loopexit2

.loopexit2:                                       ; preds = %382, %375, %372
  %385 = phi i64 [ %373, %372 ], [ %378, %382 ], [ %376, %375 ]
  %386 = getelementptr inbounds i64, i64* %263, i64 %385
  store i64 %337, i64* %386, align 8, !tbaa !2
  %387 = icmp sgt i64 %339, 8
  br i1 %387, label %333, label %.loopexit

; <label>:388:                                    ; preds = %327
  %389 = icmp sgt i64 %317, 184
  br i1 %389, label %390, label %422

; <label>:390:                                    ; preds = %388
  %391 = lshr i64 %318, 2
  %392 = getelementptr inbounds i64, i64* %263, i64 %391
  %393 = load i64, i64* %263, align 8, !tbaa !2
  %394 = load i64, i64* %392, align 8, !tbaa !2
  store i64 %394, i64* %263, align 8, !tbaa !2
  store i64 %393, i64* %392, align 8, !tbaa !2
  %395 = getelementptr inbounds i64, i64* %314, i64 -1
  %396 = sub nsw i64 0, %391
  %397 = getelementptr inbounds i64, i64* %314, i64 %396
  %398 = load i64, i64* %395, align 8, !tbaa !2
  %399 = load i64, i64* %397, align 8, !tbaa !2
  store i64 %399, i64* %395, align 8, !tbaa !2
  store i64 %398, i64* %397, align 8, !tbaa !2
  %400 = icmp sgt i64 %317, 1024
  br i1 %400, label %401, label %422

; <label>:401:                                    ; preds = %390
  %402 = getelementptr inbounds i64, i64* %263, i64 1
  %403 = add nuw nsw i64 %391, 1
  %404 = getelementptr inbounds i64, i64* %263, i64 %403
  %405 = load i64, i64* %402, align 8, !tbaa !2
  %406 = load i64, i64* %404, align 8, !tbaa !2
  store i64 %406, i64* %402, align 8, !tbaa !2
  store i64 %405, i64* %404, align 8, !tbaa !2
  %407 = getelementptr inbounds i64, i64* %263, i64 2
  %408 = add nuw nsw i64 %391, 2
  %409 = getelementptr inbounds i64, i64* %263, i64 %408
  %410 = load i64, i64* %407, align 8, !tbaa !2
  %411 = load i64, i64* %409, align 8, !tbaa !2
  store i64 %411, i64* %407, align 8, !tbaa !2
  store i64 %410, i64* %409, align 8, !tbaa !2
  %412 = getelementptr inbounds i64, i64* %314, i64 -2
  %413 = xor i64 %391, -1
  %414 = getelementptr inbounds i64, i64* %314, i64 %413
  %415 = load i64, i64* %412, align 8, !tbaa !2
  %416 = load i64, i64* %414, align 8, !tbaa !2
  store i64 %416, i64* %412, align 8, !tbaa !2
  store i64 %415, i64* %414, align 8, !tbaa !2
  %417 = getelementptr inbounds i64, i64* %314, i64 -3
  %418 = sub nuw nsw i64 -2, %391
  %419 = getelementptr inbounds i64, i64* %314, i64 %418
  %420 = load i64, i64* %417, align 8, !tbaa !2
  %421 = load i64, i64* %419, align 8, !tbaa !2
  store i64 %421, i64* %417, align 8, !tbaa !2
  store i64 %420, i64* %419, align 8, !tbaa !2
  br label %422

; <label>:422:                                    ; preds = %401, %390, %388
  %423 = icmp sgt i64 %321, 184
  br i1 %423, label %425, label %424

; <label>:424:                                    ; preds = %422
  tail call void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* nonnull %263, i64* %314, i32 %328, i1 zeroext %17)
  br label %.loopexit17

; <label>:425:                                    ; preds = %422
  %426 = lshr i64 %322, 2
  %427 = add nuw nsw i64 %426, 1
  %428 = getelementptr inbounds i64, i64* %314, i64 %427
  %429 = load i64, i64* %319, align 8, !tbaa !2
  %430 = load i64, i64* %428, align 8, !tbaa !2
  store i64 %430, i64* %319, align 8, !tbaa !2
  store i64 %429, i64* %428, align 8, !tbaa !2
  %431 = sub nsw i64 0, %426
  %432 = getelementptr inbounds i64, i64* %1, i64 %431
  %433 = load i64, i64* %11, align 8, !tbaa !2
  %434 = load i64, i64* %432, align 8, !tbaa !2
  store i64 %434, i64* %11, align 8, !tbaa !2
  store i64 %433, i64* %432, align 8, !tbaa !2
  %435 = icmp sgt i64 %321, 1024
  br i1 %435, label %436, label %.loopexit9

; <label>:436:                                    ; preds = %425
  %437 = getelementptr inbounds i64, i64* %314, i64 2
  %438 = add nuw nsw i64 %426, 2
  %439 = getelementptr inbounds i64, i64* %314, i64 %438
  %440 = load i64, i64* %437, align 8, !tbaa !2
  %441 = load i64, i64* %439, align 8, !tbaa !2
  store i64 %441, i64* %437, align 8, !tbaa !2
  store i64 %440, i64* %439, align 8, !tbaa !2
  %442 = getelementptr inbounds i64, i64* %314, i64 3
  %443 = add nuw nsw i64 %426, 3
  %444 = getelementptr inbounds i64, i64* %314, i64 %443
  %445 = load i64, i64* %442, align 8, !tbaa !2
  %446 = load i64, i64* %444, align 8, !tbaa !2
  store i64 %446, i64* %442, align 8, !tbaa !2
  store i64 %445, i64* %444, align 8, !tbaa !2
  %447 = xor i64 %426, -1
  %448 = getelementptr inbounds i64, i64* %1, i64 %447
  %449 = load i64, i64* %12, align 8, !tbaa !2
  %450 = load i64, i64* %448, align 8, !tbaa !2
  store i64 %450, i64* %12, align 8, !tbaa !2
  store i64 %449, i64* %448, align 8, !tbaa !2
  %451 = sub nuw nsw i64 -2, %426
  %452 = getelementptr inbounds i64, i64* %1, i64 %451
  %453 = load i64, i64* %13, align 8, !tbaa !2
  %454 = load i64, i64* %452, align 8, !tbaa !2
  store i64 %454, i64* %13, align 8, !tbaa !2
  store i64 %453, i64* %452, align 8, !tbaa !2
  br label %.loopexit9

; <label>:455:                                    ; preds = %.loopexit13
  br i1 %289, label %.loopexit9, label %456

; <label>:456:                                    ; preds = %455
  %457 = icmp ult i64 %313, 2
  br i1 %457, label %.loopexit12, label %458

; <label>:458:                                    ; preds = %456
  %459 = getelementptr inbounds i64, i64* %263, i64 1
  br label %460

; <label>:460:                                    ; preds = %487, %458
  %461 = phi i64* [ %459, %458 ], [ %489, %487 ]
  %462 = phi i32 [ 0, %458 ], [ %488, %487 ]
  %463 = phi i64* [ %263, %458 ], [ %461, %487 ]
  %464 = ptrtoint i64* %461 to i64
  %465 = icmp sgt i32 %462, 8
  br i1 %465, label %.loopexit9, label %466

; <label>:466:                                    ; preds = %460
  %467 = load i64, i64* %461, align 8, !tbaa !2
  %468 = load i64, i64* %463, align 8, !tbaa !2
  %469 = icmp ult i64 %467, %468
  br i1 %469, label %.preheader349, label %487

.preheader349:                                    ; preds = %466
  br label %470

; <label>:470:                                    ; preds = %.preheader349, %476
  %471 = phi i64 [ %478, %476 ], [ %468, %.preheader349 ]
  %472 = phi i64* [ %477, %476 ], [ %463, %.preheader349 ]
  %473 = phi i64* [ %474, %476 ], [ %461, %.preheader349 ]
  %474 = getelementptr inbounds i64, i64* %473, i64 -1
  store i64 %471, i64* %473, align 8, !tbaa !2
  %475 = icmp eq i64* %474, %263
  br i1 %475, label %480, label %476

; <label>:476:                                    ; preds = %470
  %477 = getelementptr inbounds i64, i64* %472, i64 -1
  %478 = load i64, i64* %477, align 8, !tbaa !2
  %479 = icmp ult i64 %467, %478
  br i1 %479, label %470, label %480

; <label>:480:                                    ; preds = %476, %470
  %481 = phi i64* [ %263, %470 ], [ %474, %476 ]
  %482 = ptrtoint i64* %481 to i64
  store i64 %467, i64* %481, align 8, !tbaa !2
  %483 = sub i64 %464, %482
  %484 = lshr exact i64 %483, 3
  %485 = trunc i64 %484 to i32
  %486 = add i32 %462, %485
  br label %487

; <label>:487:                                    ; preds = %480, %466
  %488 = phi i32 [ %486, %480 ], [ %462, %466 ]
  %489 = getelementptr inbounds i64, i64* %461, i64 1
  %490 = icmp eq i64* %489, %314
  br i1 %490, label %.loopexit12, label %460

.loopexit12:                                      ; preds = %487, %456
  %491 = icmp eq i64* %319, %1
  %492 = getelementptr inbounds i64, i64* %314, i64 2
  %493 = icmp eq i64* %492, %1
  %494 = or i1 %491, %493
  br i1 %494, label %.loopexit, label %.preheader355

.preheader355:                                    ; preds = %.loopexit12
  br label %495

; <label>:495:                                    ; preds = %.preheader355, %526
  %496 = phi i64 [ %528, %526 ], [ 2, %.preheader355 ]
  %497 = phi i32 [ %527, %526 ], [ 0, %.preheader355 ]
  %498 = phi i64* [ %499, %526 ], [ %319, %.preheader355 ]
  %499 = getelementptr inbounds i64, i64* %314, i64 %496
  %500 = ptrtoint i64* %499 to i64
  %501 = icmp sgt i32 %497, 8
  br i1 %501, label %.loopexit9, label %502

; <label>:502:                                    ; preds = %495
  %503 = load i64, i64* %499, align 8, !tbaa !2
  %504 = load i64, i64* %498, align 8, !tbaa !2
  %505 = icmp ult i64 %503, %504
  br i1 %505, label %.preheader348, label %526

.preheader348:                                    ; preds = %502
  br label %506

; <label>:506:                                    ; preds = %.preheader348, %513
  %507 = phi i64 [ %515, %513 ], [ %504, %.preheader348 ]
  %508 = phi i64* [ %514, %513 ], [ %498, %.preheader348 ]
  %509 = phi i64 [ %511, %513 ], [ %496, %.preheader348 ]
  %510 = getelementptr inbounds i64, i64* %314, i64 %509
  %511 = add nsw i64 %509, -1
  store i64 %507, i64* %510, align 8, !tbaa !2
  %512 = icmp eq i64 %511, 1
  br i1 %512, label %.loopexit5, label %513

; <label>:513:                                    ; preds = %506
  %514 = getelementptr inbounds i64, i64* %508, i64 -1
  %515 = load i64, i64* %514, align 8, !tbaa !2
  %516 = icmp ult i64 %503, %515
  br i1 %516, label %506, label %517

; <label>:517:                                    ; preds = %513
  %518 = getelementptr inbounds i64, i64* %314, i64 %511
  %519 = ptrtoint i64* %518 to i64
  br label %.loopexit5

.loopexit5:                                       ; preds = %506, %517
  %520 = phi i64 [ %519, %517 ], [ %320, %506 ]
  %521 = phi i64* [ %518, %517 ], [ %319, %506 ]
  store i64 %503, i64* %521, align 8, !tbaa !2
  %522 = sub i64 %500, %520
  %523 = lshr exact i64 %522, 3
  %524 = trunc i64 %523 to i32
  %525 = add i32 %497, %524
  br label %526

; <label>:526:                                    ; preds = %.loopexit5, %502
  %527 = phi i32 [ %525, %.loopexit5 ], [ %497, %502 ]
  %528 = add nuw nsw i64 %496, 1
  %529 = getelementptr inbounds i64, i64* %314, i64 %528
  %530 = icmp eq i64* %529, %1
  br i1 %530, label %.loopexit, label %495

.loopexit6:                                       ; preds = %260, %.loopexit7
  %531 = phi i64 [ %224, %.loopexit7 ], [ %253, %260 ]
  %532 = phi i64* [ %223, %.loopexit7 ], [ %252, %260 ]
  store i64 %531, i64* %122, align 8, !tbaa !2
  store i64 %219, i64* %532, align 8, !tbaa !2
  %533 = getelementptr inbounds i64, i64* %532, i64 1
  %534 = ptrtoint i64* %533 to i64
  %535 = sub i64 %7, %534
  %536 = icmp slt i64 %535, 192
  br i1 %536, label %.loopexit17, label %117

.loopexit9:                                       ; preds = %460, %495, %455, %436, %425
  %537 = phi i32 [ %328, %436 ], [ %328, %425 ], [ %16, %455 ], [ %16, %495 ], [ %16, %460 ]
  tail call void @_ZN5boost4sort14pdqsort_detail12pdqsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEESt4lessImELb0EEEvT_SC_T0_ib(i64* %263, i64* %314, i32 %537, i1 zeroext %17)
  %538 = icmp slt i64 %321, 192
  br i1 %538, label %.loopexit17, label %14

.loopexit:                                        ; preds = %.loopexit12, %526, %.loopexit2, %563, %551, %330, %93, %67, %66, %39, %24, %23, %.loopexit17
  ret void

; <label>:539:                                    ; preds = %.preheader, %545
  %540 = phi i64 [ %547, %545 ], [ %62, %.preheader ]
  %541 = phi i64* [ %546, %545 ], [ %44, %.preheader ]
  %542 = phi i64* [ %543, %545 ], [ %63, %.preheader ]
  %543 = getelementptr inbounds i64, i64* %542, i64 -1
  store i64 %540, i64* %542, align 8, !tbaa !2
  %544 = icmp eq i64* %543, %0
  br i1 %544, label %549, label %545

; <label>:545:                                    ; preds = %539
  %546 = getelementptr inbounds i64, i64* %541, i64 -1
  %547 = load i64, i64* %546, align 8, !tbaa !2
  %548 = icmp ult i64 %64, %547
  br i1 %548, label %539, label %549

; <label>:549:                                    ; preds = %545, %539
  %550 = phi i64* [ %0, %539 ], [ %543, %545 ]
  store i64 %64, i64* %550, align 8, !tbaa !2
  br label %551

; <label>:551:                                    ; preds = %549, %61
  %552 = getelementptr inbounds i64, i64* %44, i64 2
  %553 = icmp eq i64* %552, %1
  br i1 %553, label %.loopexit, label %43

; <label>:554:                                    ; preds = %.preheader338, %554
  %555 = phi i64 [ %560, %554 ], [ %113, %.preheader338 ]
  %556 = phi i64* [ %559, %554 ], [ %98, %.preheader338 ]
  %557 = phi i64* [ %558, %554 ], [ %114, %.preheader338 ]
  %558 = getelementptr inbounds i64, i64* %557, i64 -1
  store i64 %555, i64* %557, align 8, !tbaa !2
  %559 = getelementptr inbounds i64, i64* %556, i64 -1
  %560 = load i64, i64* %559, align 8, !tbaa !2
  %561 = icmp ult i64 %115, %560
  br i1 %561, label %554, label %562

; <label>:562:                                    ; preds = %554
  store i64 %115, i64* %558, align 8, !tbaa !2
  br label %563

; <label>:563:                                    ; preds = %562, %112
  %564 = getelementptr inbounds i64, i64* %98, i64 2
  %565 = icmp eq i64* %564, %1
  br i1 %565, label %.loopexit, label %97
}

; Function Attrs: norecurse uwtable
define linkonce_odr void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_comp_iterISt4lessImEEEEvT_SC_RT0_(i64*, i64*, %"struct.__gnu_cxx::__ops::_Iter_comp_iter"* dereferenceable(1)) local_unnamed_addr #10 comdat {
  %4 = ptrtoint i64* %0 to i64
  %5 = ptrtoint i64* %1 to i64
  %6 = sub i64 %5, %4
  %7 = ashr exact i64 %6, 3
  %8 = icmp slt i64 %6, 16
  br i1 %8, label %.loopexit2, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 8
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %16, label %.preheader30

.preheader30:                                     ; preds = %9
  br label %62

; <label>:16:                                     ; preds = %9
  %17 = shl nsw i64 %11, 1
  %18 = or i64 %17, 1
  %19 = getelementptr inbounds i64, i64* %0, i64 %18
  %20 = getelementptr inbounds i64, i64* %0, i64 %11
  br label %21

; <label>:21:                                     ; preds = %.loopexit, %16
  %22 = phi i64 [ %11, %16 ], [ %61, %.loopexit ]
  %23 = getelementptr inbounds i64, i64* %0, i64 %22
  %24 = load i64, i64* %23, align 8, !tbaa !2
  %25 = icmp sgt i64 %13, %22
  br i1 %25, label %.preheader26, label %.loopexit1

.preheader26:                                     ; preds = %21
  br label %26

; <label>:26:                                     ; preds = %.preheader26, %26
  %27 = phi i64 [ %36, %26 ], [ %22, %.preheader26 ]
  %28 = shl i64 %27, 1
  %29 = add i64 %28, 2
  %30 = getelementptr inbounds i64, i64* %0, i64 %29
  %31 = or i64 %28, 1
  %32 = getelementptr inbounds i64, i64* %0, i64 %31
  %33 = load i64, i64* %30, align 8, !tbaa !2
  %34 = load i64, i64* %32, align 8, !tbaa !2
  %35 = icmp ult i64 %33, %34
  %36 = select i1 %35, i64 %31, i64 %29
  %37 = getelementptr inbounds i64, i64* %0, i64 %36
  %38 = load i64, i64* %37, align 8, !tbaa !2
  %39 = getelementptr inbounds i64, i64* %0, i64 %27
  store i64 %38, i64* %39, align 8, !tbaa !2
  %40 = icmp slt i64 %36, %13
  br i1 %40, label %26, label %.loopexit1

.loopexit1:                                       ; preds = %26, %21
  %41 = phi i64 [ %22, %21 ], [ %36, %26 ]
  %42 = icmp eq i64 %41, %11
  br i1 %42, label %43, label %45

; <label>:43:                                     ; preds = %.loopexit1
  %44 = load i64, i64* %19, align 8, !tbaa !2
  store i64 %44, i64* %20, align 8, !tbaa !2
  br label %45

; <label>:45:                                     ; preds = %43, %.loopexit1
  %46 = phi i64 [ %18, %43 ], [ %41, %.loopexit1 ]
  %47 = icmp sgt i64 %46, %22
  br i1 %47, label %.preheader, label %.loopexit

.preheader:                                       ; preds = %45
  br label %48

; <label>:48:                                     ; preds = %.preheader, %55
  %49 = phi i64 [ %51, %55 ], [ %46, %.preheader ]
  %50 = add nsw i64 %49, -1
  %51 = sdiv i64 %50, 2
  %52 = getelementptr inbounds i64, i64* %0, i64 %51
  %53 = load i64, i64* %52, align 8, !tbaa !2
  %54 = icmp ult i64 %53, %24
  br i1 %54, label %55, label %.loopexit

; <label>:55:                                     ; preds = %48
  %56 = getelementptr inbounds i64, i64* %0, i64 %49
  store i64 %53, i64* %56, align 8, !tbaa !2
  %57 = icmp sgt i64 %51, %22
  br i1 %57, label %48, label %.loopexit

.loopexit:                                        ; preds = %55, %48, %45
  %58 = phi i64 [ %46, %45 ], [ %49, %48 ], [ %51, %55 ]
  %59 = getelementptr inbounds i64, i64* %0, i64 %58
  store i64 %24, i64* %59, align 8, !tbaa !2
  %60 = icmp eq i64 %22, 0
  %61 = add nsw i64 %22, -1
  br i1 %60, label %.loopexit2, label %21

; <label>:62:                                     ; preds = %.preheader30, %.loopexit3
  %63 = phi i64 [ %97, %.loopexit3 ], [ %11, %.preheader30 ]
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  %65 = load i64, i64* %64, align 8, !tbaa !2
  %66 = icmp sgt i64 %13, %63
  br i1 %66, label %.preheader29, label %.loopexit3

.preheader29:                                     ; preds = %62
  br label %67

; <label>:67:                                     ; preds = %.preheader29, %67
  %68 = phi i64 [ %77, %67 ], [ %63, %.preheader29 ]
  %69 = shl i64 %68, 1
  %70 = add i64 %69, 2
  %71 = getelementptr inbounds i64, i64* %0, i64 %70
  %72 = or i64 %69, 1
  %73 = getelementptr inbounds i64, i64* %0, i64 %72
  %74 = load i64, i64* %71, align 8, !tbaa !2
  %75 = load i64, i64* %73, align 8, !tbaa !2
  %76 = icmp ult i64 %74, %75
  %77 = select i1 %76, i64 %72, i64 %70
  %78 = getelementptr inbounds i64, i64* %0, i64 %77
  %79 = load i64, i64* %78, align 8, !tbaa !2
  %80 = getelementptr inbounds i64, i64* %0, i64 %68
  store i64 %79, i64* %80, align 8, !tbaa !2
  %81 = icmp slt i64 %77, %13
  br i1 %81, label %67, label %82

; <label>:82:                                     ; preds = %67
  %83 = getelementptr inbounds i64, i64* %0, i64 %77
  %84 = icmp sgt i64 %77, %63
  br i1 %84, label %.preheader27, label %.loopexit3

.preheader27:                                     ; preds = %82
  br label %85

; <label>:85:                                     ; preds = %.preheader27, %93
  %86 = phi i64 [ %88, %93 ], [ %77, %.preheader27 ]
  %87 = add nsw i64 %86, -1
  %88 = sdiv i64 %87, 2
  %89 = getelementptr inbounds i64, i64* %0, i64 %88
  %90 = load i64, i64* %89, align 8, !tbaa !2
  %91 = icmp ult i64 %90, %65
  %92 = getelementptr inbounds i64, i64* %0, i64 %86
  br i1 %91, label %93, label %.loopexit3

; <label>:93:                                     ; preds = %85
  store i64 %90, i64* %92, align 8, !tbaa !2
  %94 = icmp sgt i64 %88, %63
  br i1 %94, label %85, label %.loopexit3.loopexit

.loopexit3.loopexit:                              ; preds = %93
  %95 = getelementptr inbounds i64, i64* %0, i64 %88
  br label %.loopexit3

.loopexit3:                                       ; preds = %85, %.loopexit3.loopexit, %82, %62
  %.pre-phi = phi i64* [ %83, %82 ], [ %64, %62 ], [ %95, %.loopexit3.loopexit ], [ %92, %85 ]
  store i64 %65, i64* %.pre-phi, align 8, !tbaa !2
  %96 = icmp eq i64 %63, 0
  %97 = add nsw i64 %63, -1
  br i1 %96, label %.loopexit2, label %62

.loopexit2:                                       ; preds = %.loopexit3, %.loopexit, %3
  ret void
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64*, i64*, i64) local_unnamed_addr #7 comdat {
  %4 = alloca %"struct.__gnu_cxx::__ops::_Iter_less_iter", align 1
  %5 = ptrtoint i64* %0 to i64
  %6 = ptrtoint i64* %1 to i64
  %7 = sub i64 %6, %5
  %8 = icmp sgt i64 %7, 128
  br i1 %8, label %9, label %.loopexit2

; <label>:9:                                      ; preds = %3
  %10 = getelementptr inbounds i64, i64* %0, i64 1
  br label %11

; <label>:11:                                     ; preds = %117, %9
  %12 = phi i64 [ %7, %9 ], [ %119, %117 ]
  %13 = phi i64 [ %2, %9 ], [ %75, %117 ]
  %14 = phi i64* [ %1, %9 ], [ %105, %117 ]
  %15 = icmp eq i64 %13, 0
  br i1 %15, label %16, label %73

; <label>:16:                                     ; preds = %11
  %17 = getelementptr inbounds %"struct.__gnu_cxx::__ops::_Iter_less_iter", %"struct.__gnu_cxx::__ops::_Iter_less_iter"* %4, i64 0, i32 0
  call void @llvm.lifetime.start.p0i8(i64 1, i8* nonnull %17)
  call void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_RT0_(i64* %0, i64* %14, %"struct.__gnu_cxx::__ops::_Iter_less_iter"* nonnull dereferenceable(1) %4)
  call void @llvm.lifetime.end.p0i8(i64 1, i8* nonnull %17)
  br label %18

; <label>:18:                                     ; preds = %.loopexit, %16
  %19 = phi i64* [ %14, %16 ], [ %20, %.loopexit ]
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
  br i1 %28, label %.preheader35, label %.loopexit1

.preheader35:                                     ; preds = %18
  br label %29

; <label>:29:                                     ; preds = %.preheader35, %29
  %30 = phi i64 [ %39, %29 ], [ 0, %.preheader35 ]
  %31 = shl i64 %30, 1
  %32 = add i64 %31, 2
  %33 = getelementptr inbounds i64, i64* %0, i64 %32
  %34 = or i64 %31, 1
  %35 = getelementptr inbounds i64, i64* %0, i64 %34
  %36 = load i64, i64* %33, align 8, !tbaa !2
  %37 = load i64, i64* %35, align 8, !tbaa !2
  %38 = icmp ult i64 %36, %37
  %39 = select i1 %38, i64 %34, i64 %32
  %40 = getelementptr inbounds i64, i64* %0, i64 %39
  %41 = load i64, i64* %40, align 8, !tbaa !2
  %42 = getelementptr inbounds i64, i64* %0, i64 %30
  store i64 %41, i64* %42, align 8, !tbaa !2
  %43 = icmp slt i64 %39, %27
  br i1 %43, label %29, label %.loopexit1

.loopexit1:                                       ; preds = %29, %18
  %44 = phi i64 [ 0, %18 ], [ %39, %29 ]
  %45 = and i64 %24, 8
  %46 = icmp eq i64 %45, 0
  br i1 %46, label %47, label %57

; <label>:47:                                     ; preds = %.loopexit1
  %48 = add nsw i64 %25, -2
  %49 = sdiv i64 %48, 2
  %50 = icmp eq i64 %44, %49
  br i1 %50, label %51, label %57

; <label>:51:                                     ; preds = %47
  %52 = shl i64 %44, 1
  %53 = or i64 %52, 1
  %54 = getelementptr inbounds i64, i64* %0, i64 %53
  %55 = load i64, i64* %54, align 8, !tbaa !2
  %56 = getelementptr inbounds i64, i64* %0, i64 %44
  store i64 %55, i64* %56, align 8, !tbaa !2
  br label %57

; <label>:57:                                     ; preds = %51, %47, %.loopexit1
  %58 = phi i64 [ %53, %51 ], [ %44, %47 ], [ %44, %.loopexit1 ]
  %59 = icmp sgt i64 %58, 0
  br i1 %59, label %.preheader, label %.loopexit

.preheader:                                       ; preds = %57
  br label %60

; <label>:60:                                     ; preds = %.preheader, %67
  %61 = phi i64 [ %63, %67 ], [ %58, %.preheader ]
  %62 = add nsw i64 %61, -1
  %63 = sdiv i64 %62, 2
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  %65 = load i64, i64* %64, align 8, !tbaa !2
  %66 = icmp ult i64 %65, %22
  br i1 %66, label %67, label %.loopexit

; <label>:67:                                     ; preds = %60
  %68 = getelementptr inbounds i64, i64* %0, i64 %61
  store i64 %65, i64* %68, align 8, !tbaa !2
  %69 = icmp sgt i64 %61, 2
  br i1 %69, label %60, label %.loopexit

.loopexit:                                        ; preds = %67, %60, %57
  %70 = phi i64 [ %58, %57 ], [ %63, %67 ], [ %61, %60 ]
  %71 = getelementptr inbounds i64, i64* %0, i64 %70
  store i64 %22, i64* %71, align 8, !tbaa !2
  %72 = icmp sgt i64 %24, 8
  br i1 %72, label %18, label %.loopexit2

; <label>:73:                                     ; preds = %11
  %74 = lshr i64 %12, 4
  %75 = add nsw i64 %13, -1
  %76 = getelementptr inbounds i64, i64* %0, i64 %74
  %77 = getelementptr inbounds i64, i64* %14, i64 -1
  %78 = load i64, i64* %10, align 8, !tbaa !2
  %79 = load i64, i64* %76, align 8, !tbaa !2
  %80 = icmp ult i64 %78, %79
  %81 = load i64, i64* %77, align 8, !tbaa !2
  br i1 %80, label %82, label %91

; <label>:82:                                     ; preds = %73
  %83 = icmp ult i64 %79, %81
  br i1 %83, label %84, label %86

; <label>:84:                                     ; preds = %82
  %85 = load i64, i64* %0, align 8, !tbaa !2
  store i64 %79, i64* %0, align 8, !tbaa !2
  store i64 %85, i64* %76, align 8, !tbaa !2
  br label %.preheader37

; <label>:86:                                     ; preds = %82
  %87 = icmp ult i64 %78, %81
  %88 = load i64, i64* %0, align 8, !tbaa !2
  br i1 %87, label %89, label %90

; <label>:89:                                     ; preds = %86
  store i64 %81, i64* %0, align 8, !tbaa !2
  store i64 %88, i64* %77, align 8, !tbaa !2
  br label %.preheader37

; <label>:90:                                     ; preds = %86
  store i64 %78, i64* %0, align 8, !tbaa !2
  store i64 %88, i64* %10, align 8, !tbaa !2
  br label %.preheader37

; <label>:91:                                     ; preds = %73
  %92 = icmp ult i64 %78, %81
  br i1 %92, label %93, label %95

; <label>:93:                                     ; preds = %91
  %94 = load i64, i64* %0, align 8, !tbaa !2
  store i64 %78, i64* %0, align 8, !tbaa !2
  store i64 %94, i64* %10, align 8, !tbaa !2
  br label %.preheader37

; <label>:95:                                     ; preds = %91
  %96 = icmp ult i64 %79, %81
  %97 = load i64, i64* %0, align 8, !tbaa !2
  br i1 %96, label %98, label %99

; <label>:98:                                     ; preds = %95
  store i64 %81, i64* %0, align 8, !tbaa !2
  store i64 %97, i64* %77, align 8, !tbaa !2
  br label %.preheader37

; <label>:99:                                     ; preds = %95
  store i64 %79, i64* %0, align 8, !tbaa !2
  store i64 %97, i64* %76, align 8, !tbaa !2
  br label %.preheader37

.preheader37:                                     ; preds = %99, %98, %93, %90, %89, %84
  br label %100

; <label>:100:                                    ; preds = %.preheader37, %116
  %101 = phi i64* [ %108, %116 ], [ %10, %.preheader37 ]
  %102 = phi i64* [ %111, %116 ], [ %14, %.preheader37 ]
  %103 = load i64, i64* %0, align 8, !tbaa !2
  br label %104

; <label>:104:                                    ; preds = %104, %100
  %105 = phi i64* [ %101, %100 ], [ %108, %104 ]
  %106 = load i64, i64* %105, align 8, !tbaa !2
  %107 = icmp ult i64 %106, %103
  %108 = getelementptr inbounds i64, i64* %105, i64 1
  br i1 %107, label %104, label %.preheader36

.preheader36:                                     ; preds = %104
  br label %109

; <label>:109:                                    ; preds = %.preheader36, %109
  %110 = phi i64* [ %111, %109 ], [ %102, %.preheader36 ]
  %111 = getelementptr inbounds i64, i64* %110, i64 -1
  %112 = load i64, i64* %111, align 8, !tbaa !2
  %113 = icmp ult i64 %103, %112
  br i1 %113, label %109, label %114

; <label>:114:                                    ; preds = %109
  %115 = icmp ult i64* %105, %111
  br i1 %115, label %116, label %117

; <label>:116:                                    ; preds = %114
  store i64 %112, i64* %105, align 8, !tbaa !2
  store i64 %106, i64* %111, align 8, !tbaa !2
  br label %100

; <label>:117:                                    ; preds = %114
  tail call void @_ZSt16__introsort_loopIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEElNS0_5__ops15_Iter_less_iterEEvT_S9_T0_T1_(i64* %105, i64* %14, i64 %75)
  %118 = ptrtoint i64* %105 to i64
  %119 = sub i64 %118, %5
  %120 = icmp sgt i64 %119, 128
  br i1 %120, label %11, label %.loopexit2

.loopexit2:                                       ; preds = %117, %.loopexit, %3
  ret void
}

; Function Attrs: uwtable
define linkonce_odr void @_ZSt22__final_insertion_sortIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_T0_(i64*, i64*) local_unnamed_addr #7 comdat {
  %3 = ptrtoint i64* %0 to i64
  %4 = ptrtoint i64* %1 to i64
  %5 = sub i64 %4, %3
  %6 = icmp sgt i64 %5, 128
  br i1 %6, label %7, label %61

; <label>:7:                                      ; preds = %2
  %8 = bitcast i64* %0 to i8*
  %9 = getelementptr i64, i64* %0, i64 1
  %10 = bitcast i64* %9 to i8*
  %11 = load i64, i64* %9, align 8, !tbaa !2
  %12 = load i64, i64* %0, align 8, !tbaa !2
  %13 = icmp ult i64 %11, %12
  br i1 %13, label %14, label %15

; <label>:14:                                     ; preds = %7
  store i64 %12, i64* %9, align 8
  br label %15

; <label>:15:                                     ; preds = %7, %14
  %16 = phi i64* [ %0, %14 ], [ %9, %7 ]
  store i64 %11, i64* %16, align 8, !tbaa !2
  %17 = getelementptr inbounds i64, i64* %0, i64 2
  %18 = load i64, i64* %17, align 8, !tbaa !2
  %19 = load i64, i64* %0, align 8, !tbaa !2
  %20 = icmp ult i64 %18, %19
  br i1 %20, label %117, label %107

; <label>:21:                                     ; preds = %.loopexit4
  %22 = getelementptr i64, i64* %1, i64 -17
  %23 = ptrtoint i64* %22 to i64
  %24 = sub i64 %23, %3
  %25 = and i64 %24, 8
  %26 = icmp eq i64 %25, 0
  br i1 %26, label %27, label %40

; <label>:27:                                     ; preds = %21
  %28 = load i64, i64* %327, align 8, !tbaa !2
  %29 = load i64, i64* %311, align 8, !tbaa !2
  %30 = icmp ult i64 %28, %29
  br i1 %30, label %.preheader93, label %.loopexit3

.preheader93:                                     ; preds = %27
  br label %31

; <label>:31:                                     ; preds = %.preheader93, %31
  %32 = phi i64 [ %36, %31 ], [ %29, %.preheader93 ]
  %33 = phi i64* [ %35, %31 ], [ %311, %.preheader93 ]
  %34 = phi i64* [ %33, %31 ], [ %327, %.preheader93 ]
  store i64 %32, i64* %34, align 8, !tbaa !2
  %35 = getelementptr inbounds i64, i64* %33, i64 -1
  %36 = load i64, i64* %35, align 8, !tbaa !2
  %37 = icmp ult i64 %28, %36
  br i1 %37, label %31, label %.loopexit3

.loopexit3:                                       ; preds = %31, %27
  %38 = phi i64* [ %327, %27 ], [ %33, %31 ]
  store i64 %28, i64* %38, align 8, !tbaa !2
  %39 = getelementptr inbounds i64, i64* %0, i64 17
  br label %40

; <label>:40:                                     ; preds = %.loopexit3, %21
  %41 = phi i64* [ %327, %21 ], [ %39, %.loopexit3 ]
  %42 = icmp ult i64 %24, 8
  br i1 %42, label %.loopexit2, label %.preheader92

.preheader92:                                     ; preds = %40
  br label %43

; <label>:43:                                     ; preds = %.preheader92, %.loopexit
  %44 = phi i64* [ %105, %.loopexit ], [ %41, %.preheader92 ]
  %45 = load i64, i64* %44, align 8, !tbaa !2
  %46 = getelementptr inbounds i64, i64* %44, i64 -1
  %47 = load i64, i64* %46, align 8, !tbaa !2
  %48 = icmp ult i64 %45, %47
  br i1 %48, label %.preheader91, label %.loopexit1

.preheader91:                                     ; preds = %43
  br label %49

; <label>:49:                                     ; preds = %.preheader91, %49
  %50 = phi i64 [ %54, %49 ], [ %47, %.preheader91 ]
  %51 = phi i64* [ %53, %49 ], [ %46, %.preheader91 ]
  %52 = phi i64* [ %51, %49 ], [ %44, %.preheader91 ]
  store i64 %50, i64* %52, align 8, !tbaa !2
  %53 = getelementptr inbounds i64, i64* %51, i64 -1
  %54 = load i64, i64* %53, align 8, !tbaa !2
  %55 = icmp ult i64 %45, %54
  br i1 %55, label %49, label %.loopexit1

.loopexit1:                                       ; preds = %49, %43
  %56 = phi i64* [ %44, %43 ], [ %51, %49 ]
  store i64 %45, i64* %56, align 8, !tbaa !2
  %57 = getelementptr inbounds i64, i64* %44, i64 1
  %58 = load i64, i64* %57, align 8, !tbaa !2
  %59 = load i64, i64* %44, align 8, !tbaa !2
  %60 = icmp ult i64 %58, %59
  br i1 %60, label %.preheader, label %.loopexit

.preheader:                                       ; preds = %.loopexit1
  br label %97

; <label>:61:                                     ; preds = %2
  %62 = icmp eq i64* %0, %1
  br i1 %62, label %.loopexit2, label %63

; <label>:63:                                     ; preds = %61
  %64 = getelementptr inbounds i64, i64* %0, i64 1
  %65 = icmp eq i64* %64, %1
  br i1 %65, label %.loopexit2, label %66

; <label>:66:                                     ; preds = %63
  %67 = bitcast i64* %0 to i8*
  br label %68

; <label>:68:                                     ; preds = %.loopexit18, %66
  %69 = phi i64* [ %64, %66 ], [ %95, %.loopexit18 ]
  %70 = phi i64* [ %0, %66 ], [ %69, %.loopexit18 ]
  %71 = load i64, i64* %69, align 8, !tbaa !2
  %72 = load i64, i64* %0, align 8, !tbaa !2
  %73 = icmp ult i64 %71, %72
  br i1 %73, label %74, label %84

; <label>:74:                                     ; preds = %68
  %75 = ptrtoint i64* %69 to i64
  %76 = sub i64 %75, %3
  %77 = icmp eq i64 %76, 0
  br i1 %77, label %.loopexit18, label %78

; <label>:78:                                     ; preds = %74
  %79 = getelementptr inbounds i64, i64* %70, i64 2
  %80 = ashr exact i64 %76, 3
  %81 = sub nsw i64 0, %80
  %82 = getelementptr inbounds i64, i64* %79, i64 %81
  %83 = bitcast i64* %82 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %83, i8* nonnull %67, i64 %76, i32 8, i1 false) #2
  br label %.loopexit18

; <label>:84:                                     ; preds = %68
  %85 = load i64, i64* %70, align 8, !tbaa !2
  %86 = icmp ult i64 %71, %85
  br i1 %86, label %.preheader108, label %.loopexit18

.preheader108:                                    ; preds = %84
  br label %87

; <label>:87:                                     ; preds = %.preheader108, %87
  %88 = phi i64 [ %92, %87 ], [ %85, %.preheader108 ]
  %89 = phi i64* [ %91, %87 ], [ %70, %.preheader108 ]
  %90 = phi i64* [ %89, %87 ], [ %69, %.preheader108 ]
  store i64 %88, i64* %90, align 8, !tbaa !2
  %91 = getelementptr inbounds i64, i64* %89, i64 -1
  %92 = load i64, i64* %91, align 8, !tbaa !2
  %93 = icmp ult i64 %71, %92
  br i1 %93, label %87, label %.loopexit18

.loopexit18:                                      ; preds = %87, %84, %78, %74
  %94 = phi i64* [ %0, %78 ], [ %0, %74 ], [ %69, %84 ], [ %89, %87 ]
  store i64 %71, i64* %94, align 8, !tbaa !2
  %95 = getelementptr inbounds i64, i64* %69, i64 1
  %96 = icmp eq i64* %95, %1
  br i1 %96, label %.loopexit2, label %68

.loopexit2:                                       ; preds = %.loopexit18, %.loopexit, %.loopexit4, %63, %61, %40
  ret void

; <label>:97:                                     ; preds = %.preheader, %97
  %98 = phi i64 [ %102, %97 ], [ %59, %.preheader ]
  %99 = phi i64* [ %101, %97 ], [ %44, %.preheader ]
  %100 = phi i64* [ %99, %97 ], [ %57, %.preheader ]
  store i64 %98, i64* %100, align 8, !tbaa !2
  %101 = getelementptr inbounds i64, i64* %99, i64 -1
  %102 = load i64, i64* %101, align 8, !tbaa !2
  %103 = icmp ult i64 %58, %102
  br i1 %103, label %97, label %.loopexit

.loopexit:                                        ; preds = %97, %.loopexit1
  %104 = phi i64* [ %57, %.loopexit1 ], [ %99, %97 ]
  store i64 %58, i64* %104, align 8, !tbaa !2
  %105 = getelementptr inbounds i64, i64* %44, i64 2
  %106 = icmp eq i64* %105, %1
  br i1 %106, label %.loopexit2, label %43

; <label>:107:                                    ; preds = %15
  %108 = load i64, i64* %9, align 8, !tbaa !2
  %109 = icmp ult i64 %18, %108
  br i1 %109, label %.preheader107, label %.loopexit17

.preheader107:                                    ; preds = %107
  br label %110

; <label>:110:                                    ; preds = %.preheader107, %110
  %111 = phi i64 [ %115, %110 ], [ %108, %.preheader107 ]
  %112 = phi i64* [ %114, %110 ], [ %9, %.preheader107 ]
  %113 = phi i64* [ %112, %110 ], [ %17, %.preheader107 ]
  store i64 %111, i64* %113, align 8, !tbaa !2
  %114 = getelementptr inbounds i64, i64* %112, i64 -1
  %115 = load i64, i64* %114, align 8, !tbaa !2
  %116 = icmp ult i64 %18, %115
  br i1 %116, label %110, label %.loopexit17

; <label>:117:                                    ; preds = %15
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 16, i32 8, i1 false) #2
  br label %.loopexit17

.loopexit17:                                      ; preds = %110, %117, %107
  %118 = phi i64* [ %0, %117 ], [ %17, %107 ], [ %112, %110 ]
  store i64 %18, i64* %118, align 8, !tbaa !2
  %119 = getelementptr inbounds i64, i64* %0, i64 3
  %120 = load i64, i64* %119, align 8, !tbaa !2
  %121 = load i64, i64* %0, align 8, !tbaa !2
  %122 = icmp ult i64 %120, %121
  br i1 %122, label %133, label %123

; <label>:123:                                    ; preds = %.loopexit17
  %124 = load i64, i64* %17, align 8, !tbaa !2
  %125 = icmp ult i64 %120, %124
  br i1 %125, label %.preheader106, label %.loopexit16

.preheader106:                                    ; preds = %123
  br label %126

; <label>:126:                                    ; preds = %.preheader106, %126
  %127 = phi i64 [ %131, %126 ], [ %124, %.preheader106 ]
  %128 = phi i64* [ %130, %126 ], [ %17, %.preheader106 ]
  %129 = phi i64* [ %128, %126 ], [ %119, %.preheader106 ]
  store i64 %127, i64* %129, align 8, !tbaa !2
  %130 = getelementptr inbounds i64, i64* %128, i64 -1
  %131 = load i64, i64* %130, align 8, !tbaa !2
  %132 = icmp ult i64 %120, %131
  br i1 %132, label %126, label %.loopexit16

; <label>:133:                                    ; preds = %.loopexit17
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 24, i32 8, i1 false) #2
  br label %.loopexit16

.loopexit16:                                      ; preds = %126, %133, %123
  %134 = phi i64* [ %0, %133 ], [ %119, %123 ], [ %128, %126 ]
  store i64 %120, i64* %134, align 8, !tbaa !2
  %135 = getelementptr inbounds i64, i64* %0, i64 4
  %136 = load i64, i64* %135, align 8, !tbaa !2
  %137 = load i64, i64* %0, align 8, !tbaa !2
  %138 = icmp ult i64 %136, %137
  br i1 %138, label %149, label %139

; <label>:139:                                    ; preds = %.loopexit16
  %140 = load i64, i64* %119, align 8, !tbaa !2
  %141 = icmp ult i64 %136, %140
  br i1 %141, label %.preheader105, label %.loopexit15

.preheader105:                                    ; preds = %139
  br label %142

; <label>:142:                                    ; preds = %.preheader105, %142
  %143 = phi i64 [ %147, %142 ], [ %140, %.preheader105 ]
  %144 = phi i64* [ %146, %142 ], [ %119, %.preheader105 ]
  %145 = phi i64* [ %144, %142 ], [ %135, %.preheader105 ]
  store i64 %143, i64* %145, align 8, !tbaa !2
  %146 = getelementptr inbounds i64, i64* %144, i64 -1
  %147 = load i64, i64* %146, align 8, !tbaa !2
  %148 = icmp ult i64 %136, %147
  br i1 %148, label %142, label %.loopexit15

; <label>:149:                                    ; preds = %.loopexit16
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 32, i32 8, i1 false) #2
  br label %.loopexit15

.loopexit15:                                      ; preds = %142, %149, %139
  %150 = phi i64* [ %0, %149 ], [ %135, %139 ], [ %144, %142 ]
  store i64 %136, i64* %150, align 8, !tbaa !2
  %151 = getelementptr inbounds i64, i64* %0, i64 5
  %152 = load i64, i64* %151, align 8, !tbaa !2
  %153 = load i64, i64* %0, align 8, !tbaa !2
  %154 = icmp ult i64 %152, %153
  br i1 %154, label %165, label %155

; <label>:155:                                    ; preds = %.loopexit15
  %156 = load i64, i64* %135, align 8, !tbaa !2
  %157 = icmp ult i64 %152, %156
  br i1 %157, label %.preheader104, label %.loopexit14

.preheader104:                                    ; preds = %155
  br label %158

; <label>:158:                                    ; preds = %.preheader104, %158
  %159 = phi i64 [ %163, %158 ], [ %156, %.preheader104 ]
  %160 = phi i64* [ %162, %158 ], [ %135, %.preheader104 ]
  %161 = phi i64* [ %160, %158 ], [ %151, %.preheader104 ]
  store i64 %159, i64* %161, align 8, !tbaa !2
  %162 = getelementptr inbounds i64, i64* %160, i64 -1
  %163 = load i64, i64* %162, align 8, !tbaa !2
  %164 = icmp ult i64 %152, %163
  br i1 %164, label %158, label %.loopexit14

; <label>:165:                                    ; preds = %.loopexit15
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 40, i32 8, i1 false) #2
  br label %.loopexit14

.loopexit14:                                      ; preds = %158, %165, %155
  %166 = phi i64* [ %0, %165 ], [ %151, %155 ], [ %160, %158 ]
  store i64 %152, i64* %166, align 8, !tbaa !2
  %167 = getelementptr inbounds i64, i64* %0, i64 6
  %168 = load i64, i64* %167, align 8, !tbaa !2
  %169 = load i64, i64* %0, align 8, !tbaa !2
  %170 = icmp ult i64 %168, %169
  br i1 %170, label %181, label %171

; <label>:171:                                    ; preds = %.loopexit14
  %172 = load i64, i64* %151, align 8, !tbaa !2
  %173 = icmp ult i64 %168, %172
  br i1 %173, label %.preheader103, label %.loopexit13

.preheader103:                                    ; preds = %171
  br label %174

; <label>:174:                                    ; preds = %.preheader103, %174
  %175 = phi i64 [ %179, %174 ], [ %172, %.preheader103 ]
  %176 = phi i64* [ %178, %174 ], [ %151, %.preheader103 ]
  %177 = phi i64* [ %176, %174 ], [ %167, %.preheader103 ]
  store i64 %175, i64* %177, align 8, !tbaa !2
  %178 = getelementptr inbounds i64, i64* %176, i64 -1
  %179 = load i64, i64* %178, align 8, !tbaa !2
  %180 = icmp ult i64 %168, %179
  br i1 %180, label %174, label %.loopexit13

; <label>:181:                                    ; preds = %.loopexit14
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 48, i32 8, i1 false) #2
  br label %.loopexit13

.loopexit13:                                      ; preds = %174, %181, %171
  %182 = phi i64* [ %0, %181 ], [ %167, %171 ], [ %176, %174 ]
  store i64 %168, i64* %182, align 8, !tbaa !2
  %183 = getelementptr inbounds i64, i64* %0, i64 7
  %184 = load i64, i64* %183, align 8, !tbaa !2
  %185 = load i64, i64* %0, align 8, !tbaa !2
  %186 = icmp ult i64 %184, %185
  br i1 %186, label %197, label %187

; <label>:187:                                    ; preds = %.loopexit13
  %188 = load i64, i64* %167, align 8, !tbaa !2
  %189 = icmp ult i64 %184, %188
  br i1 %189, label %.preheader102, label %.loopexit12

.preheader102:                                    ; preds = %187
  br label %190

; <label>:190:                                    ; preds = %.preheader102, %190
  %191 = phi i64 [ %195, %190 ], [ %188, %.preheader102 ]
  %192 = phi i64* [ %194, %190 ], [ %167, %.preheader102 ]
  %193 = phi i64* [ %192, %190 ], [ %183, %.preheader102 ]
  store i64 %191, i64* %193, align 8, !tbaa !2
  %194 = getelementptr inbounds i64, i64* %192, i64 -1
  %195 = load i64, i64* %194, align 8, !tbaa !2
  %196 = icmp ult i64 %184, %195
  br i1 %196, label %190, label %.loopexit12

; <label>:197:                                    ; preds = %.loopexit13
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 56, i32 8, i1 false) #2
  br label %.loopexit12

.loopexit12:                                      ; preds = %190, %197, %187
  %198 = phi i64* [ %0, %197 ], [ %183, %187 ], [ %192, %190 ]
  store i64 %184, i64* %198, align 8, !tbaa !2
  %199 = getelementptr inbounds i64, i64* %0, i64 8
  %200 = load i64, i64* %199, align 8, !tbaa !2
  %201 = load i64, i64* %0, align 8, !tbaa !2
  %202 = icmp ult i64 %200, %201
  br i1 %202, label %213, label %203

; <label>:203:                                    ; preds = %.loopexit12
  %204 = load i64, i64* %183, align 8, !tbaa !2
  %205 = icmp ult i64 %200, %204
  br i1 %205, label %.preheader101, label %.loopexit11

.preheader101:                                    ; preds = %203
  br label %206

; <label>:206:                                    ; preds = %.preheader101, %206
  %207 = phi i64 [ %211, %206 ], [ %204, %.preheader101 ]
  %208 = phi i64* [ %210, %206 ], [ %183, %.preheader101 ]
  %209 = phi i64* [ %208, %206 ], [ %199, %.preheader101 ]
  store i64 %207, i64* %209, align 8, !tbaa !2
  %210 = getelementptr inbounds i64, i64* %208, i64 -1
  %211 = load i64, i64* %210, align 8, !tbaa !2
  %212 = icmp ult i64 %200, %211
  br i1 %212, label %206, label %.loopexit11

; <label>:213:                                    ; preds = %.loopexit12
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 64, i32 8, i1 false) #2
  br label %.loopexit11

.loopexit11:                                      ; preds = %206, %213, %203
  %214 = phi i64* [ %0, %213 ], [ %199, %203 ], [ %208, %206 ]
  store i64 %200, i64* %214, align 8, !tbaa !2
  %215 = getelementptr inbounds i64, i64* %0, i64 9
  %216 = load i64, i64* %215, align 8, !tbaa !2
  %217 = load i64, i64* %0, align 8, !tbaa !2
  %218 = icmp ult i64 %216, %217
  br i1 %218, label %229, label %219

; <label>:219:                                    ; preds = %.loopexit11
  %220 = load i64, i64* %199, align 8, !tbaa !2
  %221 = icmp ult i64 %216, %220
  br i1 %221, label %.preheader100, label %.loopexit10

.preheader100:                                    ; preds = %219
  br label %222

; <label>:222:                                    ; preds = %.preheader100, %222
  %223 = phi i64 [ %227, %222 ], [ %220, %.preheader100 ]
  %224 = phi i64* [ %226, %222 ], [ %199, %.preheader100 ]
  %225 = phi i64* [ %224, %222 ], [ %215, %.preheader100 ]
  store i64 %223, i64* %225, align 8, !tbaa !2
  %226 = getelementptr inbounds i64, i64* %224, i64 -1
  %227 = load i64, i64* %226, align 8, !tbaa !2
  %228 = icmp ult i64 %216, %227
  br i1 %228, label %222, label %.loopexit10

; <label>:229:                                    ; preds = %.loopexit11
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 72, i32 8, i1 false) #2
  br label %.loopexit10

.loopexit10:                                      ; preds = %222, %229, %219
  %230 = phi i64* [ %0, %229 ], [ %215, %219 ], [ %224, %222 ]
  store i64 %216, i64* %230, align 8, !tbaa !2
  %231 = getelementptr inbounds i64, i64* %0, i64 10
  %232 = load i64, i64* %231, align 8, !tbaa !2
  %233 = load i64, i64* %0, align 8, !tbaa !2
  %234 = icmp ult i64 %232, %233
  br i1 %234, label %245, label %235

; <label>:235:                                    ; preds = %.loopexit10
  %236 = load i64, i64* %215, align 8, !tbaa !2
  %237 = icmp ult i64 %232, %236
  br i1 %237, label %.preheader99, label %.loopexit9

.preheader99:                                     ; preds = %235
  br label %238

; <label>:238:                                    ; preds = %.preheader99, %238
  %239 = phi i64 [ %243, %238 ], [ %236, %.preheader99 ]
  %240 = phi i64* [ %242, %238 ], [ %215, %.preheader99 ]
  %241 = phi i64* [ %240, %238 ], [ %231, %.preheader99 ]
  store i64 %239, i64* %241, align 8, !tbaa !2
  %242 = getelementptr inbounds i64, i64* %240, i64 -1
  %243 = load i64, i64* %242, align 8, !tbaa !2
  %244 = icmp ult i64 %232, %243
  br i1 %244, label %238, label %.loopexit9

; <label>:245:                                    ; preds = %.loopexit10
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 80, i32 8, i1 false) #2
  br label %.loopexit9

.loopexit9:                                       ; preds = %238, %245, %235
  %246 = phi i64* [ %0, %245 ], [ %231, %235 ], [ %240, %238 ]
  store i64 %232, i64* %246, align 8, !tbaa !2
  %247 = getelementptr inbounds i64, i64* %0, i64 11
  %248 = load i64, i64* %247, align 8, !tbaa !2
  %249 = load i64, i64* %0, align 8, !tbaa !2
  %250 = icmp ult i64 %248, %249
  br i1 %250, label %261, label %251

; <label>:251:                                    ; preds = %.loopexit9
  %252 = load i64, i64* %231, align 8, !tbaa !2
  %253 = icmp ult i64 %248, %252
  br i1 %253, label %.preheader98, label %.loopexit8

.preheader98:                                     ; preds = %251
  br label %254

; <label>:254:                                    ; preds = %.preheader98, %254
  %255 = phi i64 [ %259, %254 ], [ %252, %.preheader98 ]
  %256 = phi i64* [ %258, %254 ], [ %231, %.preheader98 ]
  %257 = phi i64* [ %256, %254 ], [ %247, %.preheader98 ]
  store i64 %255, i64* %257, align 8, !tbaa !2
  %258 = getelementptr inbounds i64, i64* %256, i64 -1
  %259 = load i64, i64* %258, align 8, !tbaa !2
  %260 = icmp ult i64 %248, %259
  br i1 %260, label %254, label %.loopexit8

; <label>:261:                                    ; preds = %.loopexit9
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 88, i32 8, i1 false) #2
  br label %.loopexit8

.loopexit8:                                       ; preds = %254, %261, %251
  %262 = phi i64* [ %0, %261 ], [ %247, %251 ], [ %256, %254 ]
  store i64 %248, i64* %262, align 8, !tbaa !2
  %263 = getelementptr inbounds i64, i64* %0, i64 12
  %264 = load i64, i64* %263, align 8, !tbaa !2
  %265 = load i64, i64* %0, align 8, !tbaa !2
  %266 = icmp ult i64 %264, %265
  br i1 %266, label %277, label %267

; <label>:267:                                    ; preds = %.loopexit8
  %268 = load i64, i64* %247, align 8, !tbaa !2
  %269 = icmp ult i64 %264, %268
  br i1 %269, label %.preheader97, label %.loopexit7

.preheader97:                                     ; preds = %267
  br label %270

; <label>:270:                                    ; preds = %.preheader97, %270
  %271 = phi i64 [ %275, %270 ], [ %268, %.preheader97 ]
  %272 = phi i64* [ %274, %270 ], [ %247, %.preheader97 ]
  %273 = phi i64* [ %272, %270 ], [ %263, %.preheader97 ]
  store i64 %271, i64* %273, align 8, !tbaa !2
  %274 = getelementptr inbounds i64, i64* %272, i64 -1
  %275 = load i64, i64* %274, align 8, !tbaa !2
  %276 = icmp ult i64 %264, %275
  br i1 %276, label %270, label %.loopexit7

; <label>:277:                                    ; preds = %.loopexit8
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 96, i32 8, i1 false) #2
  br label %.loopexit7

.loopexit7:                                       ; preds = %270, %277, %267
  %278 = phi i64* [ %0, %277 ], [ %263, %267 ], [ %272, %270 ]
  store i64 %264, i64* %278, align 8, !tbaa !2
  %279 = getelementptr inbounds i64, i64* %0, i64 13
  %280 = load i64, i64* %279, align 8, !tbaa !2
  %281 = load i64, i64* %0, align 8, !tbaa !2
  %282 = icmp ult i64 %280, %281
  br i1 %282, label %293, label %283

; <label>:283:                                    ; preds = %.loopexit7
  %284 = load i64, i64* %263, align 8, !tbaa !2
  %285 = icmp ult i64 %280, %284
  br i1 %285, label %.preheader96, label %.loopexit6

.preheader96:                                     ; preds = %283
  br label %286

; <label>:286:                                    ; preds = %.preheader96, %286
  %287 = phi i64 [ %291, %286 ], [ %284, %.preheader96 ]
  %288 = phi i64* [ %290, %286 ], [ %263, %.preheader96 ]
  %289 = phi i64* [ %288, %286 ], [ %279, %.preheader96 ]
  store i64 %287, i64* %289, align 8, !tbaa !2
  %290 = getelementptr inbounds i64, i64* %288, i64 -1
  %291 = load i64, i64* %290, align 8, !tbaa !2
  %292 = icmp ult i64 %280, %291
  br i1 %292, label %286, label %.loopexit6

; <label>:293:                                    ; preds = %.loopexit7
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 104, i32 8, i1 false) #2
  br label %.loopexit6

.loopexit6:                                       ; preds = %286, %293, %283
  %294 = phi i64* [ %0, %293 ], [ %279, %283 ], [ %288, %286 ]
  store i64 %280, i64* %294, align 8, !tbaa !2
  %295 = getelementptr inbounds i64, i64* %0, i64 14
  %296 = load i64, i64* %295, align 8, !tbaa !2
  %297 = load i64, i64* %0, align 8, !tbaa !2
  %298 = icmp ult i64 %296, %297
  br i1 %298, label %309, label %299

; <label>:299:                                    ; preds = %.loopexit6
  %300 = load i64, i64* %279, align 8, !tbaa !2
  %301 = icmp ult i64 %296, %300
  br i1 %301, label %.preheader95, label %.loopexit5

.preheader95:                                     ; preds = %299
  br label %302

; <label>:302:                                    ; preds = %.preheader95, %302
  %303 = phi i64 [ %307, %302 ], [ %300, %.preheader95 ]
  %304 = phi i64* [ %306, %302 ], [ %279, %.preheader95 ]
  %305 = phi i64* [ %304, %302 ], [ %295, %.preheader95 ]
  store i64 %303, i64* %305, align 8, !tbaa !2
  %306 = getelementptr inbounds i64, i64* %304, i64 -1
  %307 = load i64, i64* %306, align 8, !tbaa !2
  %308 = icmp ult i64 %296, %307
  br i1 %308, label %302, label %.loopexit5

; <label>:309:                                    ; preds = %.loopexit6
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 112, i32 8, i1 false) #2
  br label %.loopexit5

.loopexit5:                                       ; preds = %302, %309, %299
  %310 = phi i64* [ %0, %309 ], [ %295, %299 ], [ %304, %302 ]
  store i64 %296, i64* %310, align 8, !tbaa !2
  %311 = getelementptr inbounds i64, i64* %0, i64 15
  %312 = load i64, i64* %311, align 8, !tbaa !2
  %313 = load i64, i64* %0, align 8, !tbaa !2
  %314 = icmp ult i64 %312, %313
  br i1 %314, label %325, label %315

; <label>:315:                                    ; preds = %.loopexit5
  %316 = load i64, i64* %295, align 8, !tbaa !2
  %317 = icmp ult i64 %312, %316
  br i1 %317, label %.preheader94, label %.loopexit4

.preheader94:                                     ; preds = %315
  br label %318

; <label>:318:                                    ; preds = %.preheader94, %318
  %319 = phi i64 [ %323, %318 ], [ %316, %.preheader94 ]
  %320 = phi i64* [ %322, %318 ], [ %295, %.preheader94 ]
  %321 = phi i64* [ %320, %318 ], [ %311, %.preheader94 ]
  store i64 %319, i64* %321, align 8, !tbaa !2
  %322 = getelementptr inbounds i64, i64* %320, i64 -1
  %323 = load i64, i64* %322, align 8, !tbaa !2
  %324 = icmp ult i64 %312, %323
  br i1 %324, label %318, label %.loopexit4

; <label>:325:                                    ; preds = %.loopexit5
  tail call void @llvm.memmove.p0i8.p0i8.i64(i8* nonnull %10, i8* nonnull %8, i64 120, i32 8, i1 false) #2
  br label %.loopexit4

.loopexit4:                                       ; preds = %318, %325, %315
  %326 = phi i64* [ %0, %325 ], [ %311, %315 ], [ %320, %318 ]
  store i64 %312, i64* %326, align 8, !tbaa !2
  %327 = getelementptr inbounds i64, i64* %0, i64 16
  %328 = icmp eq i64* %327, %1
  br i1 %328, label %.loopexit2, label %21
}

; Function Attrs: norecurse uwtable
define linkonce_odr void @_ZSt11__make_heapIN9__gnu_cxx17__normal_iteratorIPmSt6vectorImSaImEEEENS0_5__ops15_Iter_less_iterEEvT_S9_RT0_(i64*, i64*, %"struct.__gnu_cxx::__ops::_Iter_less_iter"* dereferenceable(1)) local_unnamed_addr #10 comdat {
  %4 = ptrtoint i64* %0 to i64
  %5 = ptrtoint i64* %1 to i64
  %6 = sub i64 %5, %4
  %7 = ashr exact i64 %6, 3
  %8 = icmp slt i64 %6, 16
  br i1 %8, label %.loopexit2, label %9

; <label>:9:                                      ; preds = %3
  %10 = add nsw i64 %7, -2
  %11 = sdiv i64 %10, 2
  %12 = add nsw i64 %7, -1
  %13 = sdiv i64 %12, 2
  %14 = and i64 %6, 8
  %15 = icmp eq i64 %14, 0
  br i1 %15, label %16, label %.preheader30

.preheader30:                                     ; preds = %9
  br label %62

; <label>:16:                                     ; preds = %9
  %17 = shl nsw i64 %11, 1
  %18 = or i64 %17, 1
  %19 = getelementptr inbounds i64, i64* %0, i64 %18
  %20 = getelementptr inbounds i64, i64* %0, i64 %11
  br label %21

; <label>:21:                                     ; preds = %.loopexit, %16
  %22 = phi i64 [ %11, %16 ], [ %61, %.loopexit ]
  %23 = getelementptr inbounds i64, i64* %0, i64 %22
  %24 = load i64, i64* %23, align 8, !tbaa !2
  %25 = icmp sgt i64 %13, %22
  br i1 %25, label %.preheader26, label %.loopexit1

.preheader26:                                     ; preds = %21
  br label %26

; <label>:26:                                     ; preds = %.preheader26, %26
  %27 = phi i64 [ %36, %26 ], [ %22, %.preheader26 ]
  %28 = shl i64 %27, 1
  %29 = add i64 %28, 2
  %30 = getelementptr inbounds i64, i64* %0, i64 %29
  %31 = or i64 %28, 1
  %32 = getelementptr inbounds i64, i64* %0, i64 %31
  %33 = load i64, i64* %30, align 8, !tbaa !2
  %34 = load i64, i64* %32, align 8, !tbaa !2
  %35 = icmp ult i64 %33, %34
  %36 = select i1 %35, i64 %31, i64 %29
  %37 = getelementptr inbounds i64, i64* %0, i64 %36
  %38 = load i64, i64* %37, align 8, !tbaa !2
  %39 = getelementptr inbounds i64, i64* %0, i64 %27
  store i64 %38, i64* %39, align 8, !tbaa !2
  %40 = icmp slt i64 %36, %13
  br i1 %40, label %26, label %.loopexit1

.loopexit1:                                       ; preds = %26, %21
  %41 = phi i64 [ %22, %21 ], [ %36, %26 ]
  %42 = icmp eq i64 %41, %11
  br i1 %42, label %43, label %45

; <label>:43:                                     ; preds = %.loopexit1
  %44 = load i64, i64* %19, align 8, !tbaa !2
  store i64 %44, i64* %20, align 8, !tbaa !2
  br label %45

; <label>:45:                                     ; preds = %43, %.loopexit1
  %46 = phi i64 [ %18, %43 ], [ %41, %.loopexit1 ]
  %47 = icmp sgt i64 %46, %22
  br i1 %47, label %.preheader, label %.loopexit

.preheader:                                       ; preds = %45
  br label %48

; <label>:48:                                     ; preds = %.preheader, %55
  %49 = phi i64 [ %51, %55 ], [ %46, %.preheader ]
  %50 = add nsw i64 %49, -1
  %51 = sdiv i64 %50, 2
  %52 = getelementptr inbounds i64, i64* %0, i64 %51
  %53 = load i64, i64* %52, align 8, !tbaa !2
  %54 = icmp ult i64 %53, %24
  br i1 %54, label %55, label %.loopexit

; <label>:55:                                     ; preds = %48
  %56 = getelementptr inbounds i64, i64* %0, i64 %49
  store i64 %53, i64* %56, align 8, !tbaa !2
  %57 = icmp sgt i64 %51, %22
  br i1 %57, label %48, label %.loopexit

.loopexit:                                        ; preds = %55, %48, %45
  %58 = phi i64 [ %46, %45 ], [ %49, %48 ], [ %51, %55 ]
  %59 = getelementptr inbounds i64, i64* %0, i64 %58
  store i64 %24, i64* %59, align 8, !tbaa !2
  %60 = icmp eq i64 %22, 0
  %61 = add nsw i64 %22, -1
  br i1 %60, label %.loopexit2, label %21

; <label>:62:                                     ; preds = %.preheader30, %.loopexit3
  %63 = phi i64 [ %97, %.loopexit3 ], [ %11, %.preheader30 ]
  %64 = getelementptr inbounds i64, i64* %0, i64 %63
  %65 = load i64, i64* %64, align 8, !tbaa !2
  %66 = icmp sgt i64 %13, %63
  br i1 %66, label %.preheader29, label %.loopexit3

.preheader29:                                     ; preds = %62
  br label %67

; <label>:67:                                     ; preds = %.preheader29, %67
  %68 = phi i64 [ %77, %67 ], [ %63, %.preheader29 ]
  %69 = shl i64 %68, 1
  %70 = add i64 %69, 2
  %71 = getelementptr inbounds i64, i64* %0, i64 %70
  %72 = or i64 %69, 1
  %73 = getelementptr inbounds i64, i64* %0, i64 %72
  %74 = load i64, i64* %71, align 8, !tbaa !2
  %75 = load i64, i64* %73, align 8, !tbaa !2
  %76 = icmp ult i64 %74, %75
  %77 = select i1 %76, i64 %72, i64 %70
  %78 = getelementptr inbounds i64, i64* %0, i64 %77
  %79 = load i64, i64* %78, align 8, !tbaa !2
  %80 = getelementptr inbounds i64, i64* %0, i64 %68
  store i64 %79, i64* %80, align 8, !tbaa !2
  %81 = icmp slt i64 %77, %13
  br i1 %81, label %67, label %82

; <label>:82:                                     ; preds = %67
  %83 = getelementptr inbounds i64, i64* %0, i64 %77
  %84 = icmp sgt i64 %77, %63
  br i1 %84, label %.preheader27, label %.loopexit3

.preheader27:                                     ; preds = %82
  br label %85

; <label>:85:                                     ; preds = %.preheader27, %93
  %86 = phi i64 [ %88, %93 ], [ %77, %.preheader27 ]
  %87 = add nsw i64 %86, -1
  %88 = sdiv i64 %87, 2
  %89 = getelementptr inbounds i64, i64* %0, i64 %88
  %90 = load i64, i64* %89, align 8, !tbaa !2
  %91 = icmp ult i64 %90, %65
  %92 = getelementptr inbounds i64, i64* %0, i64 %86
  br i1 %91, label %93, label %.loopexit3

; <label>:93:                                     ; preds = %85
  store i64 %90, i64* %92, align 8, !tbaa !2
  %94 = icmp sgt i64 %88, %63
  br i1 %94, label %85, label %.loopexit3.loopexit

.loopexit3.loopexit:                              ; preds = %93
  %95 = getelementptr inbounds i64, i64* %0, i64 %88
  br label %.loopexit3

.loopexit3:                                       ; preds = %85, %.loopexit3.loopexit, %82, %62
  %.pre-phi = phi i64* [ %83, %82 ], [ %64, %62 ], [ %95, %.loopexit3.loopexit ], [ %92, %85 ]
  store i64 %65, i64* %.pre-phi, align 8, !tbaa !2
  %96 = icmp eq i64 %63, 0
  %97 = add nsw i64 %63, -1
  br i1 %96, label %.loopexit2, label %62

.loopexit2:                                       ; preds = %.loopexit3, %.loopexit, %3
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
  %22 = inttoptr i64 %16 to i64*
  br i1 %19, label %23, label %41

; <label>:23:                                     ; preds = %4
  %24 = icmp eq i64 %10, 0
  br i1 %24, label %._crit_edge, label %25

._crit_edge:                                      ; preds = %23
  %.pre1 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  br label %32

; <label>:25:                                     ; preds = %23
  %26 = icmp ugt i64 %11, 2305843009213693951
  br i1 %26, label %27, label %28

; <label>:27:                                     ; preds = %25
  tail call void @_ZSt17__throw_bad_allocv() #16
  unreachable

; <label>:28:                                     ; preds = %25
  %29 = tail call i8* @_Znwm(i64 %10)
  %30 = bitcast i8* %29 to i64*
  %31 = inttoptr i64 %9 to i8*
  tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull %29, i8* %31, i64 %10, i32 8, i1 false) #2
  %.phi.trans.insert = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %.pre = load i64*, i64** %.phi.trans.insert, align 8, !tbaa !19
  br label %32

; <label>:32:                                     ; preds = %._crit_edge, %28
  %.pre-phi = phi i64** [ %.pre1, %._crit_edge ], [ %.phi.trans.insert, %28 ]
  %33 = phi i64* [ %22, %._crit_edge ], [ %.pre, %28 ]
  %34 = phi i64* [ null, %._crit_edge ], [ %30, %28 ]
  %35 = icmp eq i64* %33, null
  br i1 %35, label %38, label %36

; <label>:36:                                     ; preds = %32
  %37 = bitcast i64* %33 to i8*
  tail call void @_ZdlPv(i8* %37) #2
  br label %38

; <label>:38:                                     ; preds = %36, %32
  store i64* %34, i64** %.pre-phi, align 8, !tbaa !19
  %39 = getelementptr inbounds i64, i64* %34, i64 %11
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

; <label>:63:                                     ; preds = %55, %53
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

; <label>:75:                                     ; preds = %72, %63, %51, %49, %38
  %76 = phi i64** [ %42, %51 ], [ %42, %49 ], [ %42, %72 ], [ %42, %63 ], [ %40, %38 ]
  %77 = getelementptr inbounds %"class.std::vector", %"class.std::vector"* %0, i64 0, i32 0, i32 0, i32 0
  %78 = load i64*, i64** %77, align 8, !tbaa !19
  %79 = getelementptr inbounds i64, i64* %78, i64 %11
  store i64* %79, i64** %76, align 8, !tbaa !22
  br label %80

; <label>:80:                                     ; preds = %75, %2
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

; <label>:47:                                     ; preds = %40, %27
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

; <label>:64:                                     ; preds = %62, %60
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
attributes #4 = { norecurse nounwind readonly uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
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
