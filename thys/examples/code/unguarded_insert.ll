; Manually extracted from introsort.ll, for presentation only!

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

define i64* @Sorting_Introsort_unat_sort_is_unguarded_insert_impl(i64* %x, i64 %x1, i64 %x2) {

  start:
    %x3 = getelementptr i64, i64* %x, i64 %x2
    %r = load i64, i64* %x3
    %xa = insertvalue { i64, i64* } zeroinitializer, i64 %r, 0
    %xb = insertvalue { i64, i64* } %xa, i64* %x, 1
    %a1 = extractvalue { i64, i64* } %xb, 0
    %a2 = extractvalue { i64, i64* } %xb, 1
    %xc = insertvalue { i64*, i64 } zeroinitializer, i64* %a2, 0
    %xd = insertvalue { i64*, i64 } %xc, i64 %x2, 1
    br label %while_start

  while_start:
    %xca = phi { i64*, i64 } [ %x4, %while_body ], [ %xd, %start ]
    %a1a = extractvalue { i64*, i64 } %xca, 0
    %a2a = extractvalue { i64*, i64 } %xca, 1
    %bib = sub i64 %a2a, 1
    %xda = getelementptr i64, i64* %a1a, i64 %bib
    %ra = load i64, i64* %xda
    %xea = insertvalue { i64, i64* } zeroinitializer, i64 %ra, 0
    %xf = insertvalue { i64, i64* } %xea, i64* %a1a, 1
    %a1b = extractvalue { i64, i64* } %xf, 0
    %a2b = extractvalue { i64, i64* } %xf, 1
    %xg = icmp ult i64 %a1, %a1b
    %p = getelementptr i64, i64* %a2b, i64 %bib
    store i64 %a1b, i64* %p
    br i1 %xg, label %while_body, label %while_end

  while_body:
    %a1a1 = extractvalue { i64*, i64 } %xca, 0
    %a2a1 = extractvalue { i64*, i64 } %xca, 1
    %xda1 = sub i64 %a2a1, 1
    %xea1 = getelementptr i64, i64* %a1a1, i64 %xda1
    %ra1 = load i64, i64* %xea1
    %xf1 = insertvalue { i64, i64* } zeroinitializer, i64 %ra1, 0
    %xg1 = insertvalue { i64, i64* } %xf1, i64* %a1a1, 1
    %a1b1 = extractvalue { i64, i64* } %xg1, 0
    %a2b1 = extractvalue { i64, i64* } %xg1, 1
    %p1 = getelementptr i64, i64* %a2b1, i64 %a2a1
    store i64 %a1b1, i64* %p1
    %xia = sub i64 %a2a1, 1
    %xj = insertvalue { i64*, i64 } zeroinitializer, i64* %a2b1, 0
    %x4 = insertvalue { i64*, i64 } %xj, i64 %xia, 1
    br label %while_start

  while_end:
    %a1a2 = extractvalue { i64*, i64 } %xca, 0
    %a2a2 = extractvalue { i64*, i64 } %xca, 1
    %p2 = getelementptr i64, i64* %a1a2, i64 %a2a2
    store i64 %a1, i64* %p2
    ret i64* %a1a2
}
