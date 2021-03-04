; ModuleID = 'introsortXXX.ll'
source_filename = "introsortXXX.ll"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @isabelle_llvm_free(i8*) local_unnamed_addr

declare i8* @isabelle_llvm_calloc(i64, i64) local_unnamed_addr

; Function Attrs: norecurse nounwind
define void @LLVM_DS_Array_arraycpy(i8* nocapture %dst, i8* nocapture readonly %src, i64 %n) local_unnamed_addr #0 {
start:
  %x2 = icmp eq i64 %n, 0
  br i1 %x2, label %while_end, label %while_body.lr.ph

while_body.lr.ph:                                 ; preds = %start
  %min.iters.check = icmp ult i64 %n, 32
  br i1 %min.iters.check, label %while_body.preheader, label %vector.memcheck

vector.memcheck:                                  ; preds = %while_body.lr.ph
  %scevgep = getelementptr i8, i8* %dst, i64 %n
  %scevgep4 = getelementptr i8, i8* %src, i64 %n
  %bound0 = icmp ugt i8* %scevgep4, %dst
  %bound1 = icmp ugt i8* %scevgep, %src
  %memcheck.conflict = and i1 %bound0, %bound1
  br i1 %memcheck.conflict, label %while_body.preheader, label %vector.ph

vector.ph:                                        ; preds = %vector.memcheck
  %n.vec = and i64 %n, -32
  br label %vector.body

vector.body:                                      ; preds = %vector.body, %vector.ph
  %index = phi i64 [ 0, %vector.ph ], [ %index.next, %vector.body ]
  %0 = getelementptr i8, i8* %src, i64 %index
  %1 = bitcast i8* %0 to <16 x i8>*
  %wide.load = load <16 x i8>, <16 x i8>* %1, align 1, !alias.scope !0
  %2 = getelementptr i8, i8* %0, i64 16
  %3 = bitcast i8* %2 to <16 x i8>*
  %wide.load6 = load <16 x i8>, <16 x i8>* %3, align 1, !alias.scope !0
  %4 = getelementptr i8, i8* %dst, i64 %index
  %5 = bitcast i8* %4 to <16 x i8>*
  store <16 x i8> %wide.load, <16 x i8>* %5, align 1, !alias.scope !3, !noalias !0
  %6 = getelementptr i8, i8* %4, i64 16
  %7 = bitcast i8* %6 to <16 x i8>*
  store <16 x i8> %wide.load6, <16 x i8>* %7, align 1, !alias.scope !3, !noalias !0
  %index.next = add i64 %index, 32
  %8 = icmp eq i64 %index.next, %n.vec
  br i1 %8, label %middle.block, label %vector.body, !llvm.loop !5

middle.block:                                     ; preds = %vector.body
  %cmp.n = icmp eq i64 %n.vec, %n
  br i1 %cmp.n, label %while_end, label %while_body.preheader

while_body.preheader:                             ; preds = %middle.block, %vector.memcheck, %while_body.lr.ph
  %i3.ph = phi i64 [ 0, %vector.memcheck ], [ 0, %while_body.lr.ph ], [ %n.vec, %middle.block ]
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %i3 = phi i64 [ %x1, %while_body ], [ %i3.ph, %while_body.preheader ]
  %xa = getelementptr i8, i8* %src, i64 %i3
  %xaa = load i8, i8* %xa, align 1
  %p = getelementptr i8, i8* %dst, i64 %i3
  store i8 %xaa, i8* %p, align 1
  %x1 = add nuw i64 %i3, 1
  %exitcond = icmp eq i64 %x1, %n
  br i1 %exitcond, label %while_end, label %while_body, !llvm.loop !7

while_end:                                        ; preds = %while_body, %middle.block, %start
  ret void
}

define void @LLVM_DS_NArray_narray_free(i8* %p) local_unnamed_addr {
start:
  %tmp = icmp eq i8* %p, null
  br i1 %tmp, label %ctd_if, label %else

else:                                             ; preds = %start
  tail call void @isabelle_llvm_free(i8* nonnull %p)
  br label %ctd_if

ctd_if:                                           ; preds = %start, %else
  ret void
}

; Function Attrs: norecurse nounwind readonly
define i8 @llstrcmp({ i64, { i64, i8* } }* nocapture readonly %ap, { i64, { i64, i8* } }* nocapture readonly %bp) local_unnamed_addr #1 {
start:
  %a.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %ap, i64 0, i32 0
  %a.unpack = load i64, i64* %a.elt, align 8
  %a.unpack2.elt4 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %ap, i64 0, i32 1, i32 1
  %a.unpack2.unpack5 = load i8*, i8** %a.unpack2.elt4, align 8
  %b.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %bp, i64 0, i32 0
  %b.unpack = load i64, i64* %b.elt, align 8
  %b.unpack8.elt10 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %bp, i64 0, i32 1, i32 1
  %b.unpack8.unpack11 = load i8*, i8** %b.unpack8.elt10, align 8
  %xd.i = icmp sgt i64 %a.unpack, %b.unpack
  %la.l.i = select i1 %xd.i, i64 %b.unpack, i64 %a.unpack
  %xga1.i = icmp sgt i64 %la.l.i, 0
  br i1 %xga1.i, label %while_body.i.preheader, label %thend.i

while_body.i.preheader:                           ; preds = %start
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %ctd_ifa.i
  %a12.i = phi i64 [ %a1.i, %ctd_ifa.i ], [ 0, %while_body.i.preheader ]
  %xh.i = getelementptr i8, i8* %a.unpack2.unpack5, i64 %a12.i
  %xi.i = load i8, i8* %xh.i, align 1
  %xk.i = getelementptr i8, i8* %b.unpack8.unpack11, i64 %a12.i
  %xl.i = load i8, i8* %xk.i, align 1
  %xm.i = icmp eq i8 %xi.i, %xl.i
  br i1 %xm.i, label %thena.i, label %elsea.i

thena.i:                                          ; preds = %while_body.i
  %xna.i = add i64 %a12.i, 1
  %xo.i = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i, 0
  %x5.i = insertvalue { i64, i2 } %xo.i, i2 0, 1
  br label %ctd_ifa.i

elsea.i:                                          ; preds = %while_body.i
  %xn.i = icmp ult i8 %xi.i, %xl.i
  %xoa.i = add i64 %a12.i, 1
  %xp.i = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i, 0
  %x7.i = insertvalue { i64, i2 } %xp.i, i2 1, 1
  %x6.i = insertvalue { i64, i2 } %xp.i, i2 -1, 1
  %x8.i = select i1 %xn.i, { i64, i2 } %x6.i, { i64, i2 } %x7.i
  br label %ctd_ifa.i

ctd_ifa.i:                                        ; preds = %elsea.i, %thena.i
  %x9.i = phi { i64, i2 } [ %x5.i, %thena.i ], [ %x8.i, %elsea.i ]
  %a1.i = extractvalue { i64, i2 } %x9.i, 0
  %a2.i = extractvalue { i64, i2 } %x9.i, 1
  %xga.i = icmp slt i64 %a1.i, %la.l.i
  %x3.i = icmp eq i2 %a2.i, 0
  %x4.i = and i1 %xga.i, %x3.i
  br i1 %x4.i, label %while_body.i, label %while_end.i

while_end.i:                                      ; preds = %ctd_ifa.i
  switch i2 %a2.i, label %ctd_ifd.i [
    i2 -1, label %Sorting_Strings_strcmp_impl.exit
    i2 0, label %thend.i
  ]

thend.i:                                          ; preds = %while_end.i, %start
  %x10.i = icmp slt i64 %a.unpack, %b.unpack
  br label %ctd_ifd.i

ctd_ifd.i:                                        ; preds = %thend.i, %while_end.i
  %x11.i = phi i1 [ %x10.i, %thend.i ], [ false, %while_end.i ]
  br label %Sorting_Strings_strcmp_impl.exit

Sorting_Strings_strcmp_impl.exit:                 ; preds = %while_end.i, %ctd_ifd.i
  %x12.i = phi i1 [ %x11.i, %ctd_ifd.i ], [ true, %while_end.i ]
  %. = zext i1 %x12.i to i8
  ret i8 %.
}

; Function Attrs: norecurse nounwind
define void @str_init({ i64, { i64, i8* } }* nocapture %sp) local_unnamed_addr #0 {
start:
  %0 = bitcast { i64, { i64, i8* } }* %sp to i8*
  call void @llvm.memset.p0i8.i64(i8* %0, i8 0, i64 24, i32 8, i1 false)
  ret void
}

; Function Attrs: norecurse nounwind readnone
define i64 @Sorting_Log2_word_clz_impl(i64 %x) local_unnamed_addr #2 {
start:
  %x1 = icmp eq i64 %x, 0
  br i1 %x1, label %ctd_if, label %else

else:                                             ; preds = %start
  %x31.i = icmp sgt i64 %x, 0
  br i1 %x31.i, label %while_body.i.preheader, label %ctd_if

while_body.i.preheader:                           ; preds = %else
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %while_body.i
  %a114.i = phi i64 [ %xaa.i, %while_body.i ], [ 0, %while_body.i.preheader ]
  %x23.i = phi i64 [ %xba.i, %while_body.i ], [ %x, %while_body.i.preheader ]
  %xaa.i = add nuw nsw i64 %a114.i, 1
  %xba.i = shl i64 %x23.i, 1
  %x3.i = icmp sgt i64 %xba.i, 0
  br i1 %x3.i, label %while_body.i, label %ctd_if

ctd_if:                                           ; preds = %while_body.i, %else, %start
  %x3 = phi i64 [ 64, %start ], [ 0, %else ], [ %xaa.i, %while_body.i ]
  ret i64 %x3
}

; Function Attrs: norecurse nounwind readnone
define i64 @Sorting_Log2_word_clz_impl1(i64 %x) local_unnamed_addr #2 {
start:
  %x31 = icmp sgt i64 %x, 0
  br i1 %x31, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %a114 = phi i64 [ %xaa, %while_body ], [ 0, %while_body.preheader ]
  %x23 = phi i64 [ %xba, %while_body ], [ %x, %while_body.preheader ]
  %xaa = add nuw nsw i64 %a114, 1
  %xba = shl i64 %x23, 1
  %x3 = icmp sgt i64 %xba, 0
  br i1 %x3, label %while_body, label %while_end

while_end:                                        ; preds = %while_body, %start
  %a11.lcssa = phi i64 [ 0, %start ], [ %xaa, %while_body ]
  ret i64 %a11.lcssa
}

; Function Attrs: norecurse nounwind readonly
define i1 @Sorting_Strings_strcmp_impl({ i64, { i64, i8* } } %x, { i64, { i64, i8* } } %x1) local_unnamed_addr #1 {
start:
  %l = extractvalue { i64, { i64, i8* } } %x, 0
  %la = extractvalue { i64, { i64, i8* } } %x1, 0
  %xd = icmp sgt i64 %l, %la
  %la.l = select i1 %xd, i64 %la, i64 %l
  %xga1 = icmp sgt i64 %la.l, 0
  br i1 %xga1, label %while_body.lr.ph, label %thend

while_body.lr.ph:                                 ; preds = %start
  %xb = extractvalue { i64, { i64, i8* } } %x1, 1
  %x2 = extractvalue { i64, { i64, i8* } } %x, 1
  %ab2 = extractvalue { i64, i8* } %x2, 1
  %ac = extractvalue { i64, i8* } %xb, 1
  br label %while_body

while_body:                                       ; preds = %while_body.lr.ph, %ctd_ifa
  %a12 = phi i64 [ 0, %while_body.lr.ph ], [ %a1, %ctd_ifa ]
  %xh = getelementptr i8, i8* %ab2, i64 %a12
  %xi = load i8, i8* %xh, align 1
  %xk = getelementptr i8, i8* %ac, i64 %a12
  %xl = load i8, i8* %xk, align 1
  %xm = icmp eq i8 %xi, %xl
  br i1 %xm, label %thena, label %elsea

thena:                                            ; preds = %while_body
  %xna = add i64 %a12, 1
  %xo = insertvalue { i64, i2 } zeroinitializer, i64 %xna, 0
  %x5 = insertvalue { i64, i2 } %xo, i2 0, 1
  br label %ctd_ifa

elsea:                                            ; preds = %while_body
  %xn = icmp ult i8 %xi, %xl
  %xoa = add i64 %a12, 1
  %xp = insertvalue { i64, i2 } zeroinitializer, i64 %xoa, 0
  %x7 = insertvalue { i64, i2 } %xp, i2 1, 1
  %x6 = insertvalue { i64, i2 } %xp, i2 -1, 1
  %x8 = select i1 %xn, { i64, i2 } %x6, { i64, i2 } %x7
  br label %ctd_ifa

ctd_ifa:                                          ; preds = %elsea, %thena
  %x9 = phi { i64, i2 } [ %x5, %thena ], [ %x8, %elsea ]
  %a1 = extractvalue { i64, i2 } %x9, 0
  %a2 = extractvalue { i64, i2 } %x9, 1
  %xga = icmp slt i64 %a1, %la.l
  %x3 = icmp eq i2 %a2, 0
  %x4 = and i1 %xga, %x3
  br i1 %x4, label %while_body, label %while_end

while_end:                                        ; preds = %ctd_ifa
  switch i2 %a2, label %ctd_ifd [
    i2 -1, label %ctd_ifc
    i2 0, label %thend
  ]

thend:                                            ; preds = %start, %while_end
  %x10 = icmp slt i64 %l, %la
  br label %ctd_ifd

ctd_ifd:                                          ; preds = %while_end, %thend
  %x11 = phi i1 [ %x10, %thend ], [ false, %while_end ]
  br label %ctd_ifc

ctd_ifc:                                          ; preds = %while_end, %ctd_ifd
  %x12 = phi i1 [ %x11, %ctd_ifd ], [ true, %while_end ]
  ret i1 %x12
}

define void @str_append({ i64, { i64, i8* } }* nocapture %sp, i8 %x) local_unnamed_addr {
start:
  %s.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %sp, i64 0, i32 0
  %s.unpack = load i64, i64* %s.elt, align 8
  %s.unpack2.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %sp, i64 0, i32 1, i32 0
  %s.unpack2.unpack = load i64, i64* %s.unpack2.elt, align 8
  %s.unpack2.elt4 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %sp, i64 0, i32 1, i32 1
  %s.unpack2.unpack5 = load i8*, i8** %s.unpack2.elt4, align 8
  %lb = add i64 %s.unpack, 1
  %cok = icmp sgt i64 %lb, %s.unpack2.unpack
  br i1 %cok, label %else, label %ctd_if

else:                                             ; preds = %start
  %b.i = icmp ult i64 %s.unpack2.unpack, 4611686018427387904
  br i1 %b.i, label %then.i, label %ctd_if.i

then.i:                                           ; preds = %else
  %ca.i = shl i64 %s.unpack2.unpack, 1
  %cok.i = icmp slt i64 %ca.i, %lb
  %ca.c.i = select i1 %cok.i, i64 %lb, i64 %ca.i
  br label %ctd_if.i

ctd_if.i:                                         ; preds = %then.i, %else
  %ca1.i = phi i64 [ %ca.c.i, %then.i ], [ %lb, %else ]
  %tmpa.i = icmp eq i64 %ca1.i, 0
  br i1 %tmpa.i, label %ctd_ifb.i, label %elseb.i

elseb.i:                                          ; preds = %ctd_if.i
  %e.i = tail call i8* @isabelle_llvm_calloc(i64 %ca1.i, i64 1)
  br label %ctd_ifb.i

ctd_ifb.i:                                        ; preds = %elseb.i, %ctd_if.i
  %a1.i = phi i8* [ %e.i, %elseb.i ], [ null, %ctd_if.i ]
  %x2.i.i = icmp eq i64 %s.unpack, 0
  br i1 %x2.i.i, label %LLVM_DS_Array_arraycpy.exit.i, label %while_body.lr.ph.i.i

while_body.lr.ph.i.i:                             ; preds = %ctd_ifb.i
  %min.iters.check = icmp ult i64 %s.unpack, 32
  br i1 %min.iters.check, label %while_body.i.i.preheader, label %vector.memcheck

vector.memcheck:                                  ; preds = %while_body.lr.ph.i.i
  %scevgep = getelementptr i8, i8* %a1.i, i64 %s.unpack
  %scevgep11 = getelementptr i8, i8* %s.unpack2.unpack5, i64 %s.unpack
  %bound0 = icmp ult i8* %a1.i, %scevgep11
  %bound1 = icmp ult i8* %s.unpack2.unpack5, %scevgep
  %memcheck.conflict = and i1 %bound0, %bound1
  br i1 %memcheck.conflict, label %while_body.i.i.preheader, label %vector.ph

vector.ph:                                        ; preds = %vector.memcheck
  %n.vec = and i64 %s.unpack, -32
  br label %vector.body

vector.body:                                      ; preds = %vector.body, %vector.ph
  %index = phi i64 [ 0, %vector.ph ], [ %index.next, %vector.body ]
  %0 = getelementptr i8, i8* %s.unpack2.unpack5, i64 %index
  %1 = bitcast i8* %0 to <16 x i8>*
  %wide.load = load <16 x i8>, <16 x i8>* %1, align 1, !alias.scope !8
  %2 = getelementptr i8, i8* %0, i64 16
  %3 = bitcast i8* %2 to <16 x i8>*
  %wide.load13 = load <16 x i8>, <16 x i8>* %3, align 1, !alias.scope !8
  %4 = getelementptr i8, i8* %a1.i, i64 %index
  %5 = bitcast i8* %4 to <16 x i8>*
  store <16 x i8> %wide.load, <16 x i8>* %5, align 1, !alias.scope !11, !noalias !8
  %6 = getelementptr i8, i8* %4, i64 16
  %7 = bitcast i8* %6 to <16 x i8>*
  store <16 x i8> %wide.load13, <16 x i8>* %7, align 1, !alias.scope !11, !noalias !8
  %index.next = add i64 %index, 32
  %8 = icmp eq i64 %index.next, %n.vec
  br i1 %8, label %middle.block, label %vector.body, !llvm.loop !13

middle.block:                                     ; preds = %vector.body
  %cmp.n = icmp eq i64 %s.unpack, %n.vec
  br i1 %cmp.n, label %else.i.i, label %while_body.i.i.preheader

while_body.i.i.preheader:                         ; preds = %middle.block, %vector.memcheck, %while_body.lr.ph.i.i
  %i3.i.i.ph = phi i64 [ 0, %vector.memcheck ], [ 0, %while_body.lr.ph.i.i ], [ %n.vec, %middle.block ]
  br label %while_body.i.i

while_body.i.i:                                   ; preds = %while_body.i.i.preheader, %while_body.i.i
  %i3.i.i = phi i64 [ %x1.i.i, %while_body.i.i ], [ %i3.i.i.ph, %while_body.i.i.preheader ]
  %xa.i.i = getelementptr i8, i8* %s.unpack2.unpack5, i64 %i3.i.i
  %xaa.i.i = load i8, i8* %xa.i.i, align 1
  %p.i.i = getelementptr i8, i8* %a1.i, i64 %i3.i.i
  store i8 %xaa.i.i, i8* %p.i.i, align 1
  %x1.i.i = add nuw i64 %i3.i.i, 1
  %exitcond.i.i = icmp eq i64 %x1.i.i, %s.unpack
  br i1 %exitcond.i.i, label %else.i.i, label %while_body.i.i, !llvm.loop !14

LLVM_DS_Array_arraycpy.exit.i:                    ; preds = %ctd_ifb.i
  %tmp.i.i = icmp eq i8* %s.unpack2.unpack5, null
  br i1 %tmp.i.i, label %ctd_if, label %else.i.i

else.i.i:                                         ; preds = %while_body.i.i, %middle.block, %LLVM_DS_Array_arraycpy.exit.i
  tail call void @isabelle_llvm_free(i8* nonnull %s.unpack2.unpack5)
  br label %ctd_if

ctd_if:                                           ; preds = %else.i.i, %LLVM_DS_Array_arraycpy.exit.i, %start
  %ca1.i.sink = phi i64 [ %s.unpack2.unpack, %start ], [ %ca1.i, %LLVM_DS_Array_arraycpy.exit.i ], [ %ca1.i, %else.i.i ]
  %a1.i.sink = phi i8* [ %s.unpack2.unpack5, %start ], [ %a1.i, %LLVM_DS_Array_arraycpy.exit.i ], [ %a1.i, %else.i.i ]
  %p = getelementptr i8, i8* %a1.i.sink, i64 %s.unpack
  store i8 %x, i8* %p, align 1
  %le = add i64 %s.unpack, 1
  store i64 %le, i64* %s.elt, align 8
  store i64 %ca1.i.sink, i64* %s.unpack2.elt, align 8
  store i8* %a1.i.sink, i8** %s.unpack2.elt4, align 8
  ret void
}

define { i64, { i64, i8* } } @LLVM_DS_Array_List_arl_resize(i64 %c, { i64, { i64, i8* } } %al) local_unnamed_addr {
start:
  %l = extractvalue { i64, { i64, i8* } } %al, 0
  %x = extractvalue { i64, { i64, i8* } } %al, 1
  %c1 = extractvalue { i64, i8* } %x, 0
  %a = extractvalue { i64, i8* } %x, 1
  %b = icmp ult i64 %c1, 4611686018427387904
  br i1 %b, label %then, label %ctd_if

then:                                             ; preds = %start
  %ca = shl i64 %c1, 1
  %cok = icmp slt i64 %ca, %c
  %ca.c = select i1 %cok, i64 %c, i64 %ca
  br label %ctd_if

ctd_if:                                           ; preds = %start, %then
  %ca1 = phi i64 [ %ca.c, %then ], [ %c, %start ]
  %tmpa = icmp eq i64 %ca1, 0
  br i1 %tmpa, label %ctd_ifb, label %elseb

elseb:                                            ; preds = %ctd_if
  %e = tail call i8* @isabelle_llvm_calloc(i64 %ca1, i64 1)
  br label %ctd_ifb

ctd_ifb:                                          ; preds = %ctd_if, %elseb
  %a1 = phi i8* [ %e, %elseb ], [ null, %ctd_if ]
  %x2.i = icmp eq i64 %l, 0
  br i1 %x2.i, label %LLVM_DS_Array_arraycpy.exit, label %while_body.lr.ph.i

while_body.lr.ph.i:                               ; preds = %ctd_ifb
  %min.iters.check = icmp ult i64 %l, 32
  br i1 %min.iters.check, label %while_body.i.preheader, label %vector.memcheck

vector.memcheck:                                  ; preds = %while_body.lr.ph.i
  %scevgep = getelementptr i8, i8* %a1, i64 %l
  %scevgep2 = getelementptr i8, i8* %a, i64 %l
  %bound0 = icmp ult i8* %a1, %scevgep2
  %bound1 = icmp ult i8* %a, %scevgep
  %memcheck.conflict = and i1 %bound0, %bound1
  br i1 %memcheck.conflict, label %while_body.i.preheader, label %vector.ph

vector.ph:                                        ; preds = %vector.memcheck
  %n.vec = and i64 %l, -32
  br label %vector.body

vector.body:                                      ; preds = %vector.body, %vector.ph
  %index = phi i64 [ 0, %vector.ph ], [ %index.next, %vector.body ]
  %0 = getelementptr i8, i8* %a, i64 %index
  %1 = bitcast i8* %0 to <16 x i8>*
  %wide.load = load <16 x i8>, <16 x i8>* %1, align 1, !alias.scope !15
  %2 = getelementptr i8, i8* %0, i64 16
  %3 = bitcast i8* %2 to <16 x i8>*
  %wide.load4 = load <16 x i8>, <16 x i8>* %3, align 1, !alias.scope !15
  %4 = getelementptr i8, i8* %a1, i64 %index
  %5 = bitcast i8* %4 to <16 x i8>*
  store <16 x i8> %wide.load, <16 x i8>* %5, align 1, !alias.scope !18, !noalias !15
  %6 = getelementptr i8, i8* %4, i64 16
  %7 = bitcast i8* %6 to <16 x i8>*
  store <16 x i8> %wide.load4, <16 x i8>* %7, align 1, !alias.scope !18, !noalias !15
  %index.next = add i64 %index, 32
  %8 = icmp eq i64 %index.next, %n.vec
  br i1 %8, label %middle.block, label %vector.body, !llvm.loop !20

middle.block:                                     ; preds = %vector.body
  %cmp.n = icmp eq i64 %l, %n.vec
  br i1 %cmp.n, label %else.i, label %while_body.i.preheader

while_body.i.preheader:                           ; preds = %middle.block, %vector.memcheck, %while_body.lr.ph.i
  %i3.i.ph = phi i64 [ 0, %vector.memcheck ], [ 0, %while_body.lr.ph.i ], [ %n.vec, %middle.block ]
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %while_body.i
  %i3.i = phi i64 [ %x1.i, %while_body.i ], [ %i3.i.ph, %while_body.i.preheader ]
  %xa.i = getelementptr i8, i8* %a, i64 %i3.i
  %xaa.i = load i8, i8* %xa.i, align 1
  %p.i = getelementptr i8, i8* %a1, i64 %i3.i
  store i8 %xaa.i, i8* %p.i, align 1
  %x1.i = add nuw i64 %i3.i, 1
  %exitcond.i = icmp eq i64 %x1.i, %l
  br i1 %exitcond.i, label %else.i, label %while_body.i, !llvm.loop !21

LLVM_DS_Array_arraycpy.exit:                      ; preds = %ctd_ifb
  %tmp.i = icmp eq i8* %a, null
  br i1 %tmp.i, label %LLVM_DS_NArray_narray_free.exit, label %else.i

else.i:                                           ; preds = %while_body.i, %middle.block, %LLVM_DS_Array_arraycpy.exit
  tail call void @isabelle_llvm_free(i8* nonnull %a)
  br label %LLVM_DS_NArray_narray_free.exit

LLVM_DS_NArray_narray_free.exit:                  ; preds = %LLVM_DS_Array_arraycpy.exit, %else.i
  %xaa = insertvalue { i64, { i64, i8* } } zeroinitializer, i64 %l, 0
  %xe = insertvalue { i64, i8* } zeroinitializer, i64 %ca1, 0
  %x3 = insertvalue { i64, i8* } %xe, i8* %a1, 1
  %x4 = insertvalue { i64, { i64, i8* } } %xaa, { i64, i8* } %x3, 1
  ret { i64, { i64, i8* } } %x4
}

; Function Attrs: norecurse nounwind
define i64* @Proto_IICF_EOArray_swap_eo_impl(i64* returned %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %x3 = getelementptr i64, i64* %x, i64 %x1
  %r = load i64, i64* %x3, align 8
  %xc = getelementptr i64, i64* %x, i64 %x2
  %ra = load i64, i64* %xc, align 8
  store i64 %ra, i64* %x3, align 8
  store i64 %r, i64* %xc, align 8
  ret i64* %x
}

; Function Attrs: norecurse nounwind
define { i64, { i64, i8* } }* @Proto_IICF_EOArray_swap_eo_impl1({ i64, { i64, i8* } }* returned %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %r.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x1, i32 0
  %0 = bitcast i64* %r.elt to <2 x i64>*
  %1 = load <2 x i64>, <2 x i64>* %0, align 8
  %r.unpack2.elt4 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x1, i32 1, i32 1
  %2 = bitcast i8** %r.unpack2.elt4 to i64*
  %r.unpack2.unpack522 = load i64, i64* %2, align 8
  %ra.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x2, i32 0
  %3 = bitcast i64* %ra.elt to <2 x i64>*
  %4 = load <2 x i64>, <2 x i64>* %3, align 8
  %ra.unpack8.elt10 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x2, i32 1, i32 1
  %5 = bitcast i8** %ra.unpack8.elt10 to i64*
  %ra.unpack8.unpack1117 = load i64, i64* %5, align 8
  %6 = bitcast i64* %r.elt to <2 x i64>*
  store <2 x i64> %4, <2 x i64>* %6, align 8
  store i64 %ra.unpack8.unpack1117, i64* %2, align 8
  %7 = bitcast i64* %ra.elt to <2 x i64>*
  store <2 x i64> %1, <2 x i64>* %7, align 8
  store i64 %r.unpack2.unpack522, i64* %5, align 8
  ret { i64, { i64, i8* } }* %x
}

; Function Attrs: norecurse nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_heapsort_impl({ i64, { i64, i8* } }* %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %x3 = sub i64 %x2, %x1
  %xa = icmp sgt i64 %x3, 1
  br i1 %xa, label %then, label %ctd_if

then:                                             ; preds = %start
  %xa.i = add i64 %x2, -1
  %x41.i = icmp sgt i64 %xa.i, %x1
  br i1 %x41.i, label %while_body.i.preheader, label %Sorting_Introsort_str_sort_heapify_btu_impl.exit

while_body.i.preheader:                           ; preds = %then
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %while_body.i
  %a113.i = phi { i64, { i64, i8* } }* [ %xca.i, %while_body.i ], [ %x, %while_body.i.preheader ]
  %x32.i = phi i64 [ %xba.i, %while_body.i ], [ %xa.i, %while_body.i.preheader ]
  %xba.i = add i64 %x32.i, -1
  %xca.i = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_sift_down_impl(i64 %x1, i64 %x2, i64 %xba.i, { i64, { i64, i8* } }* %a113.i) #3
  %x4.i = icmp sgt i64 %xba.i, %x1
  br i1 %x4.i, label %while_body.i, label %Sorting_Introsort_str_sort_heapify_btu_impl.exit

Sorting_Introsort_str_sort_heapify_btu_impl.exit: ; preds = %while_body.i, %then
  %a11.lcssa.i = phi { i64, { i64, i8* } }* [ %x, %then ], [ %xca.i, %while_body.i ]
  %xda = add i64 %x1, 1
  %x41 = icmp slt i64 %xda, %x2
  br i1 %x41, label %while_body.preheader, label %ctd_if

while_body.preheader:                             ; preds = %Sorting_Introsort_str_sort_heapify_btu_impl.exit
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %a113 = phi { i64, { i64, i8* } }* [ %xg, %while_body ], [ %a11.lcssa.i, %while_body.preheader ]
  %a22 = phi i64 [ %xda1, %while_body ], [ %x2, %while_body.preheader ]
  %xda1 = add nsw i64 %a22, -1
  %r.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113, i64 %x1, i32 0
  %0 = bitcast i64* %r.elt.i to <2 x i64>*
  %1 = load <2 x i64>, <2 x i64>* %0, align 8
  %r.unpack2.elt4.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113, i64 %x1, i32 1, i32 1
  %2 = bitcast i8** %r.unpack2.elt4.i to i64*
  %r.unpack2.unpack522.i = load i64, i64* %2, align 8
  %ra.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113, i64 %xda1, i32 0
  %3 = bitcast i64* %ra.elt.i to <2 x i64>*
  %4 = load <2 x i64>, <2 x i64>* %3, align 8
  %ra.unpack8.elt10.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113, i64 %xda1, i32 1, i32 1
  %5 = bitcast i8** %ra.unpack8.elt10.i to i64*
  %ra.unpack8.unpack1117.i = load i64, i64* %5, align 8
  %6 = bitcast i64* %r.elt.i to <2 x i64>*
  store <2 x i64> %4, <2 x i64>* %6, align 8
  store i64 %ra.unpack8.unpack1117.i, i64* %2, align 8
  %7 = bitcast i64* %ra.elt.i to <2 x i64>*
  store <2 x i64> %1, <2 x i64>* %7, align 8
  store i64 %r.unpack2.unpack522.i, i64* %5, align 8
  %xg = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_sift_down_impl(i64 %x1, i64 %xda1, i64 %x1, { i64, { i64, i8* } }* %a113)
  %x4 = icmp slt i64 %xda, %xda1
  br i1 %x4, label %while_body, label %ctd_if

ctd_if:                                           ; preds = %while_body, %Sorting_Introsort_str_sort_heapify_btu_impl.exit, %start
  %x6 = phi { i64, { i64, i8* } }* [ %x, %start ], [ %a11.lcssa.i, %Sorting_Introsort_str_sort_heapify_btu_impl.exit ], [ %xg, %while_body ]
  ret { i64, { i64, i8* } }* %x6
}

; Function Attrs: nounwind
define { i64, { i64, i8* } }* @str_introsort({ i64, { i64, i8* } }* %x, i64 %x1, i64 %x2) local_unnamed_addr #3 {
start:
  %x3 = sub i64 %x2, %x1
  %xa = icmp sgt i64 %x3, 1
  br i1 %xa, label %while_body.i.i.preheader, label %ctd_if

while_body.i.i.preheader:                         ; preds = %start
  br label %while_body.i.i

while_body.i.i:                                   ; preds = %while_body.i.i.preheader, %while_body.i.i
  %a114.i.i = phi i64 [ %xaa.i.i, %while_body.i.i ], [ 0, %while_body.i.i.preheader ]
  %x23.i.i = phi i64 [ %xba.i.i, %while_body.i.i ], [ %x3, %while_body.i.i.preheader ]
  %xaa.i.i = add nuw nsw i64 %a114.i.i, 1
  %xba.i.i = shl i64 %x23.i.i, 1
  %x3.i.i = icmp sgt i64 %xba.i.i, 0
  br i1 %x3.i.i, label %while_body.i.i, label %Sorting_Log2_word_clz_impl.exit

Sorting_Log2_word_clz_impl.exit:                  ; preds = %while_body.i.i
  %xe = shl nuw i64 %xaa.i.i, 1
  %xf = sub i64 126, %xe
  %x4.i = insertvalue { i64, i64 } zeroinitializer, i64 %x2, 0
  %tmpa.i = insertvalue { i64, i64 } %x4.i, i64 %xf, 1
  %xa.i = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %x1, 0
  %tmpab.i = insertvalue { i64, { i64, i64 } } %xa.i, { i64, i64 } %tmpa.i, 1
  %xb.i = insertvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } zeroinitializer, { i64, { i64, i8* } }* %x, 0
  %x5.i = insertvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %xb.i, { i64, { i64, i64 } } %tmpab.i, 1
  %x6.i = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_introsort_qs_aux_impl_f_04889284({ { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %x5.i) #3
  %x41.i = icmp sgt i64 %x2, %x1
  br i1 %x41.i, label %while_body.i.preheader, label %ctd_if

while_body.i.preheader:                           ; preds = %Sorting_Log2_word_clz_impl.exit
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %while_body.i
  %a113.i = phi { i64, { i64, i8* } }* [ %xaa.i, %while_body.i ], [ %x6.i, %while_body.i.preheader ]
  %a22.i = phi i64 [ %xba.i, %while_body.i ], [ %x1, %while_body.i.preheader ]
  %xaa.i = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_is_insert_impl({ i64, { i64, i8* } }* %a113.i, i64 %x1, i64 %a22.i) #3
  %xba.i = add nsw i64 %a22.i, 1
  %exitcond.i = icmp eq i64 %xba.i, %x2
  br i1 %exitcond.i, label %ctd_if, label %while_body.i

ctd_if:                                           ; preds = %while_body.i, %Sorting_Log2_word_clz_impl.exit, %start
  %x5 = phi { i64, { i64, i8* } }* [ %x, %start ], [ %x6.i, %Sorting_Log2_word_clz_impl.exit ], [ %xaa.i, %while_body.i ]
  ret { i64, { i64, i8* } }* %x5
}

; Function Attrs: norecurse nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_is_insert_impl({ i64, { i64, i8* } }* %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %r.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x2, i32 0
  %r.unpack = load i64, i64* %r.elt, align 8
  %r.unpack2.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x2, i32 1, i32 0
  %r.unpack2.unpack = load i64, i64* %r.unpack2.elt, align 8
  %r.unpack2.elt4 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %x2, i32 1, i32 1
  %r.unpack2.unpack5 = load i8*, i8** %r.unpack2.elt4, align 8
  %xda33 = icmp sgt i64 %x2, %x1
  br i1 %xda33, label %then.preheader, label %while_end

then.preheader:                                   ; preds = %start
  br label %then

then:                                             ; preds = %then.preheader, %while_body
  %a2a36 = phi i64 [ %bib, %while_body ], [ %x2, %then.preheader ]
  %bib = add nsw i64 %a2a36, -1
  %ra.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %bib, i32 0
  %0 = bitcast i64* %ra.elt to <2 x i64>*
  %1 = load <2 x i64>, <2 x i64>* %0, align 8
  %ra.unpack23.elt25 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %bib, i32 1, i32 1
  %ra.unpack23.unpack26 = load i8*, i8** %ra.unpack23.elt25, align 8
  %2 = extractelement <2 x i64> %1, i32 0
  %xd.i = icmp sgt i64 %r.unpack, %2
  %la.l.i = select i1 %xd.i, i64 %2, i64 %r.unpack
  %xga1.i = icmp sgt i64 %la.l.i, 0
  %3 = ptrtoint i8* %ra.unpack23.unpack26 to i64
  br i1 %xga1.i, label %while_body.i.preheader, label %Sorting_Strings_strcmp_impl.exit

while_body.i.preheader:                           ; preds = %then
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %ctd_ifa.i
  %a12.i = phi i64 [ %a1.i, %ctd_ifa.i ], [ 0, %while_body.i.preheader ]
  %xh.i = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i
  %xi.i = load i8, i8* %xh.i, align 1
  %xk.i = getelementptr i8, i8* %ra.unpack23.unpack26, i64 %a12.i
  %xl.i = load i8, i8* %xk.i, align 1
  %xm.i = icmp eq i8 %xi.i, %xl.i
  br i1 %xm.i, label %thena.i, label %elsea.i

thena.i:                                          ; preds = %while_body.i
  %xna.i = add i64 %a12.i, 1
  %xo.i = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i, 0
  %x5.i = insertvalue { i64, i2 } %xo.i, i2 0, 1
  br label %ctd_ifa.i

elsea.i:                                          ; preds = %while_body.i
  %xn.i = icmp ult i8 %xi.i, %xl.i
  %xoa.i = add i64 %a12.i, 1
  %xp.i = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i, 0
  %x7.i = insertvalue { i64, i2 } %xp.i, i2 1, 1
  %x6.i = insertvalue { i64, i2 } %xp.i, i2 -1, 1
  %x8.i = select i1 %xn.i, { i64, i2 } %x6.i, { i64, i2 } %x7.i
  br label %ctd_ifa.i

ctd_ifa.i:                                        ; preds = %elsea.i, %thena.i
  %x9.i = phi { i64, i2 } [ %x5.i, %thena.i ], [ %x8.i, %elsea.i ]
  %a1.i = extractvalue { i64, i2 } %x9.i, 0
  %a2.i = extractvalue { i64, i2 } %x9.i, 1
  %xga.i = icmp slt i64 %a1.i, %la.l.i
  %x3.i = icmp eq i2 %a2.i, 0
  %x4.i = and i1 %xga.i, %x3.i
  br i1 %x4.i, label %while_body.i, label %while_end.i

while_end.i:                                      ; preds = %ctd_ifa.i
  switch i2 %a2.i, label %while_end.loopexit [
    i2 -1, label %while_body
    i2 0, label %Sorting_Strings_strcmp_impl.exit
  ]

Sorting_Strings_strcmp_impl.exit:                 ; preds = %then, %while_end.i
  %x10.i = icmp slt i64 %r.unpack, %2
  br i1 %x10.i, label %while_body, label %while_end.loopexit

while_body:                                       ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  %p1.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %a2a36, i32 0
  %4 = bitcast i64* %p1.repack to <2 x i64>*
  store <2 x i64> %1, <2 x i64>* %4, align 8
  %p1.repack17.repack19 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %a2a36, i32 1, i32 1
  %5 = bitcast i8** %p1.repack17.repack19 to i64*
  store i64 %3, i64* %5, align 8
  %xda = icmp sgt i64 %bib, %x1
  br i1 %xda, label %then, label %while_end.loopexit

while_end.loopexit:                               ; preds = %while_end.i, %while_body, %Sorting_Strings_strcmp_impl.exit
  %a2a.lcssa.ph = phi i64 [ %a2a36, %Sorting_Strings_strcmp_impl.exit ], [ %bib, %while_body ], [ %a2a36, %while_end.i ]
  %.pre = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %a2a.lcssa.ph, i32 0
  %.pre43 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %a2a.lcssa.ph, i32 1, i32 0
  %.pre44 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x, i64 %a2a.lcssa.ph, i32 1, i32 1
  br label %while_end

while_end:                                        ; preds = %while_end.loopexit, %start
  %p2.repack7.repack9.pre-phi = phi i8** [ %.pre44, %while_end.loopexit ], [ %r.unpack2.elt4, %start ]
  %p2.repack7.repack.pre-phi = phi i64* [ %.pre43, %while_end.loopexit ], [ %r.unpack2.elt, %start ]
  %p2.repack.pre-phi = phi i64* [ %.pre, %while_end.loopexit ], [ %r.elt, %start ]
  store i64 %r.unpack, i64* %p2.repack.pre-phi, align 8
  store i64 %r.unpack2.unpack, i64* %p2.repack7.repack.pre-phi, align 8
  store i8* %r.unpack2.unpack5, i8** %p2.repack7.repack9.pre-phi, align 8
  ret { i64, { i64, i8* } }* %x
}

; Function Attrs: norecurse nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_sift_down_impl(i64 %x, i64 %x1, i64 %x2, { i64, { i64, i8* } }* %x3) local_unnamed_addr #0 {
start:
  %x4 = sub i64 %x2, %x
  %r.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x2, i32 0
  %r.unpack = load i64, i64* %r.elt, align 8
  %r.unpack2.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x2, i32 1, i32 0
  %r.unpack2.unpack = load i64, i64* %r.unpack2.elt, align 8
  %r.unpack2.elt4 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x2, i32 1, i32 1
  %r.unpack2.unpack5 = load i8*, i8** %r.unpack2.elt4, align 8
  %xga = sub i64 %x1, %x
  %xha = add i64 %xga, -1
  %xia = lshr i64 %xha, 1
  %xj203 = icmp slt i64 %x4, %xia
  br i1 %xj203, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %ctd_if
  %a1b204 = phi i64 [ %xha1.sink, %ctd_if ], [ %x4, %while_body.preheader ]
  %xga1 = shl i64 %a1b204, 1
  %xha1 = or i64 %xga1, 1
  %xja = add i64 %xga1, 2
  %xk = add i64 %xha1, %x
  %xl = add i64 %xja, %x
  %ra.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xk, i32 0
  %0 = bitcast i64* %ra.elt to <2 x i64>*
  %1 = load <2 x i64>, <2 x i64>* %0, align 8
  %ra.unpack35.elt37 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xk, i32 1, i32 1
  %ra.unpack35.unpack38 = load i8*, i8** %ra.unpack35.elt37, align 8
  %rb.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xl, i32 0
  %2 = bitcast i64* %rb.elt to <2 x i64>*
  %3 = load <2 x i64>, <2 x i64>* %2, align 8
  %rb.unpack41.elt43 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xl, i32 1, i32 1
  %rb.unpack41.unpack44 = load i8*, i8** %rb.unpack41.elt43, align 8
  %4 = extractelement <2 x i64> %1, i32 0
  %5 = extractelement <2 x i64> %3, i32 0
  %xd.i = icmp sgt i64 %4, %5
  %la.l.i = select i1 %xd.i, i64 %5, i64 %4
  %xga1.i = icmp sgt i64 %la.l.i, 0
  br i1 %xga1.i, label %while_body.i.preheader, label %Sorting_Strings_strcmp_impl.exit

while_body.i.preheader:                           ; preds = %while_body
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %ctd_ifa.i
  %a12.i = phi i64 [ %a1.i, %ctd_ifa.i ], [ 0, %while_body.i.preheader ]
  %xh.i = getelementptr i8, i8* %ra.unpack35.unpack38, i64 %a12.i
  %xi.i = load i8, i8* %xh.i, align 1
  %xk.i = getelementptr i8, i8* %rb.unpack41.unpack44, i64 %a12.i
  %xl.i = load i8, i8* %xk.i, align 1
  %xm.i = icmp eq i8 %xi.i, %xl.i
  br i1 %xm.i, label %thena.i, label %elsea.i

thena.i:                                          ; preds = %while_body.i
  %xna.i = add i64 %a12.i, 1
  %xo.i = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i, 0
  %x5.i = insertvalue { i64, i2 } %xo.i, i2 0, 1
  br label %ctd_ifa.i

elsea.i:                                          ; preds = %while_body.i
  %xn.i = icmp ult i8 %xi.i, %xl.i
  %xoa.i = add i64 %a12.i, 1
  %xp.i = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i, 0
  %x7.i = insertvalue { i64, i2 } %xp.i, i2 1, 1
  %x6.i = insertvalue { i64, i2 } %xp.i, i2 -1, 1
  %x8.i = select i1 %xn.i, { i64, i2 } %x6.i, { i64, i2 } %x7.i
  br label %ctd_ifa.i

ctd_ifa.i:                                        ; preds = %elsea.i, %thena.i
  %x9.i = phi { i64, i2 } [ %x5.i, %thena.i ], [ %x8.i, %elsea.i ]
  %a1.i = extractvalue { i64, i2 } %x9.i, 0
  %a2.i = extractvalue { i64, i2 } %x9.i, 1
  %xga.i = icmp slt i64 %a1.i, %la.l.i
  %x3.i = icmp eq i2 %a2.i, 0
  %x4.i = and i1 %xga.i, %x3.i
  br i1 %x4.i, label %while_body.i, label %while_end.i

while_end.i:                                      ; preds = %ctd_ifa.i
  switch i2 %a2.i, label %else [
    i2 -1, label %then
    i2 0, label %Sorting_Strings_strcmp_impl.exit
  ]

Sorting_Strings_strcmp_impl.exit:                 ; preds = %while_body, %while_end.i
  %x10.i = icmp slt i64 %4, %5
  br i1 %x10.i, label %then, label %else

then:                                             ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  %xd.i150 = icmp sgt i64 %r.unpack, %5
  %la.l.i151 = select i1 %xd.i150, i64 %5, i64 %r.unpack
  %xga1.i152 = icmp sgt i64 %la.l.i151, 0
  br i1 %xga1.i152, label %while_body.i160.preheader, label %Sorting_Strings_strcmp_impl.exit185

while_body.i160.preheader:                        ; preds = %then
  br label %while_body.i160

while_body.i160:                                  ; preds = %while_body.i160.preheader, %ctd_ifa.i178
  %a12.i154 = phi i64 [ %a1.i173, %ctd_ifa.i178 ], [ 0, %while_body.i160.preheader ]
  %xh.i155 = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i154
  %xi.i156 = load i8, i8* %xh.i155, align 1
  %xk.i157 = getelementptr i8, i8* %rb.unpack41.unpack44, i64 %a12.i154
  %xl.i158 = load i8, i8* %xk.i157, align 1
  %xm.i159 = icmp eq i8 %xi.i156, %xl.i158
  br i1 %xm.i159, label %thena.i164, label %elsea.i171

thena.i164:                                       ; preds = %while_body.i160
  %xna.i161 = add i64 %a12.i154, 1
  %xo.i162 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i161, 0
  %x5.i163 = insertvalue { i64, i2 } %xo.i162, i2 0, 1
  br label %ctd_ifa.i178

elsea.i171:                                       ; preds = %while_body.i160
  %xn.i165 = icmp ult i8 %xi.i156, %xl.i158
  %xoa.i166 = add i64 %a12.i154, 1
  %xp.i167 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i166, 0
  %x7.i168 = insertvalue { i64, i2 } %xp.i167, i2 1, 1
  %x6.i169 = insertvalue { i64, i2 } %xp.i167, i2 -1, 1
  %x8.i170 = select i1 %xn.i165, { i64, i2 } %x6.i169, { i64, i2 } %x7.i168
  br label %ctd_ifa.i178

ctd_ifa.i178:                                     ; preds = %elsea.i171, %thena.i164
  %x9.i172 = phi { i64, i2 } [ %x5.i163, %thena.i164 ], [ %x8.i170, %elsea.i171 ]
  %a1.i173 = extractvalue { i64, i2 } %x9.i172, 0
  %a2.i174 = extractvalue { i64, i2 } %x9.i172, 1
  %xga.i175 = icmp slt i64 %a1.i173, %la.l.i151
  %x3.i176 = icmp eq i2 %a2.i174, 0
  %x4.i177 = and i1 %xga.i175, %x3.i176
  br i1 %x4.i177, label %while_body.i160, label %while_end.i179

while_end.i179:                                   ; preds = %ctd_ifa.i178
  switch i2 %a2.i174, label %ctd_if [
    i2 -1, label %thena
    i2 0, label %Sorting_Strings_strcmp_impl.exit185
  ]

Sorting_Strings_strcmp_impl.exit185:              ; preds = %then, %while_end.i179
  %x10.i180 = icmp slt i64 %r.unpack, %5
  br i1 %x10.i180, label %thena, label %ctd_if

thena:                                            ; preds = %while_end.i179, %Sorting_Strings_strcmp_impl.exit185
  %yh = add i64 %a1b204, %x
  %pc.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %yh, i32 0
  %6 = bitcast i64* %pc.repack to <2 x i64>*
  store <2 x i64> %3, <2 x i64>* %6, align 8
  %pc.repack74.repack76 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %yh, i32 1, i32 1
  store i8* %rb.unpack41.unpack44, i8** %pc.repack74.repack76, align 8
  br label %ctd_if

else:                                             ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  %xd.i114 = icmp sgt i64 %r.unpack, %4
  %la.l.i115 = select i1 %xd.i114, i64 %4, i64 %r.unpack
  %xga1.i116 = icmp sgt i64 %la.l.i115, 0
  br i1 %xga1.i116, label %while_body.i124.preheader, label %Sorting_Strings_strcmp_impl.exit149

while_body.i124.preheader:                        ; preds = %else
  br label %while_body.i124

while_body.i124:                                  ; preds = %while_body.i124.preheader, %ctd_ifa.i142
  %a12.i118 = phi i64 [ %a1.i137, %ctd_ifa.i142 ], [ 0, %while_body.i124.preheader ]
  %xh.i119 = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i118
  %xi.i120 = load i8, i8* %xh.i119, align 1
  %xk.i121 = getelementptr i8, i8* %ra.unpack35.unpack38, i64 %a12.i118
  %xl.i122 = load i8, i8* %xk.i121, align 1
  %xm.i123 = icmp eq i8 %xi.i120, %xl.i122
  br i1 %xm.i123, label %thena.i128, label %elsea.i135

thena.i128:                                       ; preds = %while_body.i124
  %xna.i125 = add i64 %a12.i118, 1
  %xo.i126 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i125, 0
  %x5.i127 = insertvalue { i64, i2 } %xo.i126, i2 0, 1
  br label %ctd_ifa.i142

elsea.i135:                                       ; preds = %while_body.i124
  %xn.i129 = icmp ult i8 %xi.i120, %xl.i122
  %xoa.i130 = add i64 %a12.i118, 1
  %xp.i131 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i130, 0
  %x7.i132 = insertvalue { i64, i2 } %xp.i131, i2 1, 1
  %x6.i133 = insertvalue { i64, i2 } %xp.i131, i2 -1, 1
  %x8.i134 = select i1 %xn.i129, { i64, i2 } %x6.i133, { i64, i2 } %x7.i132
  br label %ctd_ifa.i142

ctd_ifa.i142:                                     ; preds = %elsea.i135, %thena.i128
  %x9.i136 = phi { i64, i2 } [ %x5.i127, %thena.i128 ], [ %x8.i134, %elsea.i135 ]
  %a1.i137 = extractvalue { i64, i2 } %x9.i136, 0
  %a2.i138 = extractvalue { i64, i2 } %x9.i136, 1
  %xga.i139 = icmp slt i64 %a1.i137, %la.l.i115
  %x3.i140 = icmp eq i2 %a2.i138, 0
  %x4.i141 = and i1 %xga.i139, %x3.i140
  br i1 %x4.i141, label %while_body.i124, label %while_end.i143

while_end.i143:                                   ; preds = %ctd_ifa.i142
  switch i2 %a2.i138, label %ctd_if [
    i2 -1, label %thenb
    i2 0, label %Sorting_Strings_strcmp_impl.exit149
  ]

Sorting_Strings_strcmp_impl.exit149:              ; preds = %else, %while_end.i143
  %x10.i144 = icmp slt i64 %r.unpack, %4
  br i1 %x10.i144, label %thenb, label %ctd_if

thenb:                                            ; preds = %while_end.i143, %Sorting_Strings_strcmp_impl.exit149
  %yh1 = add i64 %a1b204, %x
  %pc1.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %yh1, i32 0
  %7 = bitcast i64* %pc1.repack to <2 x i64>*
  store <2 x i64> %1, <2 x i64>* %7, align 8
  %pc1.repack65.repack67 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %yh1, i32 1, i32 1
  store i8* %ra.unpack35.unpack38, i8** %pc1.repack65.repack67, align 8
  br label %ctd_if

ctd_if:                                           ; preds = %Sorting_Strings_strcmp_impl.exit149, %while_end.i143, %Sorting_Strings_strcmp_impl.exit185, %while_end.i179, %thenb, %thena
  %xha1.sink = phi i64 [ %xha1, %thenb ], [ %xja, %thena ], [ %a1b204, %while_end.i179 ], [ %a1b204, %Sorting_Strings_strcmp_impl.exit185 ], [ %a1b204, %while_end.i143 ], [ %a1b204, %Sorting_Strings_strcmp_impl.exit149 ]
  %.sink = phi i1 [ true, %thenb ], [ true, %thena ], [ false, %while_end.i179 ], [ false, %Sorting_Strings_strcmp_impl.exit185 ], [ false, %while_end.i143 ], [ false, %Sorting_Strings_strcmp_impl.exit149 ]
  %xj = icmp slt i64 %xha1.sink, %xia
  %x5 = and i1 %.sink, %xj
  br i1 %x5, label %while_body, label %while_end

while_end:                                        ; preds = %ctd_if, %start
  %a1b.lcssa = phi i64 [ %x4, %start ], [ %xha1.sink, %ctd_if ]
  %xha2 = lshr i64 %xga, 1
  %xi1 = icmp slt i64 %a1b.lcssa, %xha2
  br i1 %xi1, label %thenc, label %elsec

thenc:                                            ; preds = %while_end
  %xj1 = shl i64 %a1b.lcssa, 1
  %xka = or i64 %xj1, 1
  %xl1 = add i64 %xka, %x
  %ra1.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xl1, i32 0
  %ra1.unpack = load i64, i64* %ra1.elt, align 8
  %ra1.unpack12.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xl1, i32 1, i32 0
  %ra1.unpack12.unpack = load i64, i64* %ra1.unpack12.elt, align 8
  %ra1.unpack12.elt14 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xl1, i32 1, i32 1
  %ra1.unpack12.unpack15 = load i8*, i8** %ra1.unpack12.elt14, align 8
  %xd.i78 = icmp sgt i64 %r.unpack, %ra1.unpack
  %la.l.i79 = select i1 %xd.i78, i64 %ra1.unpack, i64 %r.unpack
  %xga1.i80 = icmp sgt i64 %la.l.i79, 0
  br i1 %xga1.i80, label %while_body.i88.preheader, label %Sorting_Strings_strcmp_impl.exit113

while_body.i88.preheader:                         ; preds = %thenc
  br label %while_body.i88

while_body.i88:                                   ; preds = %while_body.i88.preheader, %ctd_ifa.i106
  %a12.i82 = phi i64 [ %a1.i101, %ctd_ifa.i106 ], [ 0, %while_body.i88.preheader ]
  %xh.i83 = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i82
  %xi.i84 = load i8, i8* %xh.i83, align 1
  %xk.i85 = getelementptr i8, i8* %ra1.unpack12.unpack15, i64 %a12.i82
  %xl.i86 = load i8, i8* %xk.i85, align 1
  %xm.i87 = icmp eq i8 %xi.i84, %xl.i86
  br i1 %xm.i87, label %thena.i92, label %elsea.i99

thena.i92:                                        ; preds = %while_body.i88
  %xna.i89 = add i64 %a12.i82, 1
  %xo.i90 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i89, 0
  %x5.i91 = insertvalue { i64, i2 } %xo.i90, i2 0, 1
  br label %ctd_ifa.i106

elsea.i99:                                        ; preds = %while_body.i88
  %xn.i93 = icmp ult i8 %xi.i84, %xl.i86
  %xoa.i94 = add i64 %a12.i82, 1
  %xp.i95 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i94, 0
  %x7.i96 = insertvalue { i64, i2 } %xp.i95, i2 1, 1
  %x6.i97 = insertvalue { i64, i2 } %xp.i95, i2 -1, 1
  %x8.i98 = select i1 %xn.i93, { i64, i2 } %x6.i97, { i64, i2 } %x7.i96
  br label %ctd_ifa.i106

ctd_ifa.i106:                                     ; preds = %elsea.i99, %thena.i92
  %x9.i100 = phi { i64, i2 } [ %x5.i91, %thena.i92 ], [ %x8.i98, %elsea.i99 ]
  %a1.i101 = extractvalue { i64, i2 } %x9.i100, 0
  %a2.i102 = extractvalue { i64, i2 } %x9.i100, 1
  %xga.i103 = icmp slt i64 %a1.i101, %la.l.i79
  %x3.i104 = icmp eq i2 %a2.i102, 0
  %x4.i105 = and i1 %xga.i103, %x3.i104
  br i1 %x4.i105, label %while_body.i88, label %while_end.i107

while_end.i107:                                   ; preds = %ctd_ifa.i106
  switch i2 %a2.i102, label %Sorting_Strings_strcmp_impl.exit113.thread193 [
    i2 -1, label %Sorting_Strings_strcmp_impl.exit113.thread
    i2 0, label %Sorting_Strings_strcmp_impl.exit113
  ]

Sorting_Strings_strcmp_impl.exit113.thread193:    ; preds = %while_end.i107
  %xw2194 = add i64 %a1b.lcssa, %x
  %pa1.repack195 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2194, i32 0
  br label %elsed

Sorting_Strings_strcmp_impl.exit113.thread:       ; preds = %while_end.i107
  %xw2189 = add i64 %a1b.lcssa, %x
  %pa1.repack190 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2189, i32 0
  br label %thend

Sorting_Strings_strcmp_impl.exit113:              ; preds = %thenc, %while_end.i107
  %x10.i108 = icmp slt i64 %r.unpack, %ra1.unpack
  %xw2 = add i64 %a1b.lcssa, %x
  %pa1.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2, i32 0
  br i1 %x10.i108, label %thend, label %elsed

thend:                                            ; preds = %Sorting_Strings_strcmp_impl.exit113.thread, %Sorting_Strings_strcmp_impl.exit113
  %pa1.repack192 = phi i64* [ %pa1.repack190, %Sorting_Strings_strcmp_impl.exit113.thread ], [ %pa1.repack, %Sorting_Strings_strcmp_impl.exit113 ]
  %xw2191 = phi i64 [ %xw2189, %Sorting_Strings_strcmp_impl.exit113.thread ], [ %xw2, %Sorting_Strings_strcmp_impl.exit113 ]
  store i64 %ra1.unpack, i64* %pa1.repack192, align 8
  %pa1.repack25.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2191, i32 1, i32 0
  store i64 %ra1.unpack12.unpack, i64* %pa1.repack25.repack, align 8
  %pa1.repack25.repack27 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2191, i32 1, i32 1
  store i8* %ra1.unpack12.unpack15, i8** %pa1.repack25.repack27, align 8
  store i64 %r.unpack, i64* %ra1.elt, align 8
  store i64 %r.unpack2.unpack, i64* %ra1.unpack12.elt, align 8
  br label %ctd_ifc

elsed:                                            ; preds = %Sorting_Strings_strcmp_impl.exit113.thread193, %Sorting_Strings_strcmp_impl.exit113
  %pa1.repack197 = phi i64* [ %pa1.repack195, %Sorting_Strings_strcmp_impl.exit113.thread193 ], [ %pa1.repack, %Sorting_Strings_strcmp_impl.exit113 ]
  %xw2196 = phi i64 [ %xw2194, %Sorting_Strings_strcmp_impl.exit113.thread193 ], [ %xw2, %Sorting_Strings_strcmp_impl.exit113 ]
  store i64 %r.unpack, i64* %pa1.repack197, align 8
  %pa2.repack21.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2196, i32 1, i32 0
  store i64 %r.unpack2.unpack, i64* %pa2.repack21.repack, align 8
  %pa2.repack21.repack23 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xw2196, i32 1, i32 1
  br label %ctd_ifc

elsec:                                            ; preds = %while_end
  %xj2 = add i64 %a1b.lcssa, %x
  %p2.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xj2, i32 0
  store i64 %r.unpack, i64* %p2.repack, align 8
  %p2.repack7.repack = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xj2, i32 1, i32 0
  store i64 %r.unpack2.unpack, i64* %p2.repack7.repack, align 8
  %p2.repack7.repack9 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %xj2, i32 1, i32 1
  br label %ctd_ifc

ctd_ifc:                                          ; preds = %thend, %elsed, %elsec
  %ra1.unpack12.elt14.sink = phi i8** [ %ra1.unpack12.elt14, %thend ], [ %pa2.repack21.repack23, %elsed ], [ %p2.repack7.repack9, %elsec ]
  store i8* %r.unpack2.unpack5, i8** %ra1.unpack12.elt14.sink, align 8
  ret { i64, { i64, i8* } }* %x3
}

; Function Attrs: norecurse nounwind
define i64* @heapsort(i64* %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %x3 = sub i64 %x2, %x1
  %xa = icmp sgt i64 %x3, 1
  br i1 %xa, label %then, label %ctd_if

then:                                             ; preds = %start
  %xa.i = add i64 %x2, -1
  %x41.i = icmp sgt i64 %xa.i, %x1
  br i1 %x41.i, label %while_body.i.preheader, label %Sorting_Introsort_unat_sort_heapify_btu_impl.exit

while_body.i.preheader:                           ; preds = %then
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %while_body.i
  %a113.i = phi i64* [ %xca.i, %while_body.i ], [ %x, %while_body.i.preheader ]
  %x32.i = phi i64 [ %xba.i, %while_body.i ], [ %xa.i, %while_body.i.preheader ]
  %xba.i = add i64 %x32.i, -1
  %xca.i = tail call i64* @Sorting_Introsort_unat_sort_sift_down_impl(i64 %x1, i64 %x2, i64 %xba.i, i64* %a113.i) #3
  %x4.i = icmp sgt i64 %xba.i, %x1
  br i1 %x4.i, label %while_body.i, label %Sorting_Introsort_unat_sort_heapify_btu_impl.exit

Sorting_Introsort_unat_sort_heapify_btu_impl.exit: ; preds = %while_body.i, %then
  %a11.lcssa.i = phi i64* [ %x, %then ], [ %xca.i, %while_body.i ]
  %xda = add i64 %x1, 1
  %x41 = icmp slt i64 %xda, %x2
  br i1 %x41, label %while_body.preheader, label %ctd_if

while_body.preheader:                             ; preds = %Sorting_Introsort_unat_sort_heapify_btu_impl.exit
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %a113 = phi i64* [ %xg, %while_body ], [ %a11.lcssa.i, %while_body.preheader ]
  %a22 = phi i64 [ %xda1, %while_body ], [ %x2, %while_body.preheader ]
  %xda1 = add nsw i64 %a22, -1
  %x3.i = getelementptr i64, i64* %a113, i64 %x1
  %r.i = load i64, i64* %x3.i, align 8
  %xc.i = getelementptr i64, i64* %a113, i64 %xda1
  %ra.i = load i64, i64* %xc.i, align 8
  store i64 %ra.i, i64* %x3.i, align 8
  store i64 %r.i, i64* %xc.i, align 8
  %xg = tail call i64* @Sorting_Introsort_unat_sort_sift_down_impl(i64 %x1, i64 %xda1, i64 %x1, i64* %a113)
  %x4 = icmp slt i64 %xda, %xda1
  br i1 %x4, label %while_body, label %ctd_if

ctd_if:                                           ; preds = %while_body, %Sorting_Introsort_unat_sort_heapify_btu_impl.exit, %start
  %x6 = phi i64* [ %x, %start ], [ %a11.lcssa.i, %Sorting_Introsort_unat_sort_heapify_btu_impl.exit ], [ %xg, %while_body ]
  ret i64* %x6
}

; Function Attrs: nounwind
define i64* @introsort(i64* %x, i64 %x1, i64 %x2) local_unnamed_addr #3 {
start:
  %x3 = sub i64 %x2, %x1
  %xa = icmp sgt i64 %x3, 1
  br i1 %xa, label %while_body.i.i.preheader, label %ctd_if

while_body.i.i.preheader:                         ; preds = %start
  br label %while_body.i.i

while_body.i.i:                                   ; preds = %while_body.i.i.preheader, %while_body.i.i
  %a114.i.i = phi i64 [ %xaa.i.i, %while_body.i.i ], [ 0, %while_body.i.i.preheader ]
  %x23.i.i = phi i64 [ %xba.i.i, %while_body.i.i ], [ %x3, %while_body.i.i.preheader ]
  %xaa.i.i = add nuw nsw i64 %a114.i.i, 1
  %xba.i.i = shl i64 %x23.i.i, 1
  %x3.i.i = icmp sgt i64 %xba.i.i, 0
  br i1 %x3.i.i, label %while_body.i.i, label %Sorting_Log2_word_clz_impl.exit

Sorting_Log2_word_clz_impl.exit:                  ; preds = %while_body.i.i
  %xe = shl nuw i64 %xaa.i.i, 1
  %xf = sub i64 126, %xe
  %x4.i = insertvalue { i64, i64 } zeroinitializer, i64 %x2, 0
  %tmpa.i = insertvalue { i64, i64 } %x4.i, i64 %xf, 1
  %xa.i = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %x1, 0
  %tmpab.i = insertvalue { i64, { i64, i64 } } %xa.i, { i64, i64 } %tmpa.i, 1
  %xb.i = insertvalue { i64*, { i64, { i64, i64 } } } zeroinitializer, i64* %x, 0
  %x5.i = insertvalue { i64*, { i64, { i64, i64 } } } %xb.i, { i64, { i64, i64 } } %tmpab.i, 1
  %x6.i = tail call i64* @Sorting_Introsort_unat_sort_introsort_qs_aux_impl_f_04869164({ i64*, { i64, { i64, i64 } } } %x5.i) #3
  %x43.i = icmp sgt i64 %x2, %x1
  br i1 %x43.i, label %while_body.i.preheader, label %ctd_if

while_body.i.preheader:                           ; preds = %Sorting_Log2_word_clz_impl.exit
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %Sorting_Introsort_unat_sort_is_insert_impl.exit.i
  %a24.i = phi i64 [ %xba.i, %Sorting_Introsort_unat_sort_is_insert_impl.exit.i ], [ %x1, %while_body.i.preheader ]
  %x3.i.i1 = getelementptr i64, i64* %x6.i, i64 %a24.i
  %r.i.i = load i64, i64* %x3.i.i1, align 8
  %xda1.i.i = icmp sgt i64 %a24.i, %x1
  br i1 %xda1.i.i, label %then.i.i.preheader, label %Sorting_Introsort_unat_sort_is_insert_impl.exit.i

then.i.i.preheader:                               ; preds = %while_body.i
  br label %then.i.i

then.i.i:                                         ; preds = %then.i.i.preheader, %while_body.i.i2
  %a2a3.i.i = phi i64 [ %bib.i.i, %while_body.i.i2 ], [ %a24.i, %then.i.i.preheader ]
  %bib.i.i = add nsw i64 %a2a3.i.i, -1
  %xea.i.i = getelementptr i64, i64* %x6.i, i64 %bib.i.i
  %ra.i.i = load i64, i64* %xea.i.i, align 8
  %xh.i.i = icmp ult i64 %r.i.i, %ra.i.i
  %p1.i.i = getelementptr i64, i64* %x6.i, i64 %a2a3.i.i
  br i1 %xh.i.i, label %while_body.i.i2, label %Sorting_Introsort_unat_sort_is_insert_impl.exit.i

while_body.i.i2:                                  ; preds = %then.i.i
  store i64 %ra.i.i, i64* %p1.i.i, align 8
  %xda.i.i = icmp sgt i64 %bib.i.i, %x1
  br i1 %xda.i.i, label %then.i.i, label %Sorting_Introsort_unat_sort_is_insert_impl.exit.i.loopexit.split.loop.exit

Sorting_Introsort_unat_sort_is_insert_impl.exit.i.loopexit.split.loop.exit: ; preds = %while_body.i.i2
  %xea.i.i.le = getelementptr i64, i64* %x6.i, i64 %bib.i.i
  br label %Sorting_Introsort_unat_sort_is_insert_impl.exit.i

Sorting_Introsort_unat_sort_is_insert_impl.exit.i: ; preds = %then.i.i, %Sorting_Introsort_unat_sort_is_insert_impl.exit.i.loopexit.split.loop.exit, %while_body.i
  %p2.pre-phi.i.i = phi i64* [ %x3.i.i1, %while_body.i ], [ %xea.i.i.le, %Sorting_Introsort_unat_sort_is_insert_impl.exit.i.loopexit.split.loop.exit ], [ %p1.i.i, %then.i.i ]
  store i64 %r.i.i, i64* %p2.pre-phi.i.i, align 8
  %xba.i = add nsw i64 %a24.i, 1
  %exitcond.i = icmp eq i64 %xba.i, %x2
  br i1 %exitcond.i, label %ctd_if, label %while_body.i

ctd_if:                                           ; preds = %Sorting_Introsort_unat_sort_is_insert_impl.exit.i, %Sorting_Log2_word_clz_impl.exit, %start
  %x5 = phi i64* [ %x, %start ], [ %x6.i, %Sorting_Log2_word_clz_impl.exit ], [ %x6.i, %Sorting_Introsort_unat_sort_is_insert_impl.exit.i ]
  ret i64* %x5
}

; Function Attrs: norecurse nounwind
define i64* @Sorting_Introsort_unat_sort_is_insert_impl(i64* %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %x3 = getelementptr i64, i64* %x, i64 %x2
  %r = load i64, i64* %x3, align 8
  %xda1 = icmp sgt i64 %x2, %x1
  br i1 %xda1, label %then.preheader, label %while_end

then.preheader:                                   ; preds = %start
  br label %then

then:                                             ; preds = %then.preheader, %while_body
  %a2a3 = phi i64 [ %bib, %while_body ], [ %x2, %then.preheader ]
  %bib = add nsw i64 %a2a3, -1
  %xea = getelementptr i64, i64* %x, i64 %bib
  %ra = load i64, i64* %xea, align 8
  %xh = icmp ult i64 %r, %ra
  %p1 = getelementptr i64, i64* %x, i64 %a2a3
  br i1 %xh, label %while_body, label %while_end

while_body:                                       ; preds = %then
  store i64 %ra, i64* %p1, align 8
  %xda = icmp sgt i64 %bib, %x1
  br i1 %xda, label %then, label %while_end.loopexit

while_end.loopexit:                               ; preds = %while_body
  %xea.le = getelementptr i64, i64* %x, i64 %bib
  br label %while_end

while_end:                                        ; preds = %then, %while_end.loopexit, %start
  %p2.pre-phi = phi i64* [ %x3, %start ], [ %xea.le, %while_end.loopexit ], [ %p1, %then ]
  store i64 %r, i64* %p2.pre-phi, align 8
  ret i64* %x
}

; Function Attrs: norecurse nounwind
define i64* @Sorting_Introsort_unat_sort_sift_down_impl(i64 %x, i64 %x1, i64 %x2, i64* %x3) local_unnamed_addr #0 {
start:
  %x4 = sub i64 %x2, %x
  %xb = getelementptr i64, i64* %x3, i64 %x2
  %r = load i64, i64* %xb, align 8
  %xga = sub i64 %x1, %x
  %xha = add i64 %xga, -1
  %xia = lshr i64 %xha, 1
  %xj3 = icmp slt i64 %x4, %xia
  br i1 %xj3, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %ctd_if
  %a1b4 = phi i64 [ %xha1.sink, %ctd_if ], [ %x4, %while_body.preheader ]
  %xga1 = shl i64 %a1b4, 1
  %xha1 = or i64 %xga1, 1
  %xja = add i64 %xga1, 2
  %xk = add i64 %xha1, %x
  %xl = add i64 %xja, %x
  %xm = getelementptr i64, i64* %x3, i64 %xk
  %ra = load i64, i64* %xm, align 8
  %xp = getelementptr i64, i64* %x3, i64 %xl
  %rb = load i64, i64* %xp, align 8
  %xs = icmp ult i64 %ra, %rb
  br i1 %xs, label %then, label %else

then:                                             ; preds = %while_body
  %ya = icmp ult i64 %r, %rb
  br i1 %ya, label %thena, label %ctd_if

thena:                                            ; preds = %then
  %yh = add i64 %a1b4, %x
  %pc = getelementptr i64, i64* %x3, i64 %yh
  store i64 %rb, i64* %pc, align 8
  br label %ctd_if

else:                                             ; preds = %while_body
  %ya1 = icmp ult i64 %r, %ra
  br i1 %ya1, label %thenb, label %ctd_if

thenb:                                            ; preds = %else
  %yh1 = add i64 %a1b4, %x
  %pc1 = getelementptr i64, i64* %x3, i64 %yh1
  store i64 %ra, i64* %pc1, align 8
  br label %ctd_if

ctd_if:                                           ; preds = %else, %then, %thenb, %thena
  %xha1.sink = phi i64 [ %xha1, %thenb ], [ %xja, %thena ], [ %a1b4, %then ], [ %a1b4, %else ]
  %.sink = phi i1 [ true, %thenb ], [ true, %thena ], [ false, %then ], [ false, %else ]
  %xj = icmp slt i64 %xha1.sink, %xia
  %x5 = and i1 %.sink, %xj
  br i1 %x5, label %while_body, label %while_end

while_end:                                        ; preds = %ctd_if, %start
  %a1b.lcssa = phi i64 [ %x4, %start ], [ %xha1.sink, %ctd_if ]
  %xha2 = lshr i64 %xga, 1
  %xi1 = icmp slt i64 %a1b.lcssa, %xha2
  br i1 %xi1, label %thenc, label %elsec

thenc:                                            ; preds = %while_end
  %xj1 = shl i64 %a1b.lcssa, 1
  %xka = or i64 %xj1, 1
  %xl1 = add i64 %xka, %x
  %xm1 = getelementptr i64, i64* %x3, i64 %xl1
  %ra1 = load i64, i64* %xm1, align 8
  %xp1 = icmp ult i64 %r, %ra1
  %xw2 = add i64 %a1b.lcssa, %x
  %pa1 = getelementptr i64, i64* %x3, i64 %xw2
  br i1 %xp1, label %thend, label %ctd_ifc

thend:                                            ; preds = %thenc
  store i64 %ra1, i64* %pa1, align 8
  br label %ctd_ifc

elsec:                                            ; preds = %while_end
  %xj2 = add i64 %a1b.lcssa, %x
  %p2 = getelementptr i64, i64* %x3, i64 %xj2
  br label %ctd_ifc

ctd_ifc:                                          ; preds = %thenc, %thend, %elsec
  %xm1.sink = phi i64* [ %xm1, %thend ], [ %p2, %elsec ], [ %pa1, %thenc ]
  store i64 %r, i64* %xm1.sink, align 8
  ret i64* %x3
}

; Function Attrs: norecurse nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_heapify_btu_impl(i64 %x, i64 %x1, { i64, { i64, i8* } }* %x2) local_unnamed_addr #0 {
start:
  %xa = add i64 %x1, -1
  %x41 = icmp sgt i64 %xa, %x
  br i1 %x41, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %a113 = phi { i64, { i64, i8* } }* [ %xca, %while_body ], [ %x2, %while_body.preheader ]
  %x32 = phi i64 [ %xba, %while_body ], [ %xa, %while_body.preheader ]
  %xba = add i64 %x32, -1
  %xca = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_sift_down_impl(i64 %x, i64 %x1, i64 %xba, { i64, { i64, i8* } }* %a113)
  %x4 = icmp sgt i64 %xba, %x
  br i1 %x4, label %while_body, label %while_end

while_end:                                        ; preds = %while_body, %start
  %a11.lcssa = phi { i64, { i64, i8* } }* [ %x2, %start ], [ %xca, %while_body ]
  ret { i64, { i64, i8* } }* %a11.lcssa
}

; Function Attrs: norecurse nounwind
define { { i64, { i64, i8* } }*, i64 } @Sorting_Introsort_str_sort_qs_partition_impl(i64 %x, i64 %x1, i64 %x2, { i64, { i64, i8* } }* %x3) local_unnamed_addr #0 {
start:
  %ra.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x2, i32 0
  %ra.unpack = load i64, i64* %ra.elt, align 8
  %ra.unpack9.elt11 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x2, i32 1, i32 1
  %ra.unpack9.unpack12 = load i8*, i8** %ra.unpack9.elt11, align 8
  br label %while_start

while_start:                                      ; preds = %while_body, %start
  %s = phi i64 [ %x5, %while_body ], [ %x, %start ]
  %r.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s, i32 0
  %r.unpack = load i64, i64* %r.elt, align 8
  %r.unpack2.elt5 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s, i32 1, i32 1
  %r.unpack2.unpack6 = load i8*, i8** %r.unpack2.elt5, align 8
  %xd.i = icmp sgt i64 %r.unpack, %ra.unpack
  %la.l.i = select i1 %xd.i, i64 %ra.unpack, i64 %r.unpack
  %xga1.i = icmp sgt i64 %la.l.i, 0
  br i1 %xga1.i, label %while_body.i.preheader, label %Sorting_Strings_strcmp_impl.exit

while_body.i.preheader:                           ; preds = %while_start
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %ctd_ifa.i
  %a12.i = phi i64 [ %a1.i, %ctd_ifa.i ], [ 0, %while_body.i.preheader ]
  %xh.i = getelementptr i8, i8* %r.unpack2.unpack6, i64 %a12.i
  %xi.i = load i8, i8* %xh.i, align 1
  %xk.i = getelementptr i8, i8* %ra.unpack9.unpack12, i64 %a12.i
  %xl.i = load i8, i8* %xk.i, align 1
  %xm.i = icmp eq i8 %xi.i, %xl.i
  br i1 %xm.i, label %thena.i, label %elsea.i

thena.i:                                          ; preds = %while_body.i
  %xna.i = add i64 %a12.i, 1
  %xo.i = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i, 0
  %x5.i = insertvalue { i64, i2 } %xo.i, i2 0, 1
  br label %ctd_ifa.i

elsea.i:                                          ; preds = %while_body.i
  %xn.i = icmp ult i8 %xi.i, %xl.i
  %xoa.i = add i64 %a12.i, 1
  %xp.i = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i, 0
  %x7.i = insertvalue { i64, i2 } %xp.i, i2 1, 1
  %x6.i = insertvalue { i64, i2 } %xp.i, i2 -1, 1
  %x8.i = select i1 %xn.i, { i64, i2 } %x6.i, { i64, i2 } %x7.i
  br label %ctd_ifa.i

ctd_ifa.i:                                        ; preds = %elsea.i, %thena.i
  %x9.i = phi { i64, i2 } [ %x5.i, %thena.i ], [ %x8.i, %elsea.i ]
  %a1.i = extractvalue { i64, i2 } %x9.i, 0
  %a2.i = extractvalue { i64, i2 } %x9.i, 1
  %xga.i = icmp slt i64 %a1.i, %la.l.i
  %x3.i = icmp eq i2 %a2.i, 0
  %x4.i = and i1 %xga.i, %x3.i
  br i1 %x4.i, label %while_body.i, label %while_end.i

while_end.i:                                      ; preds = %ctd_ifa.i
  switch i2 %a2.i, label %while_starta.preheader [
    i2 -1, label %while_body
    i2 0, label %Sorting_Strings_strcmp_impl.exit
  ]

Sorting_Strings_strcmp_impl.exit:                 ; preds = %while_start, %while_end.i
  %x10.i = icmp slt i64 %r.unpack, %ra.unpack
  br i1 %x10.i, label %while_body, label %while_starta.preheader

while_starta.preheader:                           ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  br label %while_starta

while_body:                                       ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  %x5 = add i64 %s, 1
  br label %while_start

while_starta:                                     ; preds = %while_starta.backedge, %while_starta.preheader
  %s1.in = phi i64 [ %x1, %while_starta.preheader ], [ %s1, %while_starta.backedge ]
  %s1 = add i64 %s1.in, -1
  %ra1.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s1, i32 0
  %ra1.unpack = load i64, i64* %ra1.elt, align 8
  %ra1.unpack29.elt31 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s1, i32 1, i32 1
  %ra1.unpack29.unpack32 = load i8*, i8** %ra1.unpack29.elt31, align 8
  %xd.i156 = icmp sgt i64 %ra.unpack, %ra1.unpack
  %la.l.i157 = select i1 %xd.i156, i64 %ra1.unpack, i64 %ra.unpack
  %xga1.i158 = icmp sgt i64 %la.l.i157, 0
  br i1 %xga1.i158, label %while_body.i166.preheader, label %Sorting_Strings_strcmp_impl.exit191

while_body.i166.preheader:                        ; preds = %while_starta
  br label %while_body.i166

while_body.i166:                                  ; preds = %while_body.i166.preheader, %ctd_ifa.i184
  %a12.i160 = phi i64 [ %a1.i179, %ctd_ifa.i184 ], [ 0, %while_body.i166.preheader ]
  %xh.i161 = getelementptr i8, i8* %ra.unpack9.unpack12, i64 %a12.i160
  %xi.i162 = load i8, i8* %xh.i161, align 1
  %xk.i163 = getelementptr i8, i8* %ra1.unpack29.unpack32, i64 %a12.i160
  %xl.i164 = load i8, i8* %xk.i163, align 1
  %xm.i165 = icmp eq i8 %xi.i162, %xl.i164
  br i1 %xm.i165, label %thena.i170, label %elsea.i177

thena.i170:                                       ; preds = %while_body.i166
  %xna.i167 = add i64 %a12.i160, 1
  %xo.i168 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i167, 0
  %x5.i169 = insertvalue { i64, i2 } %xo.i168, i2 0, 1
  br label %ctd_ifa.i184

elsea.i177:                                       ; preds = %while_body.i166
  %xn.i171 = icmp ult i8 %xi.i162, %xl.i164
  %xoa.i172 = add i64 %a12.i160, 1
  %xp.i173 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i172, 0
  %x7.i174 = insertvalue { i64, i2 } %xp.i173, i2 1, 1
  %x6.i175 = insertvalue { i64, i2 } %xp.i173, i2 -1, 1
  %x8.i176 = select i1 %xn.i171, { i64, i2 } %x6.i175, { i64, i2 } %x7.i174
  br label %ctd_ifa.i184

ctd_ifa.i184:                                     ; preds = %elsea.i177, %thena.i170
  %x9.i178 = phi { i64, i2 } [ %x5.i169, %thena.i170 ], [ %x8.i176, %elsea.i177 ]
  %a1.i179 = extractvalue { i64, i2 } %x9.i178, 0
  %a2.i180 = extractvalue { i64, i2 } %x9.i178, 1
  %xga.i181 = icmp slt i64 %a1.i179, %la.l.i157
  %x3.i182 = icmp eq i2 %a2.i180, 0
  %x4.i183 = and i1 %xga.i181, %x3.i182
  br i1 %x4.i183, label %while_body.i166, label %while_end.i185

while_end.i185:                                   ; preds = %ctd_ifa.i184
  switch i2 %a2.i180, label %while_enda [
    i2 -1, label %while_starta.backedge
    i2 0, label %Sorting_Strings_strcmp_impl.exit191
  ]

while_starta.backedge:                            ; preds = %while_end.i185, %Sorting_Strings_strcmp_impl.exit191
  br label %while_starta

Sorting_Strings_strcmp_impl.exit191:              ; preds = %while_starta, %while_end.i185
  %x10.i186 = icmp slt i64 %ra.unpack, %ra1.unpack
  br i1 %x10.i186, label %while_starta.backedge, label %while_enda

while_enda:                                       ; preds = %while_end.i185, %Sorting_Strings_strcmp_impl.exit191
  %x9196 = icmp slt i64 %s, %s1
  br i1 %x9196, label %while_bodyb.preheader, label %while_endb

while_bodyb.preheader:                            ; preds = %while_enda
  br label %while_bodyb

while_bodyb:                                      ; preds = %while_bodyb.preheader, %while_endd
  %ra.unpack.i = phi i64 [ %ra3.unpack, %while_endd ], [ %ra1.unpack, %while_bodyb.preheader ]
  %r.unpack.i = phi i64 [ %r2.unpack, %while_endd ], [ %r.unpack, %while_bodyb.preheader ]
  %x8198 = phi i64 [ %s3, %while_endd ], [ %s1, %while_bodyb.preheader ]
  %a197 = phi i64 [ %s2, %while_endd ], [ %s, %while_bodyb.preheader ]
  %r.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %a197, i32 0
  %r.unpack2.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %a197, i32 1, i32 0
  %0 = bitcast i64* %r.unpack2.elt.i to <2 x i64>*
  %1 = load <2 x i64>, <2 x i64>* %0, align 8
  %ra.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x8198, i32 0
  %ra.unpack8.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %x8198, i32 1, i32 0
  %2 = bitcast i64* %ra.unpack8.elt.i to <2 x i64>*
  %3 = load <2 x i64>, <2 x i64>* %2, align 8
  store i64 %ra.unpack.i, i64* %r.elt.i, align 8
  %4 = bitcast i64* %r.unpack2.elt.i to <2 x i64>*
  store <2 x i64> %3, <2 x i64>* %4, align 8
  store i64 %r.unpack.i, i64* %ra.elt.i, align 8
  %5 = bitcast i64* %ra.unpack8.elt.i to <2 x i64>*
  store <2 x i64> %1, <2 x i64>* %5, align 8
  %ra2.unpack = load i64, i64* %ra.elt, align 8
  %ra2.unpack50.unpack53 = load i8*, i8** %ra.unpack9.elt11, align 8
  br label %while_startc

while_startc:                                     ; preds = %while_startc.backedge, %while_bodyb
  %s2.in = phi i64 [ %a197, %while_bodyb ], [ %s2, %while_startc.backedge ]
  %s2 = add i64 %s2.in, 1
  %r2.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s2, i32 0
  %r2.unpack = load i64, i64* %r2.elt, align 8
  %r2.unpack44.elt46 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s2, i32 1, i32 1
  %r2.unpack44.unpack47 = load i8*, i8** %r2.unpack44.elt46, align 8
  %xd.i120 = icmp sgt i64 %r2.unpack, %ra2.unpack
  %la.l.i121 = select i1 %xd.i120, i64 %ra2.unpack, i64 %r2.unpack
  %xga1.i122 = icmp sgt i64 %la.l.i121, 0
  br i1 %xga1.i122, label %while_body.i130.preheader, label %Sorting_Strings_strcmp_impl.exit155

while_body.i130.preheader:                        ; preds = %while_startc
  br label %while_body.i130

while_body.i130:                                  ; preds = %while_body.i130.preheader, %ctd_ifa.i148
  %a12.i124 = phi i64 [ %a1.i143, %ctd_ifa.i148 ], [ 0, %while_body.i130.preheader ]
  %xh.i125 = getelementptr i8, i8* %r2.unpack44.unpack47, i64 %a12.i124
  %xi.i126 = load i8, i8* %xh.i125, align 1
  %xk.i127 = getelementptr i8, i8* %ra2.unpack50.unpack53, i64 %a12.i124
  %xl.i128 = load i8, i8* %xk.i127, align 1
  %xm.i129 = icmp eq i8 %xi.i126, %xl.i128
  br i1 %xm.i129, label %thena.i134, label %elsea.i141

thena.i134:                                       ; preds = %while_body.i130
  %xna.i131 = add i64 %a12.i124, 1
  %xo.i132 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i131, 0
  %x5.i133 = insertvalue { i64, i2 } %xo.i132, i2 0, 1
  br label %ctd_ifa.i148

elsea.i141:                                       ; preds = %while_body.i130
  %xn.i135 = icmp ult i8 %xi.i126, %xl.i128
  %xoa.i136 = add i64 %a12.i124, 1
  %xp.i137 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i136, 0
  %x7.i138 = insertvalue { i64, i2 } %xp.i137, i2 1, 1
  %x6.i139 = insertvalue { i64, i2 } %xp.i137, i2 -1, 1
  %x8.i140 = select i1 %xn.i135, { i64, i2 } %x6.i139, { i64, i2 } %x7.i138
  br label %ctd_ifa.i148

ctd_ifa.i148:                                     ; preds = %elsea.i141, %thena.i134
  %x9.i142 = phi { i64, i2 } [ %x5.i133, %thena.i134 ], [ %x8.i140, %elsea.i141 ]
  %a1.i143 = extractvalue { i64, i2 } %x9.i142, 0
  %a2.i144 = extractvalue { i64, i2 } %x9.i142, 1
  %xga.i145 = icmp slt i64 %a1.i143, %la.l.i121
  %x3.i146 = icmp eq i2 %a2.i144, 0
  %x4.i147 = and i1 %xga.i145, %x3.i146
  br i1 %x4.i147, label %while_body.i130, label %while_end.i149

while_end.i149:                                   ; preds = %ctd_ifa.i148
  switch i2 %a2.i144, label %while_startd.preheader [
    i2 -1, label %while_startc.backedge
    i2 0, label %Sorting_Strings_strcmp_impl.exit155
  ]

while_startc.backedge:                            ; preds = %while_end.i149, %Sorting_Strings_strcmp_impl.exit155
  br label %while_startc

Sorting_Strings_strcmp_impl.exit155:              ; preds = %while_startc, %while_end.i149
  %x10.i150 = icmp slt i64 %r2.unpack, %ra2.unpack
  br i1 %x10.i150, label %while_startc.backedge, label %while_startd.preheader

while_startd.preheader:                           ; preds = %while_end.i149, %Sorting_Strings_strcmp_impl.exit155
  br label %while_startd

while_startd:                                     ; preds = %while_startd.backedge, %while_startd.preheader
  %s3.in = phi i64 [ %x8198, %while_startd.preheader ], [ %s3, %while_startd.backedge ]
  %s3 = add i64 %s3.in, -1
  %ra3.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s3, i32 0
  %ra3.unpack = load i64, i64* %ra3.elt, align 8
  %ra3.unpack70.elt72 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %x3, i64 %s3, i32 1, i32 1
  %ra3.unpack70.unpack73 = load i8*, i8** %ra3.unpack70.elt72, align 8
  %xd.i84 = icmp sgt i64 %ra2.unpack, %ra3.unpack
  %la.l.i85 = select i1 %xd.i84, i64 %ra3.unpack, i64 %ra2.unpack
  %xga1.i86 = icmp sgt i64 %la.l.i85, 0
  br i1 %xga1.i86, label %while_body.i94.preheader, label %Sorting_Strings_strcmp_impl.exit119

while_body.i94.preheader:                         ; preds = %while_startd
  br label %while_body.i94

while_body.i94:                                   ; preds = %while_body.i94.preheader, %ctd_ifa.i112
  %a12.i88 = phi i64 [ %a1.i107, %ctd_ifa.i112 ], [ 0, %while_body.i94.preheader ]
  %xh.i89 = getelementptr i8, i8* %ra2.unpack50.unpack53, i64 %a12.i88
  %xi.i90 = load i8, i8* %xh.i89, align 1
  %xk.i91 = getelementptr i8, i8* %ra3.unpack70.unpack73, i64 %a12.i88
  %xl.i92 = load i8, i8* %xk.i91, align 1
  %xm.i93 = icmp eq i8 %xi.i90, %xl.i92
  br i1 %xm.i93, label %thena.i98, label %elsea.i105

thena.i98:                                        ; preds = %while_body.i94
  %xna.i95 = add i64 %a12.i88, 1
  %xo.i96 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i95, 0
  %x5.i97 = insertvalue { i64, i2 } %xo.i96, i2 0, 1
  br label %ctd_ifa.i112

elsea.i105:                                       ; preds = %while_body.i94
  %xn.i99 = icmp ult i8 %xi.i90, %xl.i92
  %xoa.i100 = add i64 %a12.i88, 1
  %xp.i101 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i100, 0
  %x7.i102 = insertvalue { i64, i2 } %xp.i101, i2 1, 1
  %x6.i103 = insertvalue { i64, i2 } %xp.i101, i2 -1, 1
  %x8.i104 = select i1 %xn.i99, { i64, i2 } %x6.i103, { i64, i2 } %x7.i102
  br label %ctd_ifa.i112

ctd_ifa.i112:                                     ; preds = %elsea.i105, %thena.i98
  %x9.i106 = phi { i64, i2 } [ %x5.i97, %thena.i98 ], [ %x8.i104, %elsea.i105 ]
  %a1.i107 = extractvalue { i64, i2 } %x9.i106, 0
  %a2.i108 = extractvalue { i64, i2 } %x9.i106, 1
  %xga.i109 = icmp slt i64 %a1.i107, %la.l.i85
  %x3.i110 = icmp eq i2 %a2.i108, 0
  %x4.i111 = and i1 %xga.i109, %x3.i110
  br i1 %x4.i111, label %while_body.i94, label %while_end.i113

while_end.i113:                                   ; preds = %ctd_ifa.i112
  switch i2 %a2.i108, label %while_endd [
    i2 -1, label %while_startd.backedge
    i2 0, label %Sorting_Strings_strcmp_impl.exit119
  ]

while_startd.backedge:                            ; preds = %while_end.i113, %Sorting_Strings_strcmp_impl.exit119
  br label %while_startd

Sorting_Strings_strcmp_impl.exit119:              ; preds = %while_startd, %while_end.i113
  %x10.i114 = icmp slt i64 %ra2.unpack, %ra3.unpack
  br i1 %x10.i114, label %while_startd.backedge, label %while_endd

while_endd:                                       ; preds = %while_end.i113, %Sorting_Strings_strcmp_impl.exit119
  %x9 = icmp slt i64 %s2, %s3
  br i1 %x9, label %while_bodyb, label %while_endb

while_endb:                                       ; preds = %while_endd, %while_enda
  %a.lcssa = phi i64 [ %s, %while_enda ], [ %s2, %while_endd ]
  %xea1 = insertvalue { { i64, { i64, i8* } }*, i64 } zeroinitializer, { i64, { i64, i8* } }* %x3, 0
  %x14 = insertvalue { { i64, { i64, i8* } }*, i64 } %xea1, i64 %a.lcssa, 1
  ret { { i64, { i64, i8* } }*, i64 } %x14
}

; Function Attrs: norecurse nounwind
define i64* @Sorting_Introsort_unat_sort_heapify_btu_impl(i64 %x, i64 %x1, i64* %x2) local_unnamed_addr #0 {
start:
  %xa = add i64 %x1, -1
  %x41 = icmp sgt i64 %xa, %x
  br i1 %x41, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %a113 = phi i64* [ %xca, %while_body ], [ %x2, %while_body.preheader ]
  %x32 = phi i64 [ %xba, %while_body ], [ %xa, %while_body.preheader ]
  %xba = add i64 %x32, -1
  %xca = tail call i64* @Sorting_Introsort_unat_sort_sift_down_impl(i64 %x, i64 %x1, i64 %xba, i64* %a113)
  %x4 = icmp sgt i64 %xba, %x
  br i1 %x4, label %while_body, label %while_end

while_end:                                        ; preds = %while_body, %start
  %a11.lcssa = phi i64* [ %x2, %start ], [ %xca, %while_body ]
  ret i64* %a11.lcssa
}

; Function Attrs: norecurse nounwind
define { i64*, i64 } @Sorting_Introsort_unat_sort_qs_partition_impl(i64 %x, i64 %x1, i64 %x2, i64* %x3) local_unnamed_addr #0 {
start:
  %xc = getelementptr i64, i64* %x3, i64 %x2
  %ra = load i64, i64* %xc, align 8
  br label %while_start

while_start:                                      ; preds = %while_start, %start
  %s = phi i64 [ %x5, %while_start ], [ %x, %start ]
  %x4 = getelementptr i64, i64* %x3, i64 %s
  %r = load i64, i64* %x4, align 8
  %xf = icmp ult i64 %r, %ra
  %x5 = add i64 %s, 1
  br i1 %xf, label %while_start, label %while_starta.preheader

while_starta.preheader:                           ; preds = %while_start
  br label %while_starta

while_starta:                                     ; preds = %while_starta.preheader, %while_starta
  %s1.in = phi i64 [ %s1, %while_starta ], [ %x1, %while_starta.preheader ]
  %s1 = add i64 %s1.in, -1
  %xe1 = getelementptr i64, i64* %x3, i64 %s1
  %ra1 = load i64, i64* %xe1, align 8
  %xh = icmp ult i64 %ra, %ra1
  br i1 %xh, label %while_starta, label %while_enda

while_enda:                                       ; preds = %while_starta
  %x91 = icmp slt i64 %s, %s1
  br i1 %x91, label %while_bodyb.preheader, label %while_endb

while_bodyb.preheader:                            ; preds = %while_enda
  br label %while_bodyb

while_bodyb:                                      ; preds = %while_bodyb.preheader, %while_endd
  %ra.i = phi i64 [ %ra3, %while_endd ], [ %ra1, %while_bodyb.preheader ]
  %r.i = phi i64 [ %r2, %while_endd ], [ %r, %while_bodyb.preheader ]
  %x83 = phi i64 [ %s3, %while_endd ], [ %s1, %while_bodyb.preheader ]
  %a2 = phi i64 [ %s2, %while_endd ], [ %s, %while_bodyb.preheader ]
  %x3.i = getelementptr i64, i64* %x3, i64 %a2
  %xc.i = getelementptr i64, i64* %x3, i64 %x83
  store i64 %ra.i, i64* %x3.i, align 8
  store i64 %r.i, i64* %xc.i, align 8
  %ra2 = load i64, i64* %xc, align 8
  br label %while_startc

while_startc:                                     ; preds = %while_startc, %while_bodyb
  %s2.in = phi i64 [ %s2, %while_startc ], [ %a2, %while_bodyb ]
  %s2 = add i64 %s2.in, 1
  %xg1 = getelementptr i64, i64* %x3, i64 %s2
  %r2 = load i64, i64* %xg1, align 8
  %xm = icmp ult i64 %r2, %ra2
  br i1 %xm, label %while_startc, label %while_startd.preheader

while_startd.preheader:                           ; preds = %while_startc
  br label %while_startd

while_startd:                                     ; preds = %while_startd.preheader, %while_startd
  %s3.in = phi i64 [ %s3, %while_startd ], [ %x83, %while_startd.preheader ]
  %s3 = add i64 %s3.in, -1
  %xl1 = getelementptr i64, i64* %x3, i64 %s3
  %ra3 = load i64, i64* %xl1, align 8
  %xo = icmp ult i64 %ra2, %ra3
  br i1 %xo, label %while_startd, label %while_endd

while_endd:                                       ; preds = %while_startd
  %x9 = icmp slt i64 %s2, %s3
  br i1 %x9, label %while_bodyb, label %while_endb

while_endb:                                       ; preds = %while_endd, %while_enda
  %a.lcssa = phi i64 [ %s, %while_enda ], [ %s2, %while_endd ]
  %xea1 = insertvalue { i64*, i64 } zeroinitializer, i64* %x3, 0
  %x14 = insertvalue { i64*, i64 } %xea1, i64 %a.lcssa, 1
  ret { i64*, i64 } %x14
}

; Function Attrs: norecurse nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_insertion_sort_impl({ i64, { i64, i8* } }* %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %x41 = icmp slt i64 %x1, %x2
  br i1 %x41, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %while_body
  %a113 = phi { i64, { i64, i8* } }* [ %xaa, %while_body ], [ %x, %while_body.preheader ]
  %a22 = phi i64 [ %xba, %while_body ], [ %x1, %while_body.preheader ]
  %xaa = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_is_insert_impl({ i64, { i64, i8* } }* %a113, i64 %x1, i64 %a22)
  %xba = add nsw i64 %a22, 1
  %exitcond = icmp eq i64 %xba, %x2
  br i1 %exitcond, label %while_end, label %while_body

while_end:                                        ; preds = %while_body, %start
  %a11.lcssa = phi { i64, { i64, i8* } }* [ %x, %start ], [ %xaa, %while_body ]
  ret { i64, { i64, i8* } }* %a11.lcssa
}

; Function Attrs: norecurse nounwind
define i64* @insertion_sort(i64* %x, i64 %x1, i64 %x2) local_unnamed_addr #0 {
start:
  %x43 = icmp slt i64 %x1, %x2
  br i1 %x43, label %while_body.preheader, label %while_end

while_body.preheader:                             ; preds = %start
  br label %while_body

while_body:                                       ; preds = %while_body.preheader, %Sorting_Introsort_unat_sort_is_insert_impl.exit
  %a24 = phi i64 [ %xba, %Sorting_Introsort_unat_sort_is_insert_impl.exit ], [ %x1, %while_body.preheader ]
  %x3.i = getelementptr i64, i64* %x, i64 %a24
  %r.i = load i64, i64* %x3.i, align 8
  %xda1.i = icmp sgt i64 %a24, %x1
  br i1 %xda1.i, label %then.i.preheader, label %Sorting_Introsort_unat_sort_is_insert_impl.exit

then.i.preheader:                                 ; preds = %while_body
  br label %then.i

then.i:                                           ; preds = %then.i.preheader, %while_body.i
  %a2a3.i = phi i64 [ %bib.i, %while_body.i ], [ %a24, %then.i.preheader ]
  %bib.i = add nsw i64 %a2a3.i, -1
  %xea.i = getelementptr i64, i64* %x, i64 %bib.i
  %ra.i = load i64, i64* %xea.i, align 8
  %xh.i = icmp ult i64 %r.i, %ra.i
  %p1.i = getelementptr i64, i64* %x, i64 %a2a3.i
  br i1 %xh.i, label %while_body.i, label %Sorting_Introsort_unat_sort_is_insert_impl.exit

while_body.i:                                     ; preds = %then.i
  store i64 %ra.i, i64* %p1.i, align 8
  %xda.i = icmp sgt i64 %bib.i, %x1
  br i1 %xda.i, label %then.i, label %Sorting_Introsort_unat_sort_is_insert_impl.exit.loopexit.split.loop.exit

Sorting_Introsort_unat_sort_is_insert_impl.exit.loopexit.split.loop.exit: ; preds = %while_body.i
  %xea.i.le = getelementptr i64, i64* %x, i64 %bib.i
  br label %Sorting_Introsort_unat_sort_is_insert_impl.exit

Sorting_Introsort_unat_sort_is_insert_impl.exit:  ; preds = %then.i, %Sorting_Introsort_unat_sort_is_insert_impl.exit.loopexit.split.loop.exit, %while_body
  %p2.pre-phi.i = phi i64* [ %x3.i, %while_body ], [ %xea.i.le, %Sorting_Introsort_unat_sort_is_insert_impl.exit.loopexit.split.loop.exit ], [ %p1.i, %then.i ]
  store i64 %r.i, i64* %p2.pre-phi.i, align 8
  %xba = add nsw i64 %a24, 1
  %exitcond = icmp eq i64 %xba, %x2
  br i1 %exitcond, label %while_end, label %while_body

while_end:                                        ; preds = %Sorting_Introsort_unat_sort_is_insert_impl.exit, %start
  ret i64* %x
}

; Function Attrs: nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_introsort_qs_aux_impl({ i64, { i64, i8* } }* %x, i64 %x1, i64 %x2, i64 %x3) local_unnamed_addr #3 {
start:
  %x4 = insertvalue { i64, i64 } zeroinitializer, i64 %x2, 0
  %tmpa = insertvalue { i64, i64 } %x4, i64 %x3, 1
  %xa = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %x1, 0
  %tmpab = insertvalue { i64, { i64, i64 } } %xa, { i64, i64 } %tmpa, 1
  %xb = insertvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } zeroinitializer, { i64, { i64, i8* } }* %x, 0
  %x5 = insertvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %xb, { i64, { i64, i64 } } %tmpab, 1
  %x6 = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_introsort_qs_aux_impl_f_04889284({ { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %x5)
  ret { i64, { i64, i8* } }* %x6
}

; Function Attrs: norecurse nounwind
define { i64*, i64 } @Sorting_Introsort_unat_sort_qs_partitionXXX_impl(i64 %x, i64 %x1, i64 %x2, i64* %x3) local_unnamed_addr #0 {
start:
  %xf = getelementptr i64, i64* %x3, i64 %x2
  br label %while_body

while_body:                                       ; preds = %start, %ctd_if
  %a1b15 = phi i64 [ %x1, %start ], [ %s1, %ctd_if ]
  %a1a14 = phi i64 [ %x, %start ], [ %x6.sink, %ctd_if ]
  %ra = load i64, i64* %xf, align 8
  br label %while_starta

while_starta:                                     ; preds = %while_starta, %while_body
  %s = phi i64 [ %x6, %while_starta ], [ %a1a14, %while_body ]
  %xca = getelementptr i64, i64* %x3, i64 %s
  %r = load i64, i64* %xca, align 8
  %xi = icmp ult i64 %r, %ra
  %x6 = add i64 %s, 1
  br i1 %xi, label %while_starta, label %while_enda

while_enda:                                       ; preds = %while_starta
  %xca.le = getelementptr i64, i64* %x3, i64 %s
  br label %while_startb

while_startb:                                     ; preds = %while_startb, %while_enda
  %s1.in = phi i64 [ %s1, %while_startb ], [ %a1b15, %while_enda ]
  %s1 = add i64 %s1.in, -1
  %xh1 = getelementptr i64, i64* %x3, i64 %s1
  %ra1 = load i64, i64* %xh1, align 8
  %xk = icmp ult i64 %ra, %ra1
  br i1 %xk, label %while_startb, label %while_endb

while_endb:                                       ; preds = %while_startb
  %xf2 = icmp slt i64 %s, %s1
  br i1 %xf2, label %else, label %while_end

else:                                             ; preds = %while_endb
  %xh1.le = getelementptr i64, i64* %x3, i64 %s1
  store i64 %ra1, i64* %xca.le, align 8
  store i64 %r, i64* %xh1.le, align 8
  br label %ctd_if

ctd_if:                                           ; preds = %while_endb, %else
  ; %.sink = phi i1 [ false, %else ], [ true, %while_endb ]
  %x6.sink = phi i64 [ %x6, %else ]
  br label %while_body

while_end:                                        ; preds = %ctd_if
  %xca2 = insertvalue { i64*, i64 } zeroinitializer, i64* %x3, 0
  %x13 = insertvalue { i64*, i64 } %xca2, i64 %s, 1
  ret { i64*, i64 } %x13
}

; Function Attrs: nounwind
define i64* @introsort_aux(i64* %x, i64 %x1, i64 %x2, i64 %x3) local_unnamed_addr #3 {
start:
  %x4 = insertvalue { i64, i64 } zeroinitializer, i64 %x2, 0
  %tmpa = insertvalue { i64, i64 } %x4, i64 %x3, 1
  %xa = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %x1, 0
  %tmpab = insertvalue { i64, { i64, i64 } } %xa, { i64, i64 } %tmpa, 1
  %xb = insertvalue { i64*, { i64, { i64, i64 } } } zeroinitializer, i64* %x, 0
  %x5 = insertvalue { i64*, { i64, { i64, i64 } } } %xb, { i64, { i64, i64 } } %tmpab, 1
  %x6 = tail call i64* @Sorting_Introsort_unat_sort_introsort_qs_aux_impl_f_04869164({ i64*, { i64, { i64, i64 } } } %x5)
  ret i64* %x6
}

; Function Attrs: nounwind
define { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_introsort_qs_aux_impl_f_04889284({ { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %x) local_unnamed_addr #3 {
start:
  %a1308 = extractvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %x, 0
  %xaa309 = extractvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %x, 1
  %a1a310 = extractvalue { i64, { i64, i64 } } %xaa309, 0
  %xba311 = extractvalue { i64, { i64, i64 } } %xaa309, 1
  %a1b312 = extractvalue { i64, i64 } %xba311, 0
  %xca314 = sub i64 %a1b312, %a1a310
  %xd315 = icmp sgt i64 %xca314, 16
  br i1 %xd315, label %then.lr.ph, label %ctd_if

then.lr.ph:                                       ; preds = %start
  %a2b313 = extractvalue { i64, i64 } %xba311, 1
  %xja = add i64 %a1b312, -1
  br label %then

then:                                             ; preds = %then.lr.ph, %ctd_ifb
  %xca328 = phi i64 [ %xca314, %then.lr.ph ], [ %xca, %ctd_ifb ]
  %a2b327 = phi i64 [ %a2b313, %then.lr.ph ], [ %xza, %ctd_ifb ]
  %a1a319 = phi i64 [ %a1a310, %then.lr.ph ], [ %b, %ctd_ifb ]
  %a1316 = phi { i64, { i64, i8* } }* [ %a1308, %then.lr.ph ], [ %yaa, %ctd_ifb ]
  %xe = icmp sgt i64 %a2b327, 0
  br i1 %xe, label %thena, label %then.i

thena:                                            ; preds = %then
  %xga = lshr i64 %xca328, 1
  %xh = add i64 %xga, %a1a319
  %xia = add i64 %a1a319, 1
  %r.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xia, i32 0
  %r.unpack = load i64, i64* %r.elt, align 8
  %r.unpack2.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xia, i32 1, i32 0
  %r.unpack2.unpack = load i64, i64* %r.unpack2.elt, align 8
  %r.unpack2.elt4 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xia, i32 1, i32 1
  %r.unpack2.unpack5 = load i8*, i8** %r.unpack2.elt4, align 8
  %ra.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xh, i32 0
  %ra.unpack = load i64, i64* %ra.elt, align 8
  %ra.unpack8.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xh, i32 1, i32 0
  %ra.unpack8.unpack = load i64, i64* %ra.unpack8.elt, align 8
  %ra.unpack8.elt10 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xh, i32 1, i32 1
  %ra.unpack8.unpack11 = load i8*, i8** %ra.unpack8.elt10, align 8
  %xd.i = icmp sgt i64 %r.unpack, %ra.unpack
  %la.l.i = select i1 %xd.i, i64 %ra.unpack, i64 %r.unpack
  %xga1.i = icmp sgt i64 %la.l.i, 0
  %0 = ptrtoint i8* %ra.unpack8.unpack11 to i64
  %1 = ptrtoint i8* %r.unpack2.unpack5 to i64
  br i1 %xga1.i, label %while_body.i.preheader, label %Sorting_Strings_strcmp_impl.exit

while_body.i.preheader:                           ; preds = %thena
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %ctd_ifa.i
  %a12.i = phi i64 [ %a1.i, %ctd_ifa.i ], [ 0, %while_body.i.preheader ]
  %xh.i = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i
  %xi.i = load i8, i8* %xh.i, align 1
  %xk.i = getelementptr i8, i8* %ra.unpack8.unpack11, i64 %a12.i
  %xl.i = load i8, i8* %xk.i, align 1
  %xm.i = icmp eq i8 %xi.i, %xl.i
  br i1 %xm.i, label %thena.i, label %elsea.i

thena.i:                                          ; preds = %while_body.i
  %xna.i = add i64 %a12.i, 1
  %xo.i = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i, 0
  %x5.i = insertvalue { i64, i2 } %xo.i, i2 0, 1
  br label %ctd_ifa.i

elsea.i:                                          ; preds = %while_body.i
  %xn.i = icmp ult i8 %xi.i, %xl.i
  %xoa.i = add i64 %a12.i, 1
  %xp.i = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i, 0
  %x7.i = insertvalue { i64, i2 } %xp.i, i2 1, 1
  %x6.i = insertvalue { i64, i2 } %xp.i, i2 -1, 1
  %x8.i = select i1 %xn.i, { i64, i2 } %x6.i, { i64, i2 } %x7.i
  br label %ctd_ifa.i

ctd_ifa.i:                                        ; preds = %elsea.i, %thena.i
  %x9.i = phi { i64, i2 } [ %x5.i, %thena.i ], [ %x8.i, %elsea.i ]
  %a1.i = extractvalue { i64, i2 } %x9.i, 0
  %a2.i = extractvalue { i64, i2 } %x9.i, 1
  %xga.i = icmp slt i64 %a1.i, %la.l.i
  %x3.i = icmp eq i2 %a2.i, 0
  %x4.i = and i1 %xga.i, %x3.i
  br i1 %x4.i, label %while_body.i, label %while_end.i

while_end.i:                                      ; preds = %ctd_ifa.i
  switch i2 %a2.i, label %elseb [
    i2 -1, label %thenb
    i2 0, label %Sorting_Strings_strcmp_impl.exit
  ]

Sorting_Strings_strcmp_impl.exit:                 ; preds = %thena, %while_end.i
  %x10.i = icmp slt i64 %r.unpack, %ra.unpack
  br i1 %x10.i, label %thenb, label %elseb

thenb:                                            ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  %rc.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xja, i32 0
  %2 = bitcast i64* %rc.elt to <2 x i64>*
  %3 = load <2 x i64>, <2 x i64>* %2, align 8
  %rc.unpack59.elt61 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xja, i32 1, i32 1
  %rc.unpack59.unpack62 = load i8*, i8** %rc.unpack59.elt61, align 8
  %4 = extractelement <2 x i64> %3, i32 0
  %xd.i89 = icmp sgt i64 %ra.unpack, %4
  %la.l.i90 = select i1 %xd.i89, i64 %4, i64 %ra.unpack
  %xga1.i91 = icmp sgt i64 %la.l.i90, 0
  %5 = ptrtoint i8* %rc.unpack59.unpack62 to i64
  br i1 %xga1.i91, label %while_body.i99.preheader, label %Sorting_Strings_strcmp_impl.exit124

while_body.i99.preheader:                         ; preds = %thenb
  br label %while_body.i99

while_body.i99:                                   ; preds = %while_body.i99.preheader, %ctd_ifa.i117
  %a12.i93 = phi i64 [ %a1.i112, %ctd_ifa.i117 ], [ 0, %while_body.i99.preheader ]
  %xh.i94 = getelementptr i8, i8* %ra.unpack8.unpack11, i64 %a12.i93
  %xi.i95 = load i8, i8* %xh.i94, align 1
  %xk.i96 = getelementptr i8, i8* %rc.unpack59.unpack62, i64 %a12.i93
  %xl.i97 = load i8, i8* %xk.i96, align 1
  %xm.i98 = icmp eq i8 %xi.i95, %xl.i97
  br i1 %xm.i98, label %thena.i103, label %elsea.i110

thena.i103:                                       ; preds = %while_body.i99
  %xna.i100 = add i64 %a12.i93, 1
  %xo.i101 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i100, 0
  %x5.i102 = insertvalue { i64, i2 } %xo.i101, i2 0, 1
  br label %ctd_ifa.i117

elsea.i110:                                       ; preds = %while_body.i99
  %xn.i104 = icmp ult i8 %xi.i95, %xl.i97
  %xoa.i105 = add i64 %a12.i93, 1
  %xp.i106 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i105, 0
  %x7.i107 = insertvalue { i64, i2 } %xp.i106, i2 1, 1
  %x6.i108 = insertvalue { i64, i2 } %xp.i106, i2 -1, 1
  %x8.i109 = select i1 %xn.i104, { i64, i2 } %x6.i108, { i64, i2 } %x7.i107
  br label %ctd_ifa.i117

ctd_ifa.i117:                                     ; preds = %elsea.i110, %thena.i103
  %x9.i111 = phi { i64, i2 } [ %x5.i102, %thena.i103 ], [ %x8.i109, %elsea.i110 ]
  %a1.i112 = extractvalue { i64, i2 } %x9.i111, 0
  %a2.i113 = extractvalue { i64, i2 } %x9.i111, 1
  %xga.i114 = icmp slt i64 %a1.i112, %la.l.i90
  %x3.i115 = icmp eq i2 %a2.i113, 0
  %x4.i116 = and i1 %xga.i114, %x3.i115
  br i1 %x4.i116, label %while_body.i99, label %while_end.i118

while_end.i118:                                   ; preds = %ctd_ifa.i117
  switch i2 %a2.i113, label %elsec [
    i2 -1, label %thenc
    i2 0, label %Sorting_Strings_strcmp_impl.exit124
  ]

Sorting_Strings_strcmp_impl.exit124:              ; preds = %thenb, %while_end.i118
  %x10.i119 = icmp slt i64 %ra.unpack, %4
  br i1 %x10.i119, label %thenc, label %elsec

thenc:                                            ; preds = %while_end.i118, %Sorting_Strings_strcmp_impl.exit124
  %r.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 0
  %r.unpack2.elt.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 0
  %6 = bitcast i64* %r.elt.i to <2 x i64>*
  %7 = load <2 x i64>, <2 x i64>* %6, align 8
  %r.unpack2.elt4.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 1
  %8 = bitcast i8** %r.unpack2.elt4.i to i64*
  %r.unpack2.unpack522.i = load i64, i64* %8, align 8
  store i64 %ra.unpack, i64* %r.elt.i, align 8
  store i64 %ra.unpack8.unpack, i64* %r.unpack2.elt.i, align 8
  store i64 %0, i64* %8, align 8
  %9 = bitcast i64* %ra.elt to <2 x i64>*
  store <2 x i64> %7, <2 x i64>* %9, align 8
  br label %ctd_ifb

elsec:                                            ; preds = %while_end.i118, %Sorting_Strings_strcmp_impl.exit124
  %xd.i130 = icmp sgt i64 %r.unpack, %4
  %la.l.i131 = select i1 %xd.i130, i64 %4, i64 %r.unpack
  %xga1.i132 = icmp sgt i64 %la.l.i131, 0
  br i1 %xga1.i132, label %while_body.i140.preheader, label %Sorting_Strings_strcmp_impl.exit165

while_body.i140.preheader:                        ; preds = %elsec
  br label %while_body.i140

while_body.i140:                                  ; preds = %while_body.i140.preheader, %ctd_ifa.i158
  %a12.i134 = phi i64 [ %a1.i153, %ctd_ifa.i158 ], [ 0, %while_body.i140.preheader ]
  %xh.i135 = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i134
  %xi.i136 = load i8, i8* %xh.i135, align 1
  %xk.i137 = getelementptr i8, i8* %rc.unpack59.unpack62, i64 %a12.i134
  %xl.i138 = load i8, i8* %xk.i137, align 1
  %xm.i139 = icmp eq i8 %xi.i136, %xl.i138
  br i1 %xm.i139, label %thena.i144, label %elsea.i151

thena.i144:                                       ; preds = %while_body.i140
  %xna.i141 = add i64 %a12.i134, 1
  %xo.i142 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i141, 0
  %x5.i143 = insertvalue { i64, i2 } %xo.i142, i2 0, 1
  br label %ctd_ifa.i158

elsea.i151:                                       ; preds = %while_body.i140
  %xn.i145 = icmp ult i8 %xi.i136, %xl.i138
  %xoa.i146 = add i64 %a12.i134, 1
  %xp.i147 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i146, 0
  %x7.i148 = insertvalue { i64, i2 } %xp.i147, i2 1, 1
  %x6.i149 = insertvalue { i64, i2 } %xp.i147, i2 -1, 1
  %x8.i150 = select i1 %xn.i145, { i64, i2 } %x6.i149, { i64, i2 } %x7.i148
  br label %ctd_ifa.i158

ctd_ifa.i158:                                     ; preds = %elsea.i151, %thena.i144
  %x9.i152 = phi { i64, i2 } [ %x5.i143, %thena.i144 ], [ %x8.i150, %elsea.i151 ]
  %a1.i153 = extractvalue { i64, i2 } %x9.i152, 0
  %a2.i154 = extractvalue { i64, i2 } %x9.i152, 1
  %xga.i155 = icmp slt i64 %a1.i153, %la.l.i131
  %x3.i156 = icmp eq i2 %a2.i154, 0
  %x4.i157 = and i1 %xga.i155, %x3.i156
  br i1 %x4.i157, label %while_body.i140, label %while_end.i159

while_end.i159:                                   ; preds = %ctd_ifa.i158
  switch i2 %a2.i154, label %elsed [
    i2 -1, label %thend
    i2 0, label %Sorting_Strings_strcmp_impl.exit165
  ]

Sorting_Strings_strcmp_impl.exit165:              ; preds = %elsec, %while_end.i159
  %x10.i160 = icmp slt i64 %r.unpack, %4
  br i1 %x10.i160, label %thend, label %elsed

thend:                                            ; preds = %while_end.i159, %Sorting_Strings_strcmp_impl.exit165
  %r.elt.i166 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 0
  %10 = bitcast i64* %r.elt.i166 to <2 x i64>*
  %11 = load <2 x i64>, <2 x i64>* %10, align 8
  %r.unpack2.elt4.i170 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 1
  %12 = bitcast i8** %r.unpack2.elt4.i170 to i64*
  %r.unpack2.unpack522.i171 = load i64, i64* %12, align 8
  %13 = bitcast i64* %r.elt.i166 to <2 x i64>*
  store <2 x i64> %3, <2 x i64>* %13, align 8
  store i64 %5, i64* %12, align 8
  %14 = bitcast i64* %rc.elt to <2 x i64>*
  store <2 x i64> %11, <2 x i64>* %14, align 8
  br label %ctd_ifb

elsed:                                            ; preds = %while_end.i159, %Sorting_Strings_strcmp_impl.exit165
  %r.elt.i178 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 0
  %r.unpack2.elt.i180 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 0
  %15 = bitcast i64* %r.elt.i178 to <2 x i64>*
  %16 = load <2 x i64>, <2 x i64>* %15, align 8
  %r.unpack2.elt4.i182 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 1
  %17 = bitcast i8** %r.unpack2.elt4.i182 to i64*
  %r.unpack2.unpack522.i183 = load i64, i64* %17, align 8
  store i64 %r.unpack, i64* %r.elt.i178, align 8
  store i64 %r.unpack2.unpack, i64* %r.unpack2.elt.i180, align 8
  store i64 %1, i64* %17, align 8
  %18 = bitcast i64* %r.elt to <2 x i64>*
  store <2 x i64> %16, <2 x i64>* %18, align 8
  br label %ctd_ifb

elseb:                                            ; preds = %while_end.i, %Sorting_Strings_strcmp_impl.exit
  %rc1.elt = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xja, i32 0
  %19 = bitcast i64* %rc1.elt to <2 x i64>*
  %20 = load <2 x i64>, <2 x i64>* %19, align 8
  %rc1.unpack28.elt30 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %xja, i32 1, i32 1
  %rc1.unpack28.unpack31 = load i8*, i8** %rc1.unpack28.elt30, align 8
  %21 = extractelement <2 x i64> %20, i32 0
  %xd.i262 = icmp sgt i64 %r.unpack, %21
  %la.l.i263 = select i1 %xd.i262, i64 %21, i64 %r.unpack
  %xga1.i264 = icmp sgt i64 %la.l.i263, 0
  %22 = ptrtoint i8* %rc1.unpack28.unpack31 to i64
  br i1 %xga1.i264, label %while_body.i272.preheader, label %Sorting_Strings_strcmp_impl.exit297

while_body.i272.preheader:                        ; preds = %elseb
  br label %while_body.i272

while_body.i272:                                  ; preds = %while_body.i272.preheader, %ctd_ifa.i290
  %a12.i266 = phi i64 [ %a1.i285, %ctd_ifa.i290 ], [ 0, %while_body.i272.preheader ]
  %xh.i267 = getelementptr i8, i8* %r.unpack2.unpack5, i64 %a12.i266
  %xi.i268 = load i8, i8* %xh.i267, align 1
  %xk.i269 = getelementptr i8, i8* %rc1.unpack28.unpack31, i64 %a12.i266
  %xl.i270 = load i8, i8* %xk.i269, align 1
  %xm.i271 = icmp eq i8 %xi.i268, %xl.i270
  br i1 %xm.i271, label %thena.i276, label %elsea.i283

thena.i276:                                       ; preds = %while_body.i272
  %xna.i273 = add i64 %a12.i266, 1
  %xo.i274 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i273, 0
  %x5.i275 = insertvalue { i64, i2 } %xo.i274, i2 0, 1
  br label %ctd_ifa.i290

elsea.i283:                                       ; preds = %while_body.i272
  %xn.i277 = icmp ult i8 %xi.i268, %xl.i270
  %xoa.i278 = add i64 %a12.i266, 1
  %xp.i279 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i278, 0
  %x7.i280 = insertvalue { i64, i2 } %xp.i279, i2 1, 1
  %x6.i281 = insertvalue { i64, i2 } %xp.i279, i2 -1, 1
  %x8.i282 = select i1 %xn.i277, { i64, i2 } %x6.i281, { i64, i2 } %x7.i280
  br label %ctd_ifa.i290

ctd_ifa.i290:                                     ; preds = %elsea.i283, %thena.i276
  %x9.i284 = phi { i64, i2 } [ %x5.i275, %thena.i276 ], [ %x8.i282, %elsea.i283 ]
  %a1.i285 = extractvalue { i64, i2 } %x9.i284, 0
  %a2.i286 = extractvalue { i64, i2 } %x9.i284, 1
  %xga.i287 = icmp slt i64 %a1.i285, %la.l.i263
  %x3.i288 = icmp eq i2 %a2.i286, 0
  %x4.i289 = and i1 %xga.i287, %x3.i288
  br i1 %x4.i289, label %while_body.i272, label %while_end.i291

while_end.i291:                                   ; preds = %ctd_ifa.i290
  switch i2 %a2.i286, label %elsee [
    i2 -1, label %thene
    i2 0, label %Sorting_Strings_strcmp_impl.exit297
  ]

Sorting_Strings_strcmp_impl.exit297:              ; preds = %elseb, %while_end.i291
  %x10.i292 = icmp slt i64 %r.unpack, %21
  br i1 %x10.i292, label %thene, label %elsee

thene:                                            ; preds = %while_end.i291, %Sorting_Strings_strcmp_impl.exit297
  %r.elt.i250 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 0
  %r.unpack2.elt.i252 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 0
  %23 = bitcast i64* %r.elt.i250 to <2 x i64>*
  %24 = load <2 x i64>, <2 x i64>* %23, align 8
  %r.unpack2.elt4.i254 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 1
  %25 = bitcast i8** %r.unpack2.elt4.i254 to i64*
  %r.unpack2.unpack522.i255 = load i64, i64* %25, align 8
  store i64 %r.unpack, i64* %r.elt.i250, align 8
  store i64 %r.unpack2.unpack, i64* %r.unpack2.elt.i252, align 8
  store i64 %1, i64* %25, align 8
  %26 = bitcast i64* %r.elt to <2 x i64>*
  store <2 x i64> %24, <2 x i64>* %26, align 8
  br label %ctd_ifb

elsee:                                            ; preds = %while_end.i291, %Sorting_Strings_strcmp_impl.exit297
  %xd.i214 = icmp sgt i64 %ra.unpack, %21
  %la.l.i215 = select i1 %xd.i214, i64 %21, i64 %ra.unpack
  %xga1.i216 = icmp sgt i64 %la.l.i215, 0
  br i1 %xga1.i216, label %while_body.i224.preheader, label %Sorting_Strings_strcmp_impl.exit249

while_body.i224.preheader:                        ; preds = %elsee
  br label %while_body.i224

while_body.i224:                                  ; preds = %while_body.i224.preheader, %ctd_ifa.i242
  %a12.i218 = phi i64 [ %a1.i237, %ctd_ifa.i242 ], [ 0, %while_body.i224.preheader ]
  %xh.i219 = getelementptr i8, i8* %ra.unpack8.unpack11, i64 %a12.i218
  %xi.i220 = load i8, i8* %xh.i219, align 1
  %xk.i221 = getelementptr i8, i8* %rc1.unpack28.unpack31, i64 %a12.i218
  %xl.i222 = load i8, i8* %xk.i221, align 1
  %xm.i223 = icmp eq i8 %xi.i220, %xl.i222
  br i1 %xm.i223, label %thena.i228, label %elsea.i235

thena.i228:                                       ; preds = %while_body.i224
  %xna.i225 = add i64 %a12.i218, 1
  %xo.i226 = insertvalue { i64, i2 } zeroinitializer, i64 %xna.i225, 0
  %x5.i227 = insertvalue { i64, i2 } %xo.i226, i2 0, 1
  br label %ctd_ifa.i242

elsea.i235:                                       ; preds = %while_body.i224
  %xn.i229 = icmp ult i8 %xi.i220, %xl.i222
  %xoa.i230 = add i64 %a12.i218, 1
  %xp.i231 = insertvalue { i64, i2 } zeroinitializer, i64 %xoa.i230, 0
  %x7.i232 = insertvalue { i64, i2 } %xp.i231, i2 1, 1
  %x6.i233 = insertvalue { i64, i2 } %xp.i231, i2 -1, 1
  %x8.i234 = select i1 %xn.i229, { i64, i2 } %x6.i233, { i64, i2 } %x7.i232
  br label %ctd_ifa.i242

ctd_ifa.i242:                                     ; preds = %elsea.i235, %thena.i228
  %x9.i236 = phi { i64, i2 } [ %x5.i227, %thena.i228 ], [ %x8.i234, %elsea.i235 ]
  %a1.i237 = extractvalue { i64, i2 } %x9.i236, 0
  %a2.i238 = extractvalue { i64, i2 } %x9.i236, 1
  %xga.i239 = icmp slt i64 %a1.i237, %la.l.i215
  %x3.i240 = icmp eq i2 %a2.i238, 0
  %x4.i241 = and i1 %xga.i239, %x3.i240
  br i1 %x4.i241, label %while_body.i224, label %while_end.i243

while_end.i243:                                   ; preds = %ctd_ifa.i242
  switch i2 %a2.i238, label %elsef [
    i2 -1, label %thenf
    i2 0, label %Sorting_Strings_strcmp_impl.exit249
  ]

Sorting_Strings_strcmp_impl.exit249:              ; preds = %elsee, %while_end.i243
  %x10.i244 = icmp slt i64 %ra.unpack, %21
  br i1 %x10.i244, label %thenf, label %elsef

thenf:                                            ; preds = %while_end.i243, %Sorting_Strings_strcmp_impl.exit249
  %r.elt.i202 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 0
  %27 = bitcast i64* %r.elt.i202 to <2 x i64>*
  %28 = load <2 x i64>, <2 x i64>* %27, align 8
  %r.unpack2.elt4.i206 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 1
  %29 = bitcast i8** %r.unpack2.elt4.i206 to i64*
  %r.unpack2.unpack522.i207 = load i64, i64* %29, align 8
  %30 = bitcast i64* %r.elt.i202 to <2 x i64>*
  store <2 x i64> %20, <2 x i64>* %30, align 8
  store i64 %22, i64* %29, align 8
  %31 = bitcast i64* %rc1.elt to <2 x i64>*
  store <2 x i64> %28, <2 x i64>* %31, align 8
  br label %ctd_ifb

elsef:                                            ; preds = %while_end.i243, %Sorting_Strings_strcmp_impl.exit249
  %r.elt.i190 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 0
  %r.unpack2.elt.i192 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 0
  %32 = bitcast i64* %r.elt.i190 to <2 x i64>*
  %33 = load <2 x i64>, <2 x i64>* %32, align 8
  %r.unpack2.elt4.i194 = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a1316, i64 %a1a319, i32 1, i32 1
  %34 = bitcast i8** %r.unpack2.elt4.i194 to i64*
  %r.unpack2.unpack522.i195 = load i64, i64* %34, align 8
  store i64 %ra.unpack, i64* %r.elt.i190, align 8
  store i64 %ra.unpack8.unpack, i64* %r.unpack2.elt.i192, align 8
  store i64 %0, i64* %34, align 8
  %35 = bitcast i64* %ra.elt to <2 x i64>*
  store <2 x i64> %33, <2 x i64>* %35, align 8
  br label %ctd_ifb

ctd_ifb:                                          ; preds = %thene, %elsef, %thenf, %thenc, %elsed, %thend
  %.sink.in = phi i8** [ %r.unpack2.elt4, %thene ], [ %ra.unpack8.elt10, %elsef ], [ %rc1.unpack28.elt30, %thenf ], [ %ra.unpack8.elt10, %thenc ], [ %r.unpack2.elt4, %elsed ], [ %rc.unpack59.elt61, %thend ]
  %r.unpack2.unpack522.i255.sink = phi i64 [ %r.unpack2.unpack522.i255, %thene ], [ %r.unpack2.unpack522.i195, %elsef ], [ %r.unpack2.unpack522.i207, %thenf ], [ %r.unpack2.unpack522.i, %thenc ], [ %r.unpack2.unpack522.i183, %elsed ], [ %r.unpack2.unpack522.i171, %thend ]
  %.sink = bitcast i8** %.sink.in to i64*
  store i64 %r.unpack2.unpack522.i255.sink, i64* %.sink, align 8
  %xw2 = tail call { { i64, { i64, i8* } }*, i64 } @Sorting_Introsort_str_sort_qs_partition_impl(i64 %xia, i64 %a1b312, i64 %a1a319, { i64, { i64, i8* } }* nonnull %a1316)
  %a = extractvalue { { i64, { i64, i8* } }*, i64 } %xw2, 0
  %b = extractvalue { { i64, { i64, i8* } }*, i64 } %xw2, 1
  %xza = add i64 %a2b327, -1
  %ya2 = insertvalue { i64, i64 } zeroinitializer, i64 %b, 0
  %tmpga = insertvalue { i64, i64 } %ya2, i64 %xza, 1
  %yb = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %a1a319, 0
  %tmpha = insertvalue { i64, { i64, i64 } } %yb, { i64, i64 } %tmpga, 1
  %yc = insertvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } zeroinitializer, { i64, { i64, i8* } }* %a, 0
  %yd = insertvalue { { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %yc, { i64, { i64, i64 } } %tmpha, 1
  %yaa = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_introsort_qs_aux_impl_f_04889284({ { i64, { i64, i8* } }*, { i64, { i64, i64 } } } %yd)
  %xca = sub i64 %a1b312, %b
  %xd = icmp sgt i64 %xca, 16
  br i1 %xd, label %then, label %ctd_if

then.i:                                           ; preds = %then
  %xa.i.i = add i64 %a1b312, -1
  %x41.i.i = icmp sgt i64 %xa.i.i, %a1a319
  br i1 %x41.i.i, label %while_body.i.i.preheader, label %Sorting_Introsort_str_sort_heapify_btu_impl.exit.i

while_body.i.i.preheader:                         ; preds = %then.i
  br label %while_body.i.i

while_body.i.i:                                   ; preds = %while_body.i.i.preheader, %while_body.i.i
  %a113.i.i = phi { i64, { i64, i8* } }* [ %xca.i.i, %while_body.i.i ], [ %a1316, %while_body.i.i.preheader ]
  %x32.i.i = phi i64 [ %xba.i.i, %while_body.i.i ], [ %xa.i.i, %while_body.i.i.preheader ]
  %xba.i.i = add i64 %x32.i.i, -1
  %xca.i.i = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_sift_down_impl(i64 %a1a319, i64 %a1b312, i64 %xba.i.i, { i64, { i64, i8* } }* %a113.i.i) #3
  %x4.i.i = icmp sgt i64 %xba.i.i, %a1a319
  br i1 %x4.i.i, label %while_body.i.i, label %Sorting_Introsort_str_sort_heapify_btu_impl.exit.i

Sorting_Introsort_str_sort_heapify_btu_impl.exit.i: ; preds = %while_body.i.i, %then.i
  %a11.lcssa.i.i = phi { i64, { i64, i8* } }* [ %a1316, %then.i ], [ %xca.i.i, %while_body.i.i ]
  %xda.i = add i64 %a1a319, 1
  %x41.i = icmp slt i64 %xda.i, %a1b312
  br i1 %x41.i, label %while_body.i128.preheader, label %ctd_if

while_body.i128.preheader:                        ; preds = %Sorting_Introsort_str_sort_heapify_btu_impl.exit.i
  br label %while_body.i128

while_body.i128:                                  ; preds = %while_body.i128.preheader, %while_body.i128
  %a113.i = phi { i64, { i64, i8* } }* [ %xg.i, %while_body.i128 ], [ %a11.lcssa.i.i, %while_body.i128.preheader ]
  %a22.i = phi i64 [ %xda1.i, %while_body.i128 ], [ %a1b312, %while_body.i128.preheader ]
  %xda1.i = add nsw i64 %a22.i, -1
  %r.elt.i.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113.i, i64 %a1a319, i32 0
  %36 = bitcast i64* %r.elt.i.i to <2 x i64>*
  %37 = load <2 x i64>, <2 x i64>* %36, align 8
  %r.unpack2.elt4.i.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113.i, i64 %a1a319, i32 1, i32 1
  %38 = bitcast i8** %r.unpack2.elt4.i.i to i64*
  %r.unpack2.unpack522.i.i = load i64, i64* %38, align 8
  %ra.elt.i.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113.i, i64 %xda1.i, i32 0
  %39 = bitcast i64* %ra.elt.i.i to <2 x i64>*
  %40 = load <2 x i64>, <2 x i64>* %39, align 8
  %ra.unpack8.elt10.i.i = getelementptr inbounds { i64, { i64, i8* } }, { i64, { i64, i8* } }* %a113.i, i64 %xda1.i, i32 1, i32 1
  %41 = bitcast i8** %ra.unpack8.elt10.i.i to i64*
  %ra.unpack8.unpack1117.i.i = load i64, i64* %41, align 8
  %42 = bitcast i64* %r.elt.i.i to <2 x i64>*
  store <2 x i64> %40, <2 x i64>* %42, align 8
  store i64 %ra.unpack8.unpack1117.i.i, i64* %38, align 8
  %43 = bitcast i64* %ra.elt.i.i to <2 x i64>*
  store <2 x i64> %37, <2 x i64>* %43, align 8
  store i64 %r.unpack2.unpack522.i.i, i64* %41, align 8
  %xg.i = tail call { i64, { i64, i8* } }* @Sorting_Introsort_str_sort_sift_down_impl(i64 %a1a319, i64 %xda1.i, i64 %a1a319, { i64, { i64, i8* } }* %a113.i) #3
  %x4.i127 = icmp slt i64 %xda.i, %xda1.i
  br i1 %x4.i127, label %while_body.i128, label %ctd_if

ctd_if:                                           ; preds = %ctd_ifb, %while_body.i128, %start, %Sorting_Introsort_str_sort_heapify_btu_impl.exit.i
  %x15 = phi { i64, { i64, i8* } }* [ %a11.lcssa.i.i, %Sorting_Introsort_str_sort_heapify_btu_impl.exit.i ], [ %a1308, %start ], [ %xg.i, %while_body.i128 ], [ %yaa, %ctd_ifb ]
  ret { i64, { i64, i8* } }* %x15
}

; Function Attrs: nounwind
define i64* @Sorting_Introsort_unat_sort_introsort_qs_aux_impl_f_04869164({ i64*, { i64, { i64, i64 } } } %x) local_unnamed_addr #3 {
start:
  %a135 = extractvalue { i64*, { i64, { i64, i64 } } } %x, 0
  %xaa36 = extractvalue { i64*, { i64, { i64, i64 } } } %x, 1
  %a1a37 = extractvalue { i64, { i64, i64 } } %xaa36, 0
  %xba38 = extractvalue { i64, { i64, i64 } } %xaa36, 1
  %a1b39 = extractvalue { i64, i64 } %xba38, 0
  %xca41 = sub i64 %a1b39, %a1a37
  %xd42 = icmp sgt i64 %xca41, 16
  br i1 %xd42, label %then.lr.ph, label %ctd_if

then.lr.ph:                                       ; preds = %start
  %a2b40 = extractvalue { i64, i64 } %xba38, 1
  %xja = add i64 %a1b39, -1
  br label %then

then:                                             ; preds = %then.lr.ph, %Sorting_Introsort_unat_sort_qs_partition_impl.exit
  %xca47 = phi i64 [ %xca41, %then.lr.ph ], [ %xca, %Sorting_Introsort_unat_sort_qs_partition_impl.exit ]
  %a2b46 = phi i64 [ %a2b40, %then.lr.ph ], [ %xza, %Sorting_Introsort_unat_sort_qs_partition_impl.exit ]
  %a1a44 = phi i64 [ %a1a37, %then.lr.ph ], [ %a.lcssa.i, %Sorting_Introsort_unat_sort_qs_partition_impl.exit ]
  %a143 = phi i64* [ %a135, %then.lr.ph ], [ %yaa, %Sorting_Introsort_unat_sort_qs_partition_impl.exit ]
  %xe = icmp sgt i64 %a2b46, 0
  br i1 %xe, label %thena, label %then.i

thena:                                            ; preds = %then
  %xga = lshr i64 %xca47, 1
  %xh = add i64 %xga, %a1a44
  %xia = add i64 %a1a44, 1
  %xk = getelementptr i64, i64* %a143, i64 %xia
  %r = load i64, i64* %xk, align 8
  %xn = getelementptr i64, i64* %a143, i64 %xh
  %ra = load i64, i64* %xn, align 8
  %xq = icmp ult i64 %r, %ra
  %xx = getelementptr i64, i64* %a143, i64 %xja
  %rc = load i64, i64* %xx, align 8
  br i1 %xq, label %thenb, label %elseb

thenb:                                            ; preds = %thena
  %ya = icmp ult i64 %ra, %rc
  br i1 %ya, label %thenc, label %elsec

thenc:                                            ; preds = %thenb
  %x3.i = getelementptr i64, i64* %a143, i64 %a1a44
  %r.i = load i64, i64* %x3.i, align 8
  store i64 %ra, i64* %x3.i, align 8
  store i64 %r.i, i64* %xn, align 8
  br label %ctd_ifb

elsec:                                            ; preds = %thenb
  %yk = icmp ult i64 %r, %rc
  %x3.i1 = getelementptr i64, i64* %a143, i64 %a1a44
  %r.i2 = load i64, i64* %x3.i1, align 8
  br i1 %yk, label %thend, label %elsed

thend:                                            ; preds = %elsec
  store i64 %rc, i64* %x3.i1, align 8
  store i64 %r.i2, i64* %xx, align 8
  br label %ctd_ifb

elsed:                                            ; preds = %elsec
  store i64 %r, i64* %x3.i1, align 8
  store i64 %r.i2, i64* %xk, align 8
  br label %ctd_ifb

elseb:                                            ; preds = %thena
  %ya1 = icmp ult i64 %r, %rc
  br i1 %ya1, label %thene, label %elsee

thene:                                            ; preds = %elseb
  %x3.i10 = getelementptr i64, i64* %a143, i64 %a1a44
  %r.i11 = load i64, i64* %x3.i10, align 8
  store i64 %r, i64* %x3.i10, align 8
  store i64 %r.i11, i64* %xk, align 8
  br label %ctd_ifb

elsee:                                            ; preds = %elseb
  %yk1 = icmp ult i64 %ra, %rc
  %x3.i14 = getelementptr i64, i64* %a143, i64 %a1a44
  %r.i15 = load i64, i64* %x3.i14, align 8
  br i1 %yk1, label %thenf, label %elsef

thenf:                                            ; preds = %elsee
  store i64 %rc, i64* %x3.i14, align 8
  store i64 %r.i15, i64* %xx, align 8
  br label %ctd_ifb

elsef:                                            ; preds = %elsee
  store i64 %ra, i64* %x3.i14, align 8
  store i64 %r.i15, i64* %xn, align 8
  br label %ctd_ifb

ctd_ifb:                                          ; preds = %thene, %elsef, %thenf, %thenc, %elsed, %thend
  %xc.i18.pre-phi = phi i64* [ %x3.i10, %thene ], [ %x3.i14, %elsef ], [ %x3.i14, %thenf ], [ %x3.i, %thenc ], [ %x3.i1, %elsed ], [ %x3.i1, %thend ]
  %ra.i19 = load i64, i64* %xc.i18.pre-phi, align 8
  br label %while_start.i

while_start.i:                                    ; preds = %while_start.i, %ctd_ifb
  %s.i = phi i64 [ %x5.i, %while_start.i ], [ %xia, %ctd_ifb ]
  %x4.i20 = getelementptr i64, i64* %a143, i64 %s.i
  %r.i21 = load i64, i64* %x4.i20, align 8
  %xf.i = icmp ult i64 %r.i21, %ra.i19
  %x5.i = add i64 %s.i, 1
  br i1 %xf.i, label %while_start.i, label %while_starta.i.preheader

while_starta.i.preheader:                         ; preds = %while_start.i
  br label %while_starta.i

while_starta.i:                                   ; preds = %while_starta.i.preheader, %while_starta.i
  %s1.in.i = phi i64 [ %s1.i, %while_starta.i ], [ %a1b39, %while_starta.i.preheader ]
  %s1.i = add i64 %s1.in.i, -1
  %xe1.i = getelementptr i64, i64* %a143, i64 %s1.i
  %ra1.i = load i64, i64* %xe1.i, align 8
  %xh.i = icmp ult i64 %ra.i19, %ra1.i
  br i1 %xh.i, label %while_starta.i, label %while_enda.i

while_enda.i:                                     ; preds = %while_starta.i
  %x91.i = icmp slt i64 %s.i, %s1.i
  br i1 %x91.i, label %while_bodyb.i.preheader, label %Sorting_Introsort_unat_sort_qs_partition_impl.exit

while_bodyb.i.preheader:                          ; preds = %while_enda.i
  br label %while_bodyb.i

while_bodyb.i:                                    ; preds = %while_bodyb.i.preheader, %while_endd.i
  %ra.i.i22 = phi i64 [ %ra3.i, %while_endd.i ], [ %ra1.i, %while_bodyb.i.preheader ]
  %r.i.i23 = phi i64 [ %r2.i, %while_endd.i ], [ %r.i21, %while_bodyb.i.preheader ]
  %x83.i = phi i64 [ %s3.i, %while_endd.i ], [ %s1.i, %while_bodyb.i.preheader ]
  %a2.i = phi i64 [ %s2.i, %while_endd.i ], [ %s.i, %while_bodyb.i.preheader ]
  %x3.i.i24 = getelementptr i64, i64* %a143, i64 %a2.i
  %xc.i.i25 = getelementptr i64, i64* %a143, i64 %x83.i
  store i64 %ra.i.i22, i64* %x3.i.i24, align 8
  store i64 %r.i.i23, i64* %xc.i.i25, align 8
  %ra2.i = load i64, i64* %xc.i18.pre-phi, align 8
  br label %while_startc.i

while_startc.i:                                   ; preds = %while_startc.i, %while_bodyb.i
  %s2.in.i = phi i64 [ %s2.i, %while_startc.i ], [ %a2.i, %while_bodyb.i ]
  %s2.i = add i64 %s2.in.i, 1
  %xg1.i = getelementptr i64, i64* %a143, i64 %s2.i
  %r2.i = load i64, i64* %xg1.i, align 8
  %xm.i = icmp ult i64 %r2.i, %ra2.i
  br i1 %xm.i, label %while_startc.i, label %while_startd.i.preheader

while_startd.i.preheader:                         ; preds = %while_startc.i
  br label %while_startd.i

while_startd.i:                                   ; preds = %while_startd.i.preheader, %while_startd.i
  %s3.in.i = phi i64 [ %s3.i, %while_startd.i ], [ %x83.i, %while_startd.i.preheader ]
  %s3.i = add i64 %s3.in.i, -1
  %xl1.i = getelementptr i64, i64* %a143, i64 %s3.i
  %ra3.i = load i64, i64* %xl1.i, align 8
  %xo.i = icmp ult i64 %ra2.i, %ra3.i
  br i1 %xo.i, label %while_startd.i, label %while_endd.i

while_endd.i:                                     ; preds = %while_startd.i
  %x9.i = icmp slt i64 %s2.i, %s3.i
  br i1 %x9.i, label %while_bodyb.i, label %Sorting_Introsort_unat_sort_qs_partition_impl.exit

Sorting_Introsort_unat_sort_qs_partition_impl.exit: ; preds = %while_endd.i, %while_enda.i
  %a.lcssa.i = phi i64 [ %s.i, %while_enda.i ], [ %s2.i, %while_endd.i ]
  %xza = add i64 %a2b46, -1
  %ya2 = insertvalue { i64, i64 } zeroinitializer, i64 %a.lcssa.i, 0
  %tmpga = insertvalue { i64, i64 } %ya2, i64 %xza, 1
  %yb = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %a1a44, 0
  %tmpha = insertvalue { i64, { i64, i64 } } %yb, { i64, i64 } %tmpga, 1
  %yc = insertvalue { i64*, { i64, { i64, i64 } } } zeroinitializer, i64* %a143, 0
  %yd = insertvalue { i64*, { i64, { i64, i64 } } } %yc, { i64, { i64, i64 } } %tmpha, 1
  %yaa = tail call i64* @Sorting_Introsort_unat_sort_introsort_qs_aux_impl_f_04869164({ i64*, { i64, { i64, i64 } } } %yd)
  %xca = sub i64 %a1b39, %a.lcssa.i
  %xd = icmp sgt i64 %xca, 16
  br i1 %xd, label %then, label %ctd_if

then.i:                                           ; preds = %then
  %xa.i.i = add i64 %a1b39, -1
  %x41.i.i = icmp sgt i64 %xa.i.i, %a1a44
  br i1 %x41.i.i, label %while_body.i.i.preheader, label %Sorting_Introsort_unat_sort_heapify_btu_impl.exit.i

while_body.i.i.preheader:                         ; preds = %then.i
  br label %while_body.i.i

while_body.i.i:                                   ; preds = %while_body.i.i.preheader, %while_body.i.i
  %a113.i.i = phi i64* [ %xca.i.i, %while_body.i.i ], [ %a143, %while_body.i.i.preheader ]
  %x32.i.i = phi i64 [ %xba.i.i, %while_body.i.i ], [ %xa.i.i, %while_body.i.i.preheader ]
  %xba.i.i = add i64 %x32.i.i, -1
  %xca.i.i = tail call i64* @Sorting_Introsort_unat_sort_sift_down_impl(i64 %a1a44, i64 %a1b39, i64 %xba.i.i, i64* %a113.i.i) #3
  %x4.i.i = icmp sgt i64 %xba.i.i, %a1a44
  br i1 %x4.i.i, label %while_body.i.i, label %Sorting_Introsort_unat_sort_heapify_btu_impl.exit.i

Sorting_Introsort_unat_sort_heapify_btu_impl.exit.i: ; preds = %while_body.i.i, %then.i
  %a11.lcssa.i.i = phi i64* [ %a143, %then.i ], [ %xca.i.i, %while_body.i.i ]
  %xda.i = add i64 %a1a44, 1
  %x41.i = icmp slt i64 %xda.i, %a1b39
  br i1 %x41.i, label %while_body.i.preheader, label %ctd_if

while_body.i.preheader:                           ; preds = %Sorting_Introsort_unat_sort_heapify_btu_impl.exit.i
  br label %while_body.i

while_body.i:                                     ; preds = %while_body.i.preheader, %while_body.i
  %a113.i = phi i64* [ %xg.i, %while_body.i ], [ %a11.lcssa.i.i, %while_body.i.preheader ]
  %a22.i = phi i64 [ %xda1.i, %while_body.i ], [ %a1b39, %while_body.i.preheader ]
  %xda1.i = add nsw i64 %a22.i, -1
  %x3.i.i = getelementptr i64, i64* %a113.i, i64 %a1a44
  %r.i.i = load i64, i64* %x3.i.i, align 8
  %xc.i.i = getelementptr i64, i64* %a113.i, i64 %xda1.i
  %ra.i.i = load i64, i64* %xc.i.i, align 8
  store i64 %ra.i.i, i64* %x3.i.i, align 8
  store i64 %r.i.i, i64* %xc.i.i, align 8
  %xg.i = tail call i64* @Sorting_Introsort_unat_sort_sift_down_impl(i64 %a1a44, i64 %xda1.i, i64 %a1a44, i64* %a113.i) #3
  %x4.i = icmp slt i64 %xda.i, %xda1.i
  br i1 %x4.i, label %while_body.i, label %ctd_if

ctd_if:                                           ; preds = %Sorting_Introsort_unat_sort_qs_partition_impl.exit, %while_body.i, %start, %Sorting_Introsort_unat_sort_heapify_btu_impl.exit.i
  %x15 = phi i64* [ %a11.lcssa.i.i, %Sorting_Introsort_unat_sort_heapify_btu_impl.exit.i ], [ %a135, %start ], [ %xg.i, %while_body.i ], [ %yaa, %Sorting_Introsort_unat_sort_qs_partition_impl.exit ]
  ret i64* %x15
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1) #4

attributes #0 = { norecurse nounwind }
attributes #1 = { norecurse nounwind readonly }
attributes #2 = { norecurse nounwind readnone }
attributes #3 = { nounwind }
attributes #4 = { argmemonly nounwind }

!0 = !{!1}
!1 = distinct !{!1, !2}
!2 = distinct !{!2, !"LVerDomain"}
!3 = !{!4}
!4 = distinct !{!4, !2}
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.isvectorized", i32 1}
!7 = distinct !{!7, !6}
!8 = !{!9}
!9 = distinct !{!9, !10}
!10 = distinct !{!10, !"LVerDomain"}
!11 = !{!12}
!12 = distinct !{!12, !10}
!13 = distinct !{!13, !6}
!14 = distinct !{!14, !6}
!15 = !{!16}
!16 = distinct !{!16, !17}
!17 = distinct !{!17, !"LVerDomain"}
!18 = !{!19}
!19 = distinct !{!19, !17}
!20 = distinct !{!20, !6}
!21 = distinct !{!21, !6}
