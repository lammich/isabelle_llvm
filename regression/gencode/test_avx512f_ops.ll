; Generated by Isabelle/LLVM-shallow
target datalayout = "e-m:e-p:64:64:64-a:0:64-n8:16:32:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f16:16:16-f32:32:32-f64:64:64-f128:128:128"
target triple = "x86_64-pc-linux-gnu"



declare float @llvm.x86.avx512.vfmadd.f32(float, float, float, i32 immarg)
declare double @llvm.x86.avx512.vfmadd.f64(double, double, double, i32 immarg)
declare <4 x float> @llvm.x86.avx512.mask.sqrt.ss(<4 x float>, <4 x float>, <4 x float>, i8, i32 immarg)
declare <2 x double> @llvm.x86.avx512.mask.sqrt.sd(<2 x double>, <2 x double>, <2 x double>, i8, i32 immarg)
declare <4 x float> @llvm.x86.avx512.mask.add.ss.round(<4 x float>, <4 x float>, <4 x float>, i8, i32 immarg)
declare <4 x float> @llvm.x86.avx512.mask.div.ss.round(<4 x float>, <4 x float>, <4 x float>, i8, i32 immarg)
declare <4 x float> @llvm.x86.avx512.mask.mul.ss.round(<4 x float>, <4 x float>, <4 x float>, i8, i32 immarg)
declare <4 x float> @llvm.x86.avx512.mask.sub.ss.round(<4 x float>, <4 x float>, <4 x float>, i8, i32 immarg)
declare <2 x double> @llvm.x86.avx512.mask.add.sd.round(<2 x double>, <2 x double>, <2 x double>, i8, i32 immarg)
declare <2 x double> @llvm.x86.avx512.mask.div.sd.round(<2 x double>, <2 x double>, <2 x double>, i8, i32 immarg)
declare <2 x double> @llvm.x86.avx512.mask.mul.sd.round(<2 x double>, <2 x double>, <2 x double>, i8, i32 immarg)
declare <2 x double> @llvm.x86.avx512.mask.sub.sd.round(<2 x double>, <2 x double>, <2 x double>, i8, i32 immarg)

attributes #0 = { strictfp "target-features"="+avx512f" }

define float @avx512_32_add(i64 %x, float %a, float %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxa_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxb_ = call <4 x float> @llvm.x86.avx512.mask.add.ss.round (<4 x float> %mmx_, <4 x float> %mmxa_, <4 x float> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <4 x float> %mmxb_, i32 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxd_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxe_ = call <4 x float> @llvm.x86.avx512.mask.add.ss.round (<4 x float> %mmxc_, <4 x float> %mmxd_, <4 x float> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <4 x float> %mmxe_, i32 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxg_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxh_ = call <4 x float> @llvm.x86.avx512.mask.add.ss.round (<4 x float> %mmxf_, <4 x float> %mmxg_, <4 x float> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <4 x float> %mmxh_, i32 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxj_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxk_ = call <4 x float> @llvm.x86.avx512.mask.add.ss.round (<4 x float> %mmxi_, <4 x float> %mmxj_, <4 x float> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <4 x float> %mmxk_, i32 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi float [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi float [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi float [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret float %x7
}

define float @avx512_32_div(i64 %x, float %a, float %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxa_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxb_ = call <4 x float> @llvm.x86.avx512.mask.div.ss.round (<4 x float> %mmx_, <4 x float> %mmxa_, <4 x float> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <4 x float> %mmxb_, i32 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxd_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxe_ = call <4 x float> @llvm.x86.avx512.mask.div.ss.round (<4 x float> %mmxc_, <4 x float> %mmxd_, <4 x float> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <4 x float> %mmxe_, i32 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxg_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxh_ = call <4 x float> @llvm.x86.avx512.mask.div.ss.round (<4 x float> %mmxf_, <4 x float> %mmxg_, <4 x float> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <4 x float> %mmxh_, i32 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxj_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxk_ = call <4 x float> @llvm.x86.avx512.mask.div.ss.round (<4 x float> %mmxi_, <4 x float> %mmxj_, <4 x float> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <4 x float> %mmxk_, i32 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi float [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi float [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi float [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret float %x7
}

define float @avx512_32_mul(i64 %x, float %a, float %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxa_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxb_ = call <4 x float> @llvm.x86.avx512.mask.mul.ss.round (<4 x float> %mmx_, <4 x float> %mmxa_, <4 x float> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <4 x float> %mmxb_, i32 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxd_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxe_ = call <4 x float> @llvm.x86.avx512.mask.mul.ss.round (<4 x float> %mmxc_, <4 x float> %mmxd_, <4 x float> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <4 x float> %mmxe_, i32 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxg_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxh_ = call <4 x float> @llvm.x86.avx512.mask.mul.ss.round (<4 x float> %mmxf_, <4 x float> %mmxg_, <4 x float> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <4 x float> %mmxh_, i32 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxj_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxk_ = call <4 x float> @llvm.x86.avx512.mask.mul.ss.round (<4 x float> %mmxi_, <4 x float> %mmxj_, <4 x float> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <4 x float> %mmxk_, i32 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi float [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi float [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi float [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret float %x7
}

define float @avx512_32_sub(i64 %x, float %a, float %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxa_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxb_ = call <4 x float> @llvm.x86.avx512.mask.sub.ss.round (<4 x float> %mmx_, <4 x float> %mmxa_, <4 x float> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <4 x float> %mmxb_, i32 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxd_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxe_ = call <4 x float> @llvm.x86.avx512.mask.sub.ss.round (<4 x float> %mmxc_, <4 x float> %mmxd_, <4 x float> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <4 x float> %mmxe_, i32 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxg_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxh_ = call <4 x float> @llvm.x86.avx512.mask.sub.ss.round (<4 x float> %mmxf_, <4 x float> %mmxg_, <4 x float> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <4 x float> %mmxh_, i32 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxj_ = insertelement <4 x float> zeroinitializer, float %b, i32 0
    %mmxk_ = call <4 x float> @llvm.x86.avx512.mask.sub.ss.round (<4 x float> %mmxi_, <4 x float> %mmxj_, <4 x float> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <4 x float> %mmxk_, i32 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi float [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi float [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi float [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret float %x7
}

define double @avx512_64_add(i64 %x, double %a, double %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxa_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxb_ = call <2 x double> @llvm.x86.avx512.mask.add.sd.round (<2 x double> %mmx_, <2 x double> %mmxa_, <2 x double> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <2 x double> %mmxb_, i64 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxd_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxe_ = call <2 x double> @llvm.x86.avx512.mask.add.sd.round (<2 x double> %mmxc_, <2 x double> %mmxd_, <2 x double> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <2 x double> %mmxe_, i64 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxg_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxh_ = call <2 x double> @llvm.x86.avx512.mask.add.sd.round (<2 x double> %mmxf_, <2 x double> %mmxg_, <2 x double> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <2 x double> %mmxh_, i64 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxj_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxk_ = call <2 x double> @llvm.x86.avx512.mask.add.sd.round (<2 x double> %mmxi_, <2 x double> %mmxj_, <2 x double> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <2 x double> %mmxk_, i64 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi double [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi double [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi double [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret double %x7
}

define double @avx512_64_div(i64 %x, double %a, double %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxa_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxb_ = call <2 x double> @llvm.x86.avx512.mask.div.sd.round (<2 x double> %mmx_, <2 x double> %mmxa_, <2 x double> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <2 x double> %mmxb_, i64 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxd_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxe_ = call <2 x double> @llvm.x86.avx512.mask.div.sd.round (<2 x double> %mmxc_, <2 x double> %mmxd_, <2 x double> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <2 x double> %mmxe_, i64 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxg_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxh_ = call <2 x double> @llvm.x86.avx512.mask.div.sd.round (<2 x double> %mmxf_, <2 x double> %mmxg_, <2 x double> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <2 x double> %mmxh_, i64 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxj_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxk_ = call <2 x double> @llvm.x86.avx512.mask.div.sd.round (<2 x double> %mmxi_, <2 x double> %mmxj_, <2 x double> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <2 x double> %mmxk_, i64 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi double [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi double [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi double [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret double %x7
}

define double @avx512_64_mul(i64 %x, double %a, double %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxa_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxb_ = call <2 x double> @llvm.x86.avx512.mask.mul.sd.round (<2 x double> %mmx_, <2 x double> %mmxa_, <2 x double> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <2 x double> %mmxb_, i64 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxd_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxe_ = call <2 x double> @llvm.x86.avx512.mask.mul.sd.round (<2 x double> %mmxc_, <2 x double> %mmxd_, <2 x double> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <2 x double> %mmxe_, i64 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxg_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxh_ = call <2 x double> @llvm.x86.avx512.mask.mul.sd.round (<2 x double> %mmxf_, <2 x double> %mmxg_, <2 x double> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <2 x double> %mmxh_, i64 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxj_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxk_ = call <2 x double> @llvm.x86.avx512.mask.mul.sd.round (<2 x double> %mmxi_, <2 x double> %mmxj_, <2 x double> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <2 x double> %mmxk_, i64 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi double [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi double [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi double [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret double %x7
}

define double @avx512_64_sub(i64 %x, double %a, double %b) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxa_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxb_ = call <2 x double> @llvm.x86.avx512.mask.sub.sd.round (<2 x double> %mmx_, <2 x double> %mmxa_, <2 x double> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <2 x double> %mmxb_, i64 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxc_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxd_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxe_ = call <2 x double> @llvm.x86.avx512.mask.sub.sd.round (<2 x double> %mmxc_, <2 x double> %mmxd_, <2 x double> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <2 x double> %mmxe_, i64 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxf_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxg_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxh_ = call <2 x double> @llvm.x86.avx512.mask.sub.sd.round (<2 x double> %mmxf_, <2 x double> %mmxg_, <2 x double> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <2 x double> %mmxh_, i64 0
    br label %ctd_ifb

  elseb:
    %mmxi_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxj_ = insertelement <2 x double> zeroinitializer, double %b, i64 0
    %mmxk_ = call <2 x double> @llvm.x86.avx512.mask.sub.sd.round (<2 x double> %mmxi_, <2 x double> %mmxj_, <2 x double> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <2 x double> %mmxk_, i64 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi double [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi double [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi double [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret double %x7
}

define float @avx512_32_sqrt(i64 %x, float %a) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxa_ = call <4 x float> @llvm.x86.avx512.mask.sqrt.ss (<4 x float> %mmx_, <4 x float> %mmx_, <4 x float> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <4 x float> %mmxa_, i32 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxb_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxc_ = call <4 x float> @llvm.x86.avx512.mask.sqrt.ss (<4 x float> %mmxb_, <4 x float> %mmxb_, <4 x float> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <4 x float> %mmxc_, i32 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxd_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxe_ = call <4 x float> @llvm.x86.avx512.mask.sqrt.ss (<4 x float> %mmxd_, <4 x float> %mmxd_, <4 x float> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <4 x float> %mmxe_, i32 0
    br label %ctd_ifb

  elseb:
    %mmxf_ = insertelement <4 x float> zeroinitializer, float %a, i32 0
    %mmxg_ = call <4 x float> @llvm.x86.avx512.mask.sqrt.ss (<4 x float> %mmxf_, <4 x float> %mmxf_, <4 x float> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <4 x float> %mmxg_, i32 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi float [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi float [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi float [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret float %x7
}

define double @avx512_64_sqrt(i64 %x, double %a) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %mmx_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxa_ = call <2 x double> @llvm.x86.avx512.mask.sqrt.sd (<2 x double> %mmx_, <2 x double> %mmx_, <2 x double> zeroinitializer, i8 -1, i32 8)
    %x1 = extractelement <2 x double> %mmxa_, i64 0
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %mmxb_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxc_ = call <2 x double> @llvm.x86.avx512.mask.sqrt.sd (<2 x double> %mmxb_, <2 x double> %mmxb_, <2 x double> zeroinitializer, i8 -1, i32 10)
    %x2 = extractelement <2 x double> %mmxc_, i64 0
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %mmxd_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxe_ = call <2 x double> @llvm.x86.avx512.mask.sqrt.sd (<2 x double> %mmxd_, <2 x double> %mmxd_, <2 x double> zeroinitializer, i8 -1, i32 9)
    %x3 = extractelement <2 x double> %mmxe_, i64 0
    br label %ctd_ifb

  elseb:
    %mmxf_ = insertelement <2 x double> zeroinitializer, double %a, i64 0
    %mmxg_ = call <2 x double> @llvm.x86.avx512.mask.sqrt.sd (<2 x double> %mmxf_, <2 x double> %mmxf_, <2 x double> zeroinitializer, i8 -1, i32 11)
    %x4 = extractelement <2 x double> %mmxg_, i64 0
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi double [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi double [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi double [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret double %x7
}

define float @avx512_32_fmadd(i64 %x, float %a, float %b, float %c) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %x1 = call float @llvm.x86.avx512.vfmadd.f32 (float %a, float %b, float %c, i32 8)
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %x2 = call float @llvm.x86.avx512.vfmadd.f32 (float %a, float %b, float %c, i32 10)
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %x3 = call float @llvm.x86.avx512.vfmadd.f32 (float %a, float %b, float %c, i32 9)
    br label %ctd_ifb

  elseb:
    %x4 = call float @llvm.x86.avx512.vfmadd.f32 (float %a, float %b, float %c, i32 11)
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi float [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi float [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi float [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret float %x7
}

define double @avx512_64_fmadd(i64 %x, double %a, double %b, double %c) #0 {

  start:
    %tmp = icmp eq i64 %x, 0
    br i1 %tmp, label %then, label %else

  then:
    %x1 = call double @llvm.x86.avx512.vfmadd.f64 (double %a, double %b, double %c, i32 8)
    br label %ctd_if

  else:
    %tmpa = icmp eq i64 %x, 1
    br i1 %tmpa, label %thena, label %elsea

  thena:
    %x2 = call double @llvm.x86.avx512.vfmadd.f64 (double %a, double %b, double %c, i32 10)
    br label %ctd_ifa

  elsea:
    %tmpb = icmp eq i64 %x, 2
    br i1 %tmpb, label %thenb, label %elseb

  thenb:
    %x3 = call double @llvm.x86.avx512.vfmadd.f64 (double %a, double %b, double %c, i32 9)
    br label %ctd_ifb

  elseb:
    %x4 = call double @llvm.x86.avx512.vfmadd.f64 (double %a, double %b, double %c, i32 11)
    br label %ctd_ifb

  ctd_ifb:
    %x5 = phi double [ %x4, %elseb ], [ %x3, %thenb ]
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi double [ %x5, %ctd_ifb ], [ %x2, %thena ]
    br label %ctd_if

  ctd_if:
    %x7 = phi double [ %x6, %ctd_ifa ], [ %x1, %then ]
    ret double %x7
}