& structure LLVM_Builder_templates = struct
&
&
& fun mk_clT resT argT = "{$resT *, $argT}"
&
& fun mk_par_wrapper uid resT fname argT = let
&   val clT = mk_clT resT argT
&   val wname = "__isabelle_llvm_par_wrapper_$uid"
& in (wname,

define void @$wname (i8 * %clpv) {

  %clp = bitcast i8* %clpv to $clT *

  %cl = load $clT, $clT *%clp

  %resp = extractvalue $clT %cl, 0
  %arg = extractvalue $clT %cl, 1

  %res = call $resT @$fname ($argT %arg)

  store $resT %res, $resT *%resp

  ret void
}

& "")
& end
&
&
& fun mk_par_call uid resT1 resT2 f1 f2 argT1 argT2 = let
&   val clT1 = mk_clT resT1 argT1
&   val clT2 = mk_clT resT2 argT2
&   val (w1name,w1text) = mk_par_wrapper ("${uid}_1") resT1 f1 argT1
&   val (w2name,w2text) = mk_par_wrapper ("${uid}_2") resT2 f2 argT2
&   val rpairT = "{$resT1, $resT2}"
&   val pcname = "__isabelle_llvm_par_call_$uid"
&   val pctext =

define $rpairT @$pcname($argT1 %arg1, $argT2 %arg2) {
  ; Build closure1
  %resp1 = alloca $resT1

  %cl1a = insertvalue $clT1 zeroinitializer, $resT1* %resp1, 0
  %cl1 = insertvalue $clT1 %cl1a, $argT1 %arg1, 1

  %cl1p = alloca $clT1
  store $clT1 %cl1, $clT1* %cl1p

  ; Build closure2
  %resp2 = alloca $resT2

  %cl2a = insertvalue $clT2 zeroinitializer, $resT2* %resp2, 0
  %cl2 = insertvalue $clT2 %cl2a, $argT2 %arg2, 1

  %cl2p = alloca $clT2
  store $clT2 %cl2, $clT2* %cl2p

  ; Invoke parallel
  %cl1pv = bitcast $clT1* %cl1p to i8*
  %cl2pv = bitcast $clT2* %cl2p to i8*

  call void @isabelle_llvm_parallel (void (i8 *) *@$w1name, void (i8 *) *@$w2name, i8 * %cl1pv, i8 * %cl2pv)

  ; Extract results
  %res1 = load $resT1, $resT1* %resp1
  %res2 = load $resT2, $resT2* %resp2

  ; Assemble result
  %resa = insertvalue $rpairT zeroinitializer, $resT1 %res1, 0
  %res = insertvalue $rpairT %resa, $resT2 %res2, 1

  ret $rpairT %res
}
& ""
& in
&   (pcname, w1text ^ w2text ^ pctext)
& end
&
& end (* struct LLVM_Builder_templates *)
