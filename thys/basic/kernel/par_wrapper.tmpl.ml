(* Generated code, do not modify *)
(* Generated from par_wrapper.tmpl.ll on Thu 16 Sep 10:43:07 BST 2021 by peter *)
structure LLVM_Builder_templates = struct


fun mk_clT resT argT = "{" ^ resT ^ " *, " ^ argT ^ "}"

fun mk_par_wrapper uid resT fname argT = let
  val clT = mk_clT resT argT
  val wname = "__isabelle_llvm_par_wrapper_" ^ uid ^ ""
in (wname,
"\n" ^
"define void @" ^ wname ^ " (i8 * %clpv) {\n" ^
"\n" ^
"  %clp = bitcast i8* %clpv to " ^ clT ^ " *\n" ^
"\n" ^
"  %cl = load " ^ clT ^ ", " ^ clT ^ " *%clp\n" ^
"\n" ^
"  %resp = extractvalue " ^ clT ^ " %cl, 0\n" ^
"  %arg = extractvalue " ^ clT ^ " %cl, 1\n" ^
"\n" ^
"  %res = call " ^ resT ^ " @" ^ fname ^ " (" ^ argT ^ " %arg)\n" ^
"\n" ^
"  store " ^ resT ^ " %res, " ^ resT ^ " *%resp\n" ^
"\n" ^
"  ret void\n" ^
"}\n" ^
"\n" ^
"")
end


fun mk_par_call uid resT1 resT2 f1 f2 argT1 argT2 = let
  val clT1 = mk_clT resT1 argT1
  val clT2 = mk_clT resT2 argT2
  val (w1name,w1text) = mk_par_wrapper ("" ^ uid ^ "_1") resT1 f1 argT1
  val (w2name,w2text) = mk_par_wrapper ("" ^ uid ^ "_2") resT2 f2 argT2
  val rpairT = "{" ^ resT1 ^ ", " ^ resT2 ^ "}"
  val pcname = "__isabelle_llvm_par_call_" ^ uid ^ ""
  val pctext =
"\n" ^
"define " ^ rpairT ^ " @" ^ pcname ^ "(" ^ argT1 ^ " %arg1, " ^ argT2 ^ " %arg2) {\n" ^
"  ; Build closure1\n" ^
"  %resp1 = alloca " ^ resT1 ^ "\n" ^
"\n" ^
"  %cl1a = insertvalue " ^ clT1 ^ " zeroinitializer, " ^ resT1 ^ "* %resp1, 0\n" ^
"  %cl1 = insertvalue " ^ clT1 ^ " %cl1a, " ^ argT1 ^ " %arg1, 1\n" ^
"\n" ^
"  %cl1p = alloca " ^ clT1 ^ "\n" ^
"  store " ^ clT1 ^ " %cl1, " ^ clT1 ^ "* %cl1p\n" ^
"\n" ^
"  ; Build closure2\n" ^
"  %resp2 = alloca " ^ resT2 ^ "\n" ^
"\n" ^
"  %cl2a = insertvalue " ^ clT2 ^ " zeroinitializer, " ^ resT2 ^ "* %resp2, 0\n" ^
"  %cl2 = insertvalue " ^ clT2 ^ " %cl2a, " ^ argT2 ^ " %arg2, 1\n" ^
"\n" ^
"  %cl2p = alloca " ^ clT2 ^ "\n" ^
"  store " ^ clT2 ^ " %cl2, " ^ clT2 ^ "* %cl2p\n" ^
"\n" ^
"  ; Invoke parallel\n" ^
"  %cl1pv = bitcast " ^ clT1 ^ "* %cl1p to i8*\n" ^
"  %cl2pv = bitcast " ^ clT2 ^ "* %cl2p to i8*\n" ^
"\n" ^
"  call void @isabelle_llvm_parallel (void (i8 *) *@" ^ w1name ^ ", void (i8 *) *@" ^ w2name ^ ", i8 * %cl1pv, i8 * %cl2pv)\n" ^
"\n" ^
"  ; Extract results\n" ^
"  %res1 = load " ^ resT1 ^ ", " ^ resT1 ^ "* %resp1\n" ^
"  %res2 = load " ^ resT2 ^ ", " ^ resT2 ^ "* %resp2\n" ^
"\n" ^
"  ; Assemble result\n" ^
"  %resa = insertvalue " ^ rpairT ^ " zeroinitializer, " ^ resT1 ^ " %res1, 0\n" ^
"  %res = insertvalue " ^ rpairT ^ " %resa, " ^ resT2 ^ " %res2, 1\n" ^
"\n" ^
"  ret " ^ rpairT ^ " %res\n" ^
"}\n" ^
""
in
  (pcname, w1text ^ w2text ^ pctext)
end

end (* struct LLVM_Builder_templates *)
