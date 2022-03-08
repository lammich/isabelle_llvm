(** TODO: Maybe some nice parallel examples directly with VCG here?
  currently, all more complex stuff is done via Sepref, and there's 
  only the minimum required VCG setup!
*)
theory Par_Array_Examples
imports "../sepref/IICF/Impl/IICF_Array"
begin
  declare [[llc_compile_par_call=true]]

  context fixes f :: "'a \<Rightarrow> 'a" begin

  fun abs_map where
    "abs_map xs = (
      if length xs \<le> 1 then map f xs 
      else let
        xs\<^sub>1 = take (length xs div 2) xs;
        xs\<^sub>2 = drop (length xs div 2) xs;
        xs\<^sub>1 = abs_map xs\<^sub>1;
        xs\<^sub>2 = abs_map xs\<^sub>2
      in
        xs\<^sub>1@xs\<^sub>2
      )"
    
    lemmas [simp del] = abs_map.simps  

      
    lemma "abs_map xs = map f xs"
      apply (induction xs rule: abs_map.induct)
      apply (subst abs_map.simps)
      apply (auto split: if_splits)
      by (metis atd_lem map_append)
    
    
    definition "map1 \<equiv> RECT (\<lambda>map1 (xs,n). doN {
      ASSERT (n = length xs);
      if length xs = 0 then RETURN xs
      else if length xs = 1 then doN {
        x \<leftarrow> mop_list_get xs 0;
        xs \<leftarrow> mop_list_set xs 0 (f x);
        RETURN xs
      } else doN {
        let m = n div 2;
        (_,xs) \<leftarrow> WITH_SPLIT m xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
          (xs\<^sub>1,xs\<^sub>2) \<leftarrow> nres_par map1 map1 (xs\<^sub>1,m) (xs\<^sub>2,n-m);
          RETURN ((),(xs\<^sub>1,xs\<^sub>2))
        });
        RETURN xs
      }
      })"  
      
    schematic_goal map1_unfold: "map1 = ?foo"
      unfolding map1_def
      apply (subst RECT_unfold)
      apply refine_mono
      unfolding map1_def[symmetric]
      ..
      
    lemma map_by_idx: "length xs = 1 \<Longrightarrow> xs[0:=f (xs!0)] = map f xs" by (cases xs) auto
      
    lemma aux1: "length xs\<^sub>1 = length (xs\<^sub>1 @ xs\<^sub>2) div 2 \<longleftrightarrow> length (xs\<^sub>1 @ xs\<^sub>2) div 2 = length xs\<^sub>1" by auto
    
    lemma "n=length xs \<Longrightarrow> map1 (xs,n) \<le> RETURN (map f xs)"  
      unfolding map1_def  
      apply (refine_vcg RECT_rule[where V="measure snd" and pre="\<lambda>(xs,n). n=length xs" and M="\<lambda>(xs,n). RETURN (map f xs)", THEN order_trans])
      apply simp
      apply simp
      apply simp
      apply simp
      apply simp
      apply simp
      apply (simp add: map_by_idx)
      apply simp
      
      apply (simp only: split prod.inject, elim conjE)
      apply (thin_tac "length a = length a" for a)
      apply (thin_tac "RECT _ = _")
      apply hypsubst
      apply (simp only: aux1)
      
      apply (rule order_trans, rprems)
      apply simp_all
      apply auto []
      apply (rule order_trans, rprems)
      apply auto
      by (metis div2_Suc_Suc length_0_conv nat.distinct(1) old.nat.exhaust)
    
    
    
    oops
    proof (induction xs arbitrary: n rule: abs_map.induct)
      case (1 xs)
      
      note IH1="1"(1)[of _ _ "length xs div 2", OF _ _ refl]
      
      note [simp] = \<open>n=length xs\<close>
      
      have aux1: "(xs,n) = (a,b) \<longleftrightarrow> a=xs \<and> b=n" for a b by auto
      
      show ?case
        apply (subst map1_unfold)
        apply (subst abs_map.simps)
        unfolding WITH_SPLIT_def
        apply refine_vcg
        apply simp
        apply simp
        apply simp
        apply simp
        apply simp
        apply (cases xs; simp)
        apply simp
        apply (subst (asm) aux1, elim conjE)
        apply (simp only:, hypsubst)
        apply (rule order_trans[OF IH1])
        apply simp
        apply simp
        apply simp
        apply refine_vcg
        
      
      
      
    qed
      
      
      
          
  end  

    
    
  context
    includes monad_syntax_M
  begin
  
  definition par_incr :: "8 word ptr \<times> 64 word \<Rightarrow> 8 word ptr llM"
  where [llvm_code]: "par_incr \<equiv> MMonad.REC (\<lambda>par_incr (p,n).
    if n=1 then doM {
      x \<leftarrow> array_nth p (0::64 word);
      x \<leftarrow> ll_udiv x 2;
      array_upd p (0::64 word) x;
      return p
    } else doM {
      i \<leftarrow> ll_sdiv n 2;
      (p\<^sub>1,p\<^sub>2) \<leftarrow> ars_split i p;
      llc_par par_incr par_incr (p\<^sub>1,i) (p\<^sub>2,n-i);
      ars_join p\<^sub>1 p\<^sub>2;
      return p
    })"
  
  end  
  
  export_llvm par_incr
  
  schematic_goal par_incr_unfold: "par_incr = ?foo"
    unfolding par_incr_def
    apply (subst MMonad.REC_unfold)
    apply pf_mono_prover
    unfolding par_incr_def[symmetric]
    ..
  
    
  lemma "llvm_htriple 
    (raw_array_slice_assn xs xsi ** snat_assn n ni ** \<up>(n=length xs)) 
    (par_incr (xsi,ni))
    (\<lambda>_. raw_array_slice_assn (abs_map (\<lambda>x. x div 2) xs) xsi)
    "
  proof (induction xs rule: abs_map.induct[where f="(\<lambda>x. x div 2)"])
    case (1 xs)
    show ?case
      apply (subst par_incr_unfold)
      apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
      apply vcg_monadify
      
      find_theorems pure_part LLVM_DS_NArray.array_slice_assn
      
      apply vcg
      apply vcg_rl
      apply vcg_try_solve
    
    
  qed
    
    
    unfolding par_incr_def
    apply (rule REC_rule[where V="measure nat" and P="\<lambda>t ()"])
    apply vcg
    apply pf_mono_prover
  
  
  
  
  
  
  
  
  lemma REC_rule: (* Needs annotation to be usable in automated setting! *)
    assumes WF: "wf V"
    assumes MONO: "M_mono_body B"
    assumes STEP: "\<And>D t x. \<lbrakk>\<And>t' x. (t',t)\<in>V \<Longrightarrow> htriple (P t' x ** F) (D x) (Q x) \<rbrakk> \<Longrightarrow> htriple (P t x ** F) (B D x) (Q x)"
    assumes INIT: "P' \<turnstile> P t x ** F"
    shows "htriple P' (MMonad.REC B x) (Q x)"
  proof -  
  
    have "htriple (P t x ** F) (MMonad.REC B x) (Q x)"
      using WF
      apply (induction t arbitrary: x)
      apply (subst MMonad.REC_unfold[OF MONO])
      by (rule STEP)
    thus ?thesis
      apply (rule cons_rule)
      subgoal using INIT unfolding entails_def by simp
      subgoal .
      .
  qed



  declare [[llc_compile_par_call=true]]

  find_theorems raw_array_slice_assn

  context
    includes monad_syntax_M
  begin

  definition [llvm_code]: ""
  
  
  
  definition [llvm_code]: "par_incr (p::8 word ptr) (n::64 word) \<equiv> MMonad.REC (\<lambda>par_incr (p,n).
    if n=1 then doM {
      x \<leftarrow> array_nth p (0::64 word);
      x \<leftarrow> ll_udiv x 2;
      array_upd p (0::64 word) x;
      return p
    } else doM {
      i \<leftarrow> ll_sdiv n 2;
      (p\<^sub>1,p\<^sub>2) \<leftarrow> ars_split i p;
      llc_par par_incr par_incr (p\<^sub>1,i) (p\<^sub>2,n-i);
      ars_join p\<^sub>1 p\<^sub>2;
      return p
    }) (p,n)
  "

  
  export_llvm par_incr
  
  lemma
    shows ""
  
  
  
  lemma "llvm_htriple 
    (raw_array_slice_assn xs xsi ** snat_assn n ni ** \<up>(n=length xs)) 
    (par_incr xsi ni)
    (\<lambda>_. raw_array_slice_assn (map (\<lambda>x. x div 2) xs) xsi)
    "
    unfolding par_incr_def
    apply (rule REC_rule[where V="measure nat" and P="\<lambda>t ()"])
    apply vcg
    apply pf_mono_prover
    
  
    find_theorems MMonad.REC 
    
  
  end



end
