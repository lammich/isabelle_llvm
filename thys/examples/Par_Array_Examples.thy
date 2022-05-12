(** TODO: Maybe some nice parallel examples directly with VCG here?
  currently, all more complex stuff is done via Sepref, and there's 
  only the minimum required VCG setup!
*)
theory Par_Array_Examples
imports "../sepref/IICF/Impl/IICF_Array"
begin

  (* TODO: Move *)

  lemma curry_mono[refine_mono]: 
    "\<lbrakk>\<And>ab. f ab \<le> f' ab\<rbrakk> \<Longrightarrow> curry f a b \<le> curry f' a b"
    unfolding curry_def
    by refine_mono
  
  (* Monadifier setup *)
  lemma curry_arity[sepref_monadify_arity]: "curry \<equiv> \<lambda>\<^sub>2f a b. SP curry$(\<lambda>\<^sub>2ab. f$ab)$a$b"
    by (simp add: curry_def)
  
  lemma curry_comb[sepref_monadify_comb]:  
    "curry$f$a$b = Refine_Basic.bind$(EVAL$a)$(\<lambda>\<^sub>2a. Refine_Basic.bind$(EVAL$b)$(\<lambda>\<^sub>2b. SP curry$f$a$b))"
    by simp
  
  lemma curry_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>ab. flat_ge (f ab) (f' ab)\<rbrakk> \<Longrightarrow> flat_ge (curry f a b) (curry f' a b)"
    unfolding curry_def
    by refine_mono
  
  lemma curry_rule[refine_vcg]:
    assumes "f (a,b) \<le> SPEC P"
    shows "curry f a b \<le> SPEC P"  
    using assms(1) unfolding curry_def
    apply auto
    done

  lemma curry_refine[refine]:
    assumes [refine]: "f' (a',b') \<le> \<Down>R (f (a,b))"
    shows "curry f' a' b' \<le>\<Down>R (curry f a b)"
    unfolding curry_def
    by refine_rcg

    
  thm sepref_comb_rules  
    
  lemma hn_curry_aux:
    assumes "\<And>ab abi. \<lbrakk> ab=(a,b); CP_assm (abi=(ai,bi)) \<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt (A\<times>\<^sub>aB) ab abi ** F) (fi abi) (hn_ctxt (A'\<times>\<^sub>aB') ab abi ** F') R (CP' abi) (f ab)"
    assumes "CP_simplify (CP' (ai,bi)) CP"
    shows "hn_refine (A a ai ** B b bi ** F) (fi (ai,bi)) (A' a ai ** B' b bi ** F') R CP (f (a,b))"
    using assms
    apply (clarsimp simp: CP_assm_def CP_simplify_def hn_ctxt_def)
    apply (rule hn_refine_cons_cp[rotated])
    apply (rprems; simp)
    apply simp_all
    done
  

  lemma hn_curry[sepref_comb_rules]:  
    assumes FR1: "\<Gamma> \<turnstile> hn_ctxt A a ai ** hn_ctxt B b bi ** F"
    assumes HN: "\<And>ab abi. \<lbrakk> ab=(a,b); CP_assm (abi=(ai,bi)) \<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt (A\<times>\<^sub>aB) ab abi ** F) (fi abi) (\<Gamma>' ab abi) R (CP' abi) (f ab)"
    assumes FR2: "\<And>ab abi. \<Gamma>' ab abi \<turnstile> hn_ctxt (A'\<times>\<^sub>aB') ab abi ** F'"
    assumes CP: "CP_simplify (CP' (ai,bi)) CP"
    shows "hn_refine \<Gamma> (fi (ai,bi)) (hn_ctxt A' a ai ** hn_ctxt B' b bi ** F') R CP (curry$(\<lambda>\<^sub>2ab. f ab)$a$b)"
    apply simp
    apply (rule hn_refine_cons_cp[rotated])
    apply (rule HN[simplified])
    apply simp
    apply (simp add: CP_assm_def)
    using FR2[of "(a,b)" "(ai,bi)", unfolded hn_ctxt_def, simplified] apply (simp add: hn_ctxt_def)
    apply simp
    using CP apply (simp add: CP_defs)
    using FR1 apply (simp add: hn_ctxt_def)
    done
    


  declare [[llc_compile_par_call=true]]

  locale map_reduce =
    fixes f :: "'a \<Rightarrow> 'b::monoid_add"
    fixes A B
    fixes fi :: "'ai::llvm_rep \<Rightarrow> 'bi::llvm_rep llM"
    fixes addi zi
    assumes [sepref_fr_rules]: 
      "(fi,RETURN o f)\<in>A\<^sup>k \<rightarrow>\<^sub>a B"
      "(uncurry addi, uncurry (RETURN oo (+)))\<in>B\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a B"
      "(uncurry0 zi, uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a B"
    assumes AB_pure[safe_constraint_rules]: "is_pure A" "is_pure B"
    
    
    notes [[sepref_register_adhoc f "(+)::'b \<Rightarrow> _" "0::'b"]]
    notes [sepref_frame_free_rules] = AB_pure[THEN mk_free_is_pure]
  begin

    abbreviation threshold where "threshold \<equiv> 10000::nat"

    definition "idx_fold xs n \<equiv> doN {
      ASSERT (n=length xs);
      (_,a) \<leftarrow> WHILEIT (\<lambda>(i,a). i\<le>n \<and> a = sum_list (map f (take i xs))) (\<lambda>(i,a). i<n) (\<lambda>(i,a). doN { 
        ASSERT (i<n);
        RETURN (i+1, a + (f (xs!i)))
      }) (0,0);
      RETURN a
    }"
    
    lemma idx_fold_rule[refine_vcg]: "n=length xs \<Longrightarrow> idx_fold xs n \<le> SPEC (\<lambda>r. r = sum_list (map f xs))"
      unfolding idx_fold_def
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). n-i)"])
      by (auto simp: take_Suc_conv_app_nth)
      
    sepref_register idx_fold  
      
      
    find_theorems array_slice_assn  
      
    sepref_def idx_fold_impl [] is "uncurry (PR_CONST idx_fold)" :: "(array_slice_assn A)\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a B" 
      unfolding idx_fold_def PR_CONST_def
      apply (annot_snat_const "TYPE(64)")
      by sepref_dbg_keep
      
    term WITH_SPLIT  
    
    find_theorems hn_invalid CP_cond
    
    
    definition "idx_fold_par xs n \<equiv> doN {
      ASSERT (n=length xs);
      curry (RECT (\<lambda>idx_fold_par (xs,n). do {
        ASSERT (n = length xs);
        if n \<le> threshold then
          idx_fold xs n
        else
          WITH_SPLIT_ro threshold xs (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
            let n\<^sub>1 = threshold;
            let n\<^sub>2 = n - threshold;
            a\<^sub>1 \<leftarrow> idx_fold xs\<^sub>1 n\<^sub>1;
            a\<^sub>2 \<leftarrow> curry idx_fold_par xs\<^sub>2 n\<^sub>2;
             
            RETURN (a\<^sub>1+a\<^sub>2)
          })
      })) xs n
    }"
    
    lemma "n=length xs \<Longrightarrow> idx_fold_par xs n \<le> RETURN (sum_list (map f xs))"
      unfolding idx_fold_par_def
      supply R = RECT_rule[where 
            pre="\<lambda>(xs,n). n=length xs" 
        and M="\<lambda>(xs,n). RETURN (sum_list (map f xs))"
        and V="measure (\<lambda>(_,n). n)"
      , THEN order_trans]
      unfolding Let_def curry_def
      apply (refine_vcg R)
      
      apply auto
      apply (rule order_trans, rprems)
      apply auto
      done
      

    sepref_def idx_fold_par_impl [] is "uncurry (PR_CONST idx_fold_par)" :: "(array_slice_assn A)\<^sup>k *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a B" 
      unfolding idx_fold_par_def PR_CONST_def
      apply (annot_snat_const "TYPE(64)")
      supply [sepref_comb_rules] = hn_RECT'[where Rx'="IICF_Array.array_slice_assn A \<times>\<^sub>a snat_assn"]
      by sepref

  end  
     
  
  global_interpretation map_reduce 
  xxx, ctd here. Instantiate to something meaningful!
   
      
  
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
