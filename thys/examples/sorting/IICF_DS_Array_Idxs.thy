theory IICF_DS_Array_Idxs
imports "Isabelle_LLVM.LLVM_DS_NArray" "Isabelle_LLVM.Proto_IICF_EOArray" IICF_Shared_Lists
begin

  (* TODO: Move *)
  lemma entailsD1: "a=b \<Longrightarrow> a\<turnstile>b" by auto
  lemma entailsD2: "a=b \<Longrightarrow> b\<turnstile>a" by auto

    
  (* TODO: Move *)  
  lemma htriple_exI: "\<lbrakk>\<And>x. htriple (P x) c Q\<rbrakk> \<Longrightarrow> htriple (EXS x. P x) c Q"  
    unfolding htriple_def STATE_def by blast
    
  
  
  (* TODO: Move *)  
  lemma mk_assn_dr_prefix_eq[simp]: "mk_assn \<upharpoonleft>A = A" unfolding mk_assn_def dr_assn_prefix_def by simp
  lemma dr_prefix_mk_assn_eq[simp]: "\<upharpoonleft>(mk_assn A) = A" unfolding mk_assn_def dr_assn_prefix_def by simp
    
  
  (* TODO: Move *)  
  lemma sint_in_int_image_cnv: "snat_invar ii \<Longrightarrow> sint ii \<in> int ` s \<longleftrightarrow> snat ii \<in> s"  
    by (force simp add: cnv_snat_to_uint simp del: nat_uint_eq) 
    
  lemma nat_sint_to_snat: "nat (sint i) = snat i" unfolding snat_def by auto 

  lemma int_eq_sint_snat_eq_conv: "snat_invar ii \<Longrightarrow> int i = sint ii \<longleftrightarrow> i = snat ii"  
    apply (auto simp: snat_def)
    by (simp add: cnv_snat_to_uint(2))
    
    
  (* TODO: Move *)  
  lemma SOLVE_AUTO_DEFER_FALSE[simp]: "SOLVE_AUTO_DEFER False = False" unfolding SOLVE_AUTO_DEFER_def by simp 
      
    

(* TODO: Move *)    
lemma fri_ll_range_cong: 
  assumes "PRECOND (SOLVE_AUTO (I'=I))"
  assumes "PRECOND (SOLVE_AUTO (\<forall>i\<in>I. f' i = f i))"
  shows "\<upharpoonleft>(ll_range I) f p \<turnstile> \<upharpoonleft>(ll_range I') f' p"
  using assms
  by (simp add: PRECOND_def SOLVE_AUTO_def cong: ll_range_cong)


(* TODO: Move *)
lemma entails_pure_triv_simps[simp]: 
  "(\<box> \<turnstile> \<up>Q) \<longleftrightarrow> Q"  
  "(\<up>P \<turnstile> \<box>)"  
  "(\<up>P \<turnstile> \<up>Q) \<longleftrightarrow> (P \<longrightarrow> Q)"  
  by (auto simp: sep_algebra_simps entails_def)

lemma entails_exE: 
  assumes "\<And>x. P x \<turnstile> Q"
  shows "(EXS x. P x) \<turnstile> Q"  
  using assms by (auto simp: entails_def)

  
  
(* TODO: Move *)    
lemma list_assn_append2[simp]: "length xs\<^sub>2 = length ys\<^sub>2 
  \<Longrightarrow> \<upharpoonleft>(list_assn A) (xs\<^sub>1@xs\<^sub>2) (ys\<^sub>1@ys\<^sub>2) = (\<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"  
  by (smt (verit, del_insts) add.commute add_diff_cancel_right' length_append list_assn_append list_assn_neq_len(2) sep_conj_commute)
    

    
section \<open>Arrays with Partial Index Ownership\<close>  

context begin

  interpretation llvm_prim_mem_setup .

  definition "array_idxs_dr_assn \<equiv> mk_assn (\<lambda>xs p. 
    if xs=[] then \<box>
    else \<upharpoonleft>(ll_range (int ` sl_indexes' xs)) (sl_get xs o nat) p
  )"


  context
    notes [[coercion_enabled]]
  begin  
  (* For paper *)
  lemma "array_idxs_dr_assn = mk_assn (\<lambda>xs p. 
    if xs=[] then \<box>
    else \<upharpoonleft>(ll_range {i | i. i<length xs \<and> xs!i\<noteq>None}) (\<lambda>i. the (xs!nat i)) p
  )"
  proof -
    have 1: "int ` sl_indexes' xs = {int i | i. i<length xs \<and> xs!i\<noteq>None}" for xs :: "'a option list"
      unfolding sl_indexes_alt by auto
    thus ?thesis
      unfolding array_idxs_dr_assn_def sl_get_def
      apply (fo_rule cong refl)+
      apply (intro ext)
      apply (fo_rule ll_range_cong cong refl 1)+
      by auto
  
  qed
  end
  
  
  lemma array_idxs_empty[sep_algebra_simps]:
    "\<upharpoonleft>array_idxs_dr_assn [] p = \<box>"  
    unfolding array_idxs_dr_assn_def
    by auto
      
  lemma narray_assn_to_idxs: "\<upharpoonleft>narray_assn xs p = (\<upharpoonleft>array_idxs_dr_assn (sl_of_list xs) p ** \<upharpoonleft>array_base_assn (length xs) p)"  
    unfolding narray_assn_def LLVM_DS_Array.array_assn_def array_base_assn_def array_idxs_dr_assn_def
    apply (simp add: cong: ll_range_cong)
    apply (simp add: image_int_atLeastLessThan)
    by (auto simp: sep_algebra_simps comp_def split: list.splits)

  lemma array_slice_to_idxs: "\<upharpoonleft>LLVM_DS_NArray.array_slice_assn xs p = \<upharpoonleft>array_idxs_dr_assn (sl_of_list xs) p"
    unfolding LLVM_DS_NArray.array_slice_assn_def array_idxs_dr_assn_def
    by (simp add: image_int_atLeastLessThan cong: ll_range_cong)
    
    
  lemma array_idxs_join_eq:
    assumes "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)"
    shows "(\<upharpoonleft>array_idxs_dr_assn xs\<^sub>1 p ** \<upharpoonleft>array_idxs_dr_assn xs\<^sub>2 p) = \<upharpoonleft>array_idxs_dr_assn (sl_join xs\<^sub>1 xs\<^sub>2) p" 
  proof -
  
    have A: "i\<in>int`sl_indexes' xs\<^sub>1 \<Longrightarrow> sl_get xs\<^sub>1 (nat i) = sl_get (sl_join xs\<^sub>1 xs\<^sub>2) (nat i)" for i
      by (auto simp add: assms sl_get_join1)

    have B: "i\<in>int`sl_indexes' xs\<^sub>2 \<Longrightarrow> sl_get xs\<^sub>2 (nat i) = sl_get (sl_join xs\<^sub>1 xs\<^sub>2) (nat i)" for i
      by (auto simp add: assms sl_get_join2)
        
    show ?thesis  
      unfolding array_idxs_dr_assn_def
      using assms
      apply (clarsimp simp: sep_algebra_simps)
      apply (auto simp: sep_algebra_simps A B cong: ll_range_cong)
      
      apply (subst ll_range_merge)
      apply (auto dest!: sl_compat_idx_djD) []
      
      apply (fo_rule fun_cong arg_cong)+
      by auto
  qed  

  
  lemma array_idxs_join:
    "(\<upharpoonleft>array_idxs_dr_assn xs\<^sub>1 p ** \<upharpoonleft>array_idxs_dr_assn xs\<^sub>2 p ** \<up>(sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2))) 
      \<turnstile> \<upharpoonleft>array_idxs_dr_assn (sl_join xs\<^sub>1 xs\<^sub>2) p" 
    apply (clarsimp simp: pred_lift_move_front_simps entails_lift_extract_simps)  
    by (simp add: array_idxs_join_eq)
      

  lemma array_idxs_split_eq: 
    fixes ls xs
    defines "xs\<^sub>1 \<equiv> sl_split ls xs"
    defines "xs\<^sub>2 \<equiv> sl_split (-ls) xs"
    shows "\<upharpoonleft>array_idxs_dr_assn xs p = (\<upharpoonleft>array_idxs_dr_assn xs\<^sub>1 p ** \<upharpoonleft>array_idxs_dr_assn xs\<^sub>2 p)"
    apply (subst array_idxs_join_eq)
    unfolding assms
    by (auto simp: sl_compat_splitI sl_join_split_eq)
    
    
  lemma array_idxs_nth_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_idxs_dr_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i\<in>sl_indexes' xs))
    (array_nth p ii)
    (\<lambda>r. \<up>(r=sl_get xs i) ** \<upharpoonleft>array_idxs_dr_assn xs p)
  "
    apply (cases "xs=[]"; (simp add: array_idxs_empty)?)
    unfolding array_nth_def array_idxs_dr_assn_def snat.assn_def
    supply [simp] = sint_in_int_image_cnv nat_sint_to_snat
    by vcg

  lemma array_idxs_upd_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_idxs_dr_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i\<in>sl_indexes' xs))
    (array_upd p ii x)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_idxs_dr_assn (sl_put xs i x) p)
  "
    apply (cases "xs=[]"; (simp add: array_idxs_empty)?)
    unfolding array_upd_def array_idxs_dr_assn_def snat.assn_def
    supply [simp] = sint_in_int_image_cnv nat_sint_to_snat int_eq_sint_snat_eq_conv
    supply [fri_rules] = fri_ll_range_cong
    by vcg

    
    
  definition [llvm_inline]: "raw_array_swap p i j \<equiv> doM {
    vi \<leftarrow> array_nth p i;
    vj \<leftarrow> array_nth p j;
    p \<leftarrow> array_upd p i vj;
    p \<leftarrow> array_upd p j vi;
    Mreturn p
  }"  
  
  
  (* TODO: raw_array_swap should be implemented for more arrays. *)
  lemma raw_array_swap_idxs_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>array_idxs_dr_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji ** \<up>\<^sub>d(i\<in>sl_indexes' xs \<and> j\<in>sl_indexes' xs))
    (raw_array_swap p ii ji)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_idxs_dr_assn (swap xs i j) p)"
    unfolding raw_array_swap_def
    supply [simp] = sl_swap_aux
    by vcg
    
    
    
    
    
    
  subsection \<open>Composition with Assertion for Elements\<close>    
    
  context
    fixes A :: "('a,'c) dr_assn"
  begin  
  
    definition "option_assn \<equiv> mk_assn (\<lambda>a c. case (a,c) of
        (None,None) \<Rightarrow> \<box>
      | (Some a, Some c) \<Rightarrow> \<upharpoonleft>A a c
      | _ \<Rightarrow> sep_false)
    "

    lemma option_assn_simps[simp]:  
      "\<upharpoonleft>option_assn None None = \<box>"  
      "\<upharpoonleft>option_assn (Some a) (Some c) = \<upharpoonleft>A a c"  
      "\<upharpoonleft>option_assn None (Some c) = sep_false"
      "\<upharpoonleft>option_assn (Some a) None = sep_false"
      
      "\<upharpoonleft>option_assn (Some a) bb = (EXS b. \<up>(bb=Some b) ** \<upharpoonleft>A a b)"
      "\<upharpoonleft>option_assn aa (Some b) = (EXS a. \<up>(aa=Some a) ** \<upharpoonleft>A a b)"
      "\<upharpoonleft>option_assn None bb = \<up>(bb=None)"
      "\<upharpoonleft>option_assn aa None = \<up>(aa=None)"
      
      unfolding option_assn_def 
      apply (auto split: option.splits simp: sep_algebra_simps)
      done
          
  end  

  definition "list_option_assn A \<equiv> list_assn (option_assn A)"
  
  lemma list_option_assn_imp_struct_eq: "pure_part (\<upharpoonleft>(list_option_assn A) xs xs') \<Longrightarrow> sl_struct xs = sl_struct xs'"
    apply (induction xs xs' rule: list_induct2')
    by (auto simp: list_option_assn_def sep_algebra_simps dest!: pure_part_split_conj)
    
  lemma list_option_assn_empty[simp]: 
    "\<upharpoonleft>(list_option_assn A) [] [] = \<box>"  
    "\<upharpoonleft>(list_option_assn A) [] (y#ys) = sep_false"  
    "\<upharpoonleft>(list_option_assn A) (x#xs) [] = sep_false"  
    unfolding list_option_assn_def
    by (auto simp: sep_algebra_simps)
    
    
  lemma list_option_assn_cons[simp]: "\<upharpoonleft>(list_option_assn A) (x#xs) (y#ys) 
    = (\<upharpoonleft>(option_assn A) x y ** \<upharpoonleft>(list_option_assn A) xs ys)"  
    unfolding list_option_assn_def
    by simp
    
  lemma list_option_assn_cons1_conv:
    "\<upharpoonleft>(list_option_assn A) (x#xs') ys 
      = (EXS y ys'. \<up>(ys=y#ys') ** \<upharpoonleft>(option_assn A) x y ** \<upharpoonleft>(list_option_assn A) xs' ys')"  
    unfolding list_option_assn_def
    by (auto simp: list_assn_cons1_conv)
    
  lemma list_option_assn_cons2_conv:
    "\<upharpoonleft>(list_option_assn A) xs (y#ys') 
      = (EXS x xs'. \<up>(xs=x#xs') ** \<upharpoonleft>(option_assn A) x y ** \<upharpoonleft>(list_option_assn A) xs' ys')"  
    unfolding list_option_assn_def
    by (auto simp: list_assn_cons2_conv)

    
  (* TODO: append is more general! *)    
  lemma list_option_assn_snoc[simp]: "\<upharpoonleft>(list_option_assn A) (xs@[x]) (ys@[y]) = ( \<upharpoonleft>(list_option_assn A) xs ys ** \<upharpoonleft>(option_assn A) x y)"  
    unfolding list_option_assn_def
    by (auto simp: sep_algebra_simps)

  lemma list_option_assn_empty_conv[simp]:
    "\<upharpoonleft>(list_option_assn A) xs [] = (\<up>(xs=[]))"
    "\<upharpoonleft>(list_option_assn A) [] ys = (\<up>(ys=[]))"
    unfolding list_option_assn_def by auto
    
    
  lemma list_option_assn_pure_part[vcg_prep_ext_rules]: 
    "pure_part (\<upharpoonleft>(list_option_assn A) xs ys) \<Longrightarrow> length xs = length ys" (* TODO: Extraction should also go to elements! *)  
    unfolding list_option_assn_def
    apply (vcg_prepare_external)
    by (auto)
    
        
  lemmas list_option_assn_cons_conv = list_option_assn_cons1_conv list_option_assn_cons2_conv
    
    
  lemma list_option_join_aux:
    assumes "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)"
    shows 
      "(\<upharpoonleft>(list_option_assn A) xs\<^sub>1 xs\<^sub>1' ** \<upharpoonleft>(list_option_assn A) xs\<^sub>2 xs\<^sub>2') 
      \<turnstile> \<upharpoonleft>(list_option_assn A) (sl_join xs\<^sub>1 xs\<^sub>2) (sl_join xs\<^sub>1' xs\<^sub>2')" 
    using assms
  proof (induction xs\<^sub>1 xs\<^sub>2 arbitrary: xs\<^sub>1' xs\<^sub>2' rule: list_induct2')
    case 1
    then show ?case by (auto simp: sep_algebra_simps entails_def)
  next
    case (2 x\<^sub>1 xs\<^sub>1)
    then show ?case by simp
  next
    case (3 x\<^sub>2 xs\<^sub>2)
    then show ?case by simp
  next
    case (4 x\<^sub>1 xs\<^sub>1 x\<^sub>2 xs\<^sub>2)
    hence 
      COMPAT: "x\<^sub>1=None \<or> x\<^sub>2=None" and
      IH: "\<upharpoonleft>(list_option_assn A) xs\<^sub>1 xs\<^sub>1' \<and>* \<upharpoonleft>(list_option_assn A) xs\<^sub>2 xs\<^sub>2' 
          \<turnstile> \<upharpoonleft>(list_option_assn A) (sl_join xs\<^sub>1 xs\<^sub>2) (sl_join xs\<^sub>1' xs\<^sub>2')" for xs\<^sub>1' xs\<^sub>2'
      by auto    
    
    show ?case
      apply (rewrite in "\<hole>\<turnstile>_" list_option_assn_cons1_conv)+
      apply (clarsimp 
            simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
            intro!: entails_exE)
    proof goal_cases
      case (1 x\<^sub>1' xs\<^sub>1'' x\<^sub>2' xs\<^sub>2'')
      then show ?case
        apply (sep_drule IH)
        using COMPAT
        apply (cases x\<^sub>1; cases x\<^sub>2; 
          clarsimp 
            simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
            intro!: entails_exE
        )
        apply fri
        apply fri
        done
        
    qed  
  qed
    
  lemma list_option_join:
    assumes "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)"
    shows 
      "(\<upharpoonleft>(list_option_assn A) xs\<^sub>1 xs\<^sub>1' ** \<upharpoonleft>(list_option_assn A) xs\<^sub>2 xs\<^sub>2') 
      \<turnstile> \<upharpoonleft>(list_option_assn A) (sl_join xs\<^sub>1 xs\<^sub>2) (sl_join xs\<^sub>1' xs\<^sub>2') ** \<up>(sl_compat (sl_struct xs\<^sub>1') (sl_struct xs\<^sub>2'))" 
    apply (rule entails_pureI)
    using assms
    apply (clarsimp dest!: pure_part_split_conj list_option_assn_imp_struct_eq simp: sep_algebra_simps)
    apply (rule list_option_join_aux) 
    by simp

        
  lemma list_option_split:
    fixes ls xs xs'
    defines "xs\<^sub>1 \<equiv> sl_split ls xs"
    defines "xs\<^sub>2 \<equiv> sl_split (-ls) xs"
    defines "xs\<^sub>1' \<equiv> sl_split ls xs'"
    defines "xs\<^sub>2' \<equiv> sl_split (-ls) xs'"
    shows "\<upharpoonleft>(list_option_assn A) xs xs' \<turnstile> \<upharpoonleft>(list_option_assn A) xs\<^sub>1 xs\<^sub>1' ** \<upharpoonleft>(list_option_assn A) xs\<^sub>2 xs\<^sub>2'"
    unfolding assms
  proof (induction xs xs' rule: rev_induct2')
    case empty
    then show ?case by (simp add: sep_algebra_simps)
  next
    case (snocl x\<^sub>1 xs\<^sub>1)
    then show ?case by simp
  next
    case (snocr x\<^sub>1 xs\<^sub>2)
    then show ?case by simp
  next
    case (snoclr x\<^sub>1 xs\<^sub>1 x\<^sub>2 xs\<^sub>2)
    
    show ?case 
      apply (rule entails_pureI)
      apply vcg_prepare_external
    
      apply (sep_drule snoclr.IH)
      apply (simp add: sl_split_snoc)
      apply (cases "length xs\<^sub>2 \<in> ls"; simp)
      apply fri
      apply fri
      done
  qed    
      
  
  definition "oarray_idxs_dr_assn A \<equiv> mk_assn (assn_comp (\<upharpoonleft>(list_option_assn A)) (\<upharpoonleft>array_idxs_dr_assn))"
  
  lemma oarray_idxs_join:
    assumes COMPAT: "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)"
    shows "(\<upharpoonleft>(oarray_idxs_dr_assn A) xs\<^sub>1 p ** \<upharpoonleft>(oarray_idxs_dr_assn A) xs\<^sub>2 p) \<turnstile> \<upharpoonleft>(oarray_idxs_dr_assn A) (sl_join xs\<^sub>1 xs\<^sub>2) p" 
    
    unfolding oarray_idxs_dr_assn_def assn_comp_def
    apply (clarsimp 
          simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
          intro!: entails_exE)
    apply (sep_drule list_option_join[OF COMPAT])      
    apply (sep_drule array_idxs_join)
    by fri

    
  lemma oarray_idxs_split: 
    fixes ls xs
    defines "xs\<^sub>1 \<equiv> sl_split ls xs"
    defines "xs\<^sub>2 \<equiv> sl_split (-ls) xs"
    shows "\<upharpoonleft>(oarray_idxs_dr_assn A) xs p \<turnstile> (\<upharpoonleft>(oarray_idxs_dr_assn A) xs\<^sub>1 p ** \<upharpoonleft>(oarray_idxs_dr_assn A) xs\<^sub>2 p)"
    unfolding oarray_idxs_dr_assn_def assn_comp_def
    apply (clarsimp 
          simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists assms
          intro!: entails_exE)
    apply (subst array_idxs_split_eq[where ls=ls])
    apply (sep_drule list_option_split[where ls=ls])
    apply fri
    done
    
  
  (* TODO: There's a simproc for that in HOL. And there was one in Sep_Logic_Imp_HOL. *)
  lemma EXS_det_simple: 
    "(EXS x. \<up>(x=a) ** P x) = (P a)"
    "(EXS x x'. \<up>(x=f x') ** Q x x') = (EXS x'. Q (f x') x')"
    by (auto simp: sep_algebra_simps)
    
    
  
  lemma list_option_map_Some1_conv:"\<upharpoonleft>(list_option_assn A) (map Some xs) yss = (EXS ys. \<up>(yss = map Some ys) ** \<upharpoonleft>(list_assn A) xs ys)"  
    apply (induction xs yss rule: list_induct2') 
    apply (simp_all add: sep_algebra_simps) [3]
    apply simp
    apply (thin_tac _)
    apply (simp add: list_assn_cons1_conv)
    apply (rule entails_eqI)
    
    apply (rule entails_pureI)
    apply (clarsimp 
      dest!: pure_part_split_conj
      simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
      intro!: entails_exE
      )
    subgoal for x xs y ys
      apply (rule entails_exI[where x="y#ys"])
      by fri
    
    apply (clarsimp 
      dest!: pure_part_split_conj
      simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
      intro!: entails_exE
      )
    apply fri  
    done
      
  lemma list_option_map_Some2_conv:
    "\<upharpoonleft>(list_option_assn A) xss (map Some ys) 
    = (EXS xs. \<up>(xss = map Some xs) ** \<upharpoonleft>(list_assn A) xs ys)"  
    apply (induction xss ys rule: list_induct2') 
    apply (simp_all add: sep_algebra_simps) [3]
    apply simp
    apply (thin_tac _)
    apply (simp add: list_assn_cons2_conv)
    apply (rule entails_eqI)
    
    apply (rule entails_pureI)
    apply (clarsimp 
      dest!: pure_part_split_conj
      simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
      intro!: entails_exE
      )
    subgoal for x xs y ys
      apply (rule entails_exI[where x="y#ys"])
      by fri
    
    apply (clarsimp 
      dest!: pure_part_split_conj
      simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
      intro!: entails_exE
      )
    apply fri  
    done
    
    
  lemma list_oelem_assn_map_Some_conv: "\<upharpoonleft>(list_assn (oelem_assn A)) (map Some xs) ys = \<upharpoonleft>(list_assn A) xs ys"  
    apply (induction xs ys rule: list_induct2')
    by auto
    
  lemma sao_assn_map_Some_conv: "\<upharpoonleft>(sao_assn A) (map Some xs) p = (EXS xsh. (\<upharpoonleft>(list_assn A) xs xsh) ** raw_array_slice_assn xsh p)"  
    unfolding sao_assn_def
    by (simp add: list_oelem_assn_map_Some_conv sep_conj_commute)
    
  lemma woarray_slice_to_idxs: "woarray_slice_assn A xs p = \<upharpoonleft>(oarray_idxs_dr_assn (mk_assn A)) (sl_of_list xs) p"
    unfolding woarray_slice_assn_def hr_comp_def
    apply (clarsimp 
      simp: some_list_rel_conv EXS_det_simple sl_of_list_def
      simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists
    )
    unfolding oarray_idxs_dr_assn_def assn_comp_def
    apply (clarsimp simp: list_option_map_Some1_conv EXS_det_simple sep_conj_exists)
    unfolding eoarray_slice_assn_def
    by (simp add: sao_assn_map_Some_conv array_slice_to_idxs sl_of_list_def)

  lemma idxs_to_woarray_slice: "sl_complete (sl_struct xs) \<Longrightarrow> \<upharpoonleft>(oarray_idxs_dr_assn A) xs p = woarray_slice_assn (\<upharpoonleft>A) (list_of_sl xs) p"
    apply (subst woarray_slice_to_idxs)
    by simp
    
    
  lemma list_option_assn_swap: 
    "\<lbrakk>i<length xs; j<length xs\<rbrakk> \<Longrightarrow> \<upharpoonleft>(list_option_assn A) (swap xs i j) (swap xs' i j) = \<upharpoonleft>(list_option_assn A) xs xs'"  
    unfolding list_option_assn_def list_assn_def
    apply (cases "length xs = length xs'"; simp add: sep_algebra_simps)
    apply (cases "i=j"; simp?)
    apply (rewrite in "\<hole>=_" sep_set_img_remove[of i], simp)
    apply (rewrite in "\<hole>=_" sep_set_img_remove[of j], simp)
    apply (rewrite in "_=\<hole>" sep_set_img_remove[of i], simp)
    apply (rewrite in "_=\<hole>" sep_set_img_remove[of j], simp)
    apply (simp add: swap_def)
    apply (rule entails_eqI)
    apply fri+
    done
    
  lemma list_option_assn_swap_fri_rl: 
    "PRECOND (SOLVE_DEFAULT_AUTO (i<length xs \<and> j<length xs)) \<Longrightarrow> \<upharpoonleft>(list_option_assn A) xs xs' \<turnstile> \<upharpoonleft>(list_option_assn A) (swap xs i j) (swap xs' i j)"  
    by (simp add: PRECOND_def SOLVE_DEFAULT_AUTO_def list_option_assn_swap)
    
  lemma sl_struct_eq_imp_length_eq: "sl_struct xs = sl_struct ys \<Longrightarrow> length xs = length ys"  
    unfolding sl_struct_def by (rule map_eq_imp_length_eq)
  
  lemma raw_array_swap_oidxs_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(oarray_idxs_dr_assn A) xs p ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji ** \<up>\<^sub>d(i\<in>sl_indexes' xs \<and> j\<in>sl_indexes' xs))
    (raw_array_swap p ii ji)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>(oarray_idxs_dr_assn A) (swap xs i j) p)"
    unfolding oarray_idxs_dr_assn_def assn_comp_def
    apply (clarsimp simp: sep_conj_exists intro!: htriple_exI)
    apply (rule htriple_pure_preI)
    apply (clarsimp dest!: pure_part_split_conj list_option_assn_imp_struct_eq)
    apply (frule sl_struct_eq_imp_length_eq)

    supply [fri_rules] = list_option_assn_swap_fri_rl
    supply [dest] = sl_indexes_lengthD
    by vcg

    
  definition [llvm_inline]: "oidxs_split ls p \<equiv> Mreturn ()"  
  definition [llvm_inline]: "oidxs_join p\<^sub>1 p\<^sub>2 \<equiv> Mreturn ()"
  
  lemma oidxs_split_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(oarray_idxs_dr_assn A) xs p)
    (oidxs_split ls p)
    (\<lambda>_. \<upharpoonleft>(oarray_idxs_dr_assn A) (sl_split ls xs) p ** \<upharpoonleft>(oarray_idxs_dr_assn A) (sl_split (-ls) xs) p)"
    unfolding oidxs_split_def
    apply (rule htriple_ent_pre)
    apply (sep_drule oarray_idxs_split[where ls=ls], rule entails_refl)
    by vcg
  
  lemma oidxs_join_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(oarray_idxs_dr_assn A) xs\<^sub>1 p\<^sub>1 ** \<upharpoonleft>(oarray_idxs_dr_assn A) xs\<^sub>2 p\<^sub>2 ** \<up>(p\<^sub>1=p\<^sub>2 \<and> sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)))
    (oidxs_join p\<^sub>1 p\<^sub>2)
    (\<lambda>_. \<upharpoonleft>(oarray_idxs_dr_assn A) (sl_join xs\<^sub>1 xs\<^sub>2) p\<^sub>2)"    
    unfolding oidxs_join_def
    apply (rule htriple_ent_pre)
    apply (clarsimp simp: pred_lift_move_front_simps entails_lift_extract_simps sep_conj_exists)
    apply (sep_drule oarray_idxs_join, simp)
    apply (rule entails_refl)
    by vcg

    
  definition "oarray_idxs_assn A \<equiv> \<upharpoonleft>(oarray_idxs_dr_assn (mk_assn A))"
        
    
  definition "oidxs_with_idxs ls p m \<equiv> doM {
    oidxs_split ls p;
    (r,p\<^sub>1,p\<^sub>2) \<leftarrow> m p p;
    oidxs_join p\<^sub>1 p\<^sub>2;
    Mreturn (r,p)
  }"
  
  definition [llvm_inline]: "oidxs_with_idxs' p m \<equiv> doM { (r,_,_) \<leftarrow> m p p; Mreturn (r,p) }"
  
  lemma oidxs_with_idxs_elim_ghost[llvm_inline]: "oidxs_with_idxs ls p m = oidxs_with_idxs' p m"
    unfolding oidxs_with_idxs_def oidxs_split_def oidxs_join_def oidxs_with_idxs'_def
    by simp
  
  (* Monotonicity setup *)
  lemma oidxs_with_idxs_mono[partial_function_mono]:
    assumes "\<And>xs\<^sub>1 xs\<^sub>2. M_mono' (\<lambda>D. m D xs\<^sub>1 xs\<^sub>2)"
    shows "M_mono' (\<lambda>D. oidxs_with_idxs ls a (m D))"
    unfolding oidxs_with_idxs_def using assms
    by pf_mono_prover

  lemma oidxs_with_idxs'_mono[partial_function_mono]:
    assumes "\<And>xs\<^sub>1 xs\<^sub>2. M_mono' (\<lambda>D. m D xs\<^sub>1 xs\<^sub>2)"
    shows "M_mono' (\<lambda>D. oidxs_with_idxs' a (m D))"
    unfolding oidxs_with_idxs'_def using assms
    by pf_mono_prover
    
        
  lemma hn_WITH_IDXS_aux:
    assumes MHN: "\<And>xs\<^sub>1 xs\<^sub>2. hn_refine 
      (hn_ctxt (oarray_idxs_assn A) xs\<^sub>1 xsi ** hn_ctxt (oarray_idxs_assn A) xs\<^sub>2 xsi ** F) 
      (mi xsi xsi) 
      (F') 
      (R \<times>\<^sub>a oarray_idxs_assn A \<times>\<^sub>a oarray_idxs_assn A) 
      (CP' xsi xsi) 
      (m xs\<^sub>1 xs\<^sub>2)"
    assumes CP': "\<And>ri xsi\<^sub>1' xsi\<^sub>2'. CP' xsi xsi (ri,xsi\<^sub>1',xsi\<^sub>2') \<Longrightarrow> xsi\<^sub>1'=xsi \<and> xsi\<^sub>2'=xsi \<and> CP ri"
    shows "hn_refine 
      (hn_ctxt (oarray_idxs_assn A) xs xsi ** F) 
      (oidxs_with_idxs' xsi mi) 
      (F') 
      (R \<times>\<^sub>a oarray_idxs_assn A) 
      (\<lambda>(ri,xsi'). xsi'=xsi \<and> CP ri) 
      (WITH_IDXS ls xs m)"  
      
    apply (rewrite oidxs_with_idxs_elim_ghost[symmetric, where ls=ls])  
      
    apply (sepref_to_hoare)
    unfolding oidxs_with_idxs_def WITH_IDXS_def oarray_idxs_assn_def hn_ctxt_def
    
    supply [simp] = pure_def refine_pw_simps pw_le_iff sl_compat_splitI
    supply [dest] = CP'
    
    apply (clarsimp simp: )
    
    supply [vcg_rules] = hn_refineD[OF MHN, unfolded oarray_idxs_assn_def hn_ctxt_def]
    
    apply vcg
    apply (drule CP')
    apply vcg
    done
        
  lemma hn_WITH_IDXS_oarray_idxs[sepref_comb_rules]: 
    assumes FR: "\<Gamma> \<turnstile> hn_ctxt (oarray_idxs_assn A) xs xsi ** \<Gamma>\<^sub>1"
    assumes HN: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<lbrakk> CP_assm (xsi\<^sub>1 = xsi); CP_assm (xsi\<^sub>2 = xsi) \<rbrakk> \<Longrightarrow> hn_refine 
      (hn_ctxt (oarray_idxs_assn A) xs\<^sub>1 xsi\<^sub>1 ** hn_ctxt (oarray_idxs_assn A) xs\<^sub>2 xsi\<^sub>2 ** \<Gamma>\<^sub>1) 
      (mi xsi\<^sub>1 xsi\<^sub>2) 
      (\<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2) (R) (CP xsi\<^sub>1 xsi\<^sub>2) (m xs\<^sub>1 xs\<^sub>2)"
    assumes CP: "\<And>ri' xsi\<^sub>1 xsi\<^sub>2 xsi\<^sub>1' xsi\<^sub>2'. CP_assm (CP xsi\<^sub>1 xsi\<^sub>2 (ri',xsi\<^sub>1',xsi\<^sub>2')) \<Longrightarrow> CP_cond (xsi\<^sub>1' = xsi\<^sub>1 \<and> xsi\<^sub>2'=xsi\<^sub>2)"  
    assumes FR2: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2 \<turnstile>
      hn_invalid (oarray_idxs_assn A) xs\<^sub>1 xsi\<^sub>1 ** hn_invalid (oarray_idxs_assn A) xs\<^sub>2 xsi\<^sub>2 ** \<Gamma>\<^sub>1'"
    assumes FR3: "\<And>x xi. hn_ctxt R x xi \<turnstile> hn_ctxt (R' \<times>\<^sub>a oarray_idxs_assn A \<times>\<^sub>a oarray_idxs_assn A) x xi"  
    assumes CP2: "CP_simplify (CP_EX32 (CP xsi xsi)) (CP')"  
    shows "hn_refine 
      (\<Gamma>) 
      (oidxs_with_idxs' xsi mi) 
      (hn_invalid (oarray_idxs_assn A) xs xsi ** \<Gamma>\<^sub>1') 
      (R' \<times>\<^sub>a oarray_idxs_assn A) 
      (CP') 
      (PR_CONST (WITH_IDXS ls)$xs$(\<lambda>\<^sub>2a b. m a b))"  
      unfolding autoref_tag_defs PROTECT2_def
      apply (rule hn_refine_cons_pre)
      applyS (rule FR)
      apply1 extract_hnr_invalids
      supply R = hn_WITH_IDXS_aux[where CP="\<lambda>ri. CP xsi xsi (ri,xsi,xsi)"]
      thm hn_refine_cons_cp[OF _ R[where CP'=CP]]
      apply (rule hn_refine_cons_cp[OF _ R])
      
      applyS (fri)
      apply1 extract_hnr_invalids
      
      supply R = hn_refine_cons[OF _ HN, of _ _ xsi _ xsi]
      thm R
      
      apply (rule R)
      applyS (fri)
      applyS (simp add: CP_defs)
      applyS (simp add: CP_defs)
      applyS (sep_drule FR2; simp; rule entails_refl)
      focus
        apply clarsimp
        apply (sep_drule FR3[unfolded hn_ctxt_def])
        apply simp
        apply (rule entails_refl)
        solved
      subgoal 
        using CP unfolding CP_defs by blast 
      applyS simp  
      applyS simp  
      subgoal
        using CP2 unfolding CP_defs by blast 
      done  
      
        
      
  lemma slist_swap_oidxs_hnr: "(uncurry2 raw_array_swap,uncurry2 mop_slist_swap) 
    \<in> [\<lambda>_. True]\<^sub>c (oarray_idxs_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> oarray_idxs_assn A [\<lambda>((xsi,_),_) ri. ri=xsi]\<^sub>c"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply (simp add: refine_pw_simps)
    unfolding oarray_idxs_assn_def
    by vcg

  thm woarray_slice_to_idxs
  
  lemma oidxs_of_woarray_slice_hnr: "(Mreturn,mop_sl_of_list) \<in> [\<lambda>_. True]\<^sub>c (woarray_slice_assn A)\<^sup>d \<rightarrow> oarray_idxs_assn A [\<lambda>xsi ri. ri=xsi]\<^sub>c"  
    apply sepref_to_hoare
    apply (simp add: woarray_slice_to_idxs oarray_idxs_assn_def)
    by vcg
    
  lemma woarray_slice_of_oidxs_hnr: "(Mreturn,mop_list_of_sl) \<in> [\<lambda>_. True]\<^sub>c (oarray_idxs_assn A)\<^sup>d \<rightarrow> woarray_slice_assn A [\<lambda>xsi ri. ri=xsi]\<^sub>c"  
    apply sepref_to_hoare
    apply (simp add: refine_pw_simps)
    apply (simp add: idxs_to_woarray_slice oarray_idxs_assn_def)
    apply vcg
    done
    
              
  context
    notes [fcomp_norm_simps] = option_rel_id_simp list_rel_id_simp
  begin  
    sepref_decl_impl (ismop) slist_swap_oidxs_hnr uses mop_slist_swap.fref[of Id] .
    sepref_decl_impl (ismop) oidxs_of_woarray_slice_hnr .
    sepref_decl_impl (ismop) woarray_slice_of_oidxs_hnr .
  end


end

end
