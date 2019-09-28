theory Sorting_Setup
imports Sorting_Misc
begin


definition "le_by_lt lt a b \<equiv> \<not>lt b a"  
definition "lt_by_le le a b \<equiv> le a b \<and> \<not>le b a"

locale weak_ordering_le =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes trans: "a \<^bold>\<le> b \<Longrightarrow> b \<^bold>\<le> c \<Longrightarrow> a \<^bold>\<le> c"
  assumes connex: "a\<^bold>\<le>b \<or> b\<^bold>\<le>a"

locale weak_ordering_lt =
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 50)
  assumes asym: "a\<^bold><b \<Longrightarrow> \<not>b\<^bold><a"
  assumes itrans: "a\<^bold><c \<Longrightarrow> a\<^bold><b \<or> b\<^bold><c"
      
locale weak_ordering = 
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 50)
  assumes trans[trans]: "a \<^bold>\<le> b \<Longrightarrow> b \<^bold>\<le> c \<Longrightarrow> a \<^bold>\<le> c"
  assumes connex: "a\<^bold>\<le>b \<or> b\<^bold>\<le>a"
  assumes asym: "a\<^bold><b \<Longrightarrow> \<not>b\<^bold><a"
  assumes itrans: "a\<^bold><c \<Longrightarrow> a\<^bold><b \<or> b\<^bold><c"
  assumes lt_by_le: "lt_by_le (\<^bold>\<le>) = (\<^bold><)"
  assumes le_by_lt: "le_by_lt (\<^bold><) = (\<^bold>\<le>)"
begin


  lemma unfold_lt_to_le: "a \<^bold>< b \<longleftrightarrow> a\<^bold>\<le>b \<and> \<not>b\<^bold>\<le>a" unfolding lt_by_le[symmetric] lt_by_le_def by simp
  lemma unfold_le_to_lt: "a \<^bold>\<le> b \<longleftrightarrow> \<not>b\<^bold><a" unfolding le_by_lt[symmetric] le_by_lt_def by simp

  abbreviation (input) greater_eq (infix "\<^bold>\<ge>" 50) where "b\<^bold>\<ge>a \<equiv> a\<^bold>\<le>b"
  abbreviation (input) greater (infix "\<^bold>>" 50) where "b\<^bold>>a \<equiv> a\<^bold><b"

  lemma wo_refl[iff]: "a \<^bold>\<le> a" using connex by auto
  lemma wo_irrefl[iff]: "\<not>a\<^bold><a" using asym by blast
  lemma wo_less_trans[trans]: "a\<^bold><b \<Longrightarrow> b\<^bold><c \<Longrightarrow> a\<^bold><c" using asym itrans by blast

  lemma [iff]:
    shows transp_le: "transp (\<^bold>\<le>)"
      and reflp_le: "reflp (\<^bold>\<le>)"
      and transp_lt: "transp (\<^bold><)"
      and irreflp_lt: "irreflp (\<^bold><)"
    unfolding transp_def reflp_def irreflp_def
    using trans wo_less_trans   
    by blast+
    
  
  
  definition eq (infix "\<^bold>=" 50) where "a \<^bold>= b \<equiv> \<not>a\<^bold><b \<and> \<not>b\<^bold><a"
    
  lemma eq_refl[iff]: "a \<^bold>= a"
    unfolding eq_def by blast
        
  lemma eq_sym: "a \<^bold>= b \<longleftrightarrow> b \<^bold>= a"  
    unfolding eq_def by blast
    
  lemma eq_trans: "a \<^bold>= b \<Longrightarrow> b \<^bold>= c \<Longrightarrow> a \<^bold>= c"
    unfolding eq_def using itrans by blast
  
  lemma eq_equiv: "equivp (\<^bold>=)"
    apply (intro equivpI reflpI sympI transpI)
    using eq_sym eq_trans by blast+

  text \<open>Compatibility lemmas, similar names as for order\<close>  
    
  lemma wo_leI: "\<not> x \<^bold>< y \<Longrightarrow> y \<^bold>\<le> x" by (simp add: unfold_le_to_lt)
  
  lemma wo_leD: "y \<^bold>\<le> x \<Longrightarrow> \<not> x \<^bold>< y" by (simp add: unfold_le_to_lt)
  
  lemma wo_not_le_imp_less: "\<not> y \<^bold>\<le> x \<Longrightarrow> x \<^bold>< y" by (simp add: unfold_le_to_lt)
    
  lemma wo_le_less_trans[trans]: "x \<^bold>\<le> y \<Longrightarrow> y \<^bold>< z \<Longrightarrow> x \<^bold>< z"
    using itrans wo_leD by blast
  
  lemma wo_less_le_trans[trans]: "x \<^bold>< y \<Longrightarrow> y \<^bold>\<le> z \<Longrightarrow> x \<^bold>< z"
    using itrans wo_leD by blast
    
  lemma wo_less_not_sym: "x \<^bold>< y \<Longrightarrow> \<not> (y \<^bold>< x)"
    using asym by blast
  
  lemma wo_less_asym: "x \<^bold>< y \<Longrightarrow> (\<not> P \<Longrightarrow> y \<^bold>< x) \<Longrightarrow> P"
    using asym by blast
    
    
    

end  

sublocale weak_ordering_lt < weak_ordering "le_by_lt (\<^bold><)"
  apply (unfold_locales)
  unfolding le_by_lt_def lt_by_le_def using asym itrans by blast+

sublocale weak_ordering_le < weak_ordering "(\<^bold>\<le>)" "lt_by_le (\<^bold>\<le>)"
  apply (unfold_locales)
  unfolding le_by_lt_def lt_by_le_def using trans connex by blast+

  
  
lemma linwo: "weak_ordering (\<le>) ((<)::_::linorder \<Rightarrow> _)"
  apply unfold_locales
  unfolding le_by_lt_def lt_by_le_def
  by (auto simp: fun_eq_iff)

lemma funwo: "weak_ordering (\<lambda>a b. f a \<le> f b) (\<lambda>a b. f a < f b)" for f :: "'a \<Rightarrow> 'b::linorder"
  apply unfold_locales
  unfolding le_by_lt_def lt_by_le_def
  by (auto simp: fun_eq_iff)
  
lemma le_by_linorder[simp]: "le_by_lt ((<)::_::linorder \<Rightarrow> _) = (\<le>)"  
  unfolding le_by_lt_def less_le_not_le by (intro ext) auto
  
lemma lt_by_linorder[simp]: "lt_by_le ((\<le>)::_::linorder \<Rightarrow> _) = (<)"  
  unfolding lt_by_le_def less_le_not_le by (intro ext) auto
    
  
lemma bex_intv_shift_aux: "(\<forall>x\<in>{0..<Suc n}. P x) \<longleftrightarrow> (P 0 \<and> (\<forall>x\<in>{0..<n}. P (Suc x)))"
  apply auto
  using less_Suc_eq_0_disj by auto

lemma sorted_wrt_adjacent: "\<lbrakk>transp R\<rbrakk> \<Longrightarrow> sorted_wrt R xs \<longleftrightarrow> (\<forall>i\<in>{0..<length xs-1}. R (xs!i) (xs!Suc i))"
  supply [simp del] = sorted_wrt.simps(2) and [simp] = sorted_wrt2_simps
  apply (induction xs rule: induct_list012)
  apply (auto simp: bex_intv_shift_aux)
  done

abbreviation "sorted_wrt_lt lt \<equiv> sorted_wrt (le_by_lt lt)"

lemma sorted_wrt_lt_adjacent: 
  assumes "weak_ordering_lt lt" 
  shows "sorted_wrt_lt lt xs \<longleftrightarrow> (\<forall>i\<in>{0..<length xs-1}. \<not>lt (xs!Suc i) (xs!i))"
proof -
  interpret weak_ordering_lt lt by fact
  
  show ?thesis
    apply (subst sorted_wrt_adjacent)
    apply (simp_all add: le_by_lt_def)
    done
    
qed

lemma sorted_sorted_wrt_lt: "sorted = sorted_wrt_lt ((<)::_::linorder \<Rightarrow>_)"
  apply (intro ext) unfolding sorted_sorted_wrt by simp



definition "sort_spec lt xs xs' \<equiv> mset xs'=mset xs \<and> sorted_wrt_lt lt xs'" 
  
definition "slice_sort_spec lt xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0);
    SPEC (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec lt (Misc.slice l h xs\<^sub>0) (Misc.slice l h xs))
  }"
  
  
text \<open> Sorting a permutation of a list amounts to sorting the list! \<close>
lemma sort_spec_permute: "\<lbrakk>mset xs' = mset xs; sort_spec lt xs' ys\<rbrakk> \<Longrightarrow> sort_spec lt xs ys"
  unfolding sort_spec_def by auto


  
  
     

definition "refines_relp A R Rimpl \<equiv> (uncurry Rimpl,uncurry (RETURN oo R)) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn"

term "GEN_ALGO Rimpl (refines_relp A R)"

lemma gen_refines_relpD: "GEN_ALGO Rimpl (refines_relp A R) \<Longrightarrow> (uncurry Rimpl,uncurry (RETURN oo R)) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn"
  by (simp add: GEN_ALGO_def refines_relp_def)

lemma gen_refines_relpI: "(uncurry Rimpl,uncurry (RETURN oo R)) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn \<Longrightarrow> GEN_ALGO Rimpl (refines_relp A R)"
  by (simp add: GEN_ALGO_def refines_relp_def)
  
  
locale sort_impl_context = weak_ordering +
  fixes lt_impl :: "'ai::llvm_rep \<Rightarrow> 'ai \<Rightarrow> 1 word llM"
    and elem_assn :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
  assumes lt_impl: "GEN_ALGO lt_impl (refines_relp elem_assn (\<^bold><))"
  assumes pureA[safe_constraint_rules]: "CONSTRAINT is_pure elem_assn"
  notes [sepref_frame_free_rules] = mk_free_is_pure[OF CONSTRAINT_D[OF pureA]]
  
  notes lt_hnr[sepref_fr_rules] = gen_refines_relpD[OF lt_impl]
  
  notes [[sepref_register_adhoc "(\<^bold><)"]]
  
begin
  abbreviation "arr_assn \<equiv> array_assn elem_assn"
end  

(* TODO: Refine lemmas to support more general size datatypes! *)
  
type_synonym size_t = "64"
abbreviation "size_assn \<equiv> snat_assn' TYPE(size_t)"
  
lemma unat_sort_impl_context: "sort_impl_context (\<le>) (<) ll_icmp_ult unat_assn"
  apply intro_locales
  apply (rule linwo)
  apply unfold_locales
  apply (rule gen_refines_relpI)
  apply (rule hn_unat_ops)
  apply (solve_constraint)
  done
  
  
  
  
  
  
  
(*
(* TODO: Refine lemmas to support more general datatypes! *)
type_synonym elem_t = "64"

abbreviation "elem_assn \<equiv> unat_assn' TYPE(elem_t)"

abbreviation "arr_assn \<equiv> array_assn elem_assn"
*)


end
