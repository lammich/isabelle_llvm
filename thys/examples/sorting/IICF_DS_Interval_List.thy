theory IICF_DS_Interval_List
imports "Isabelle_LLVM.IICF"
begin

(* TODO: Move *)  
lemma sort_key_empty_iff[simp]: "sort_key f xs = [] \<longleftrightarrow> xs=[]"
  by (cases xs) auto



(* TODO: Move *)  
lemma Max_at_least_less_than[simp]: "l<h \<Longrightarrow> Max {l..<h} = h-1" for l h :: nat 
  apply (subgoal_tac "(\<forall>x\<in>{l..<h}. x \<le> h-1)")
  by (auto intro: antisym)

lemma id_set_constraint_simps:
  "IS_LEFT_UNIQUE Id"  
  "single_valued Id"
  "(True \<Longrightarrow> PROP Q) \<equiv> PROP Q"
  by (auto simp: left_unique_id) 

  
(* TODO: Move *)  
lemma hr_comp_elim_b_rel:
  assumes "\<And>s s'. rdomp A s \<Longrightarrow> (s,s')\<in>R \<Longrightarrow> \<Phi> s'" 
  shows "hr_comp A (b_rel R \<Phi>) = hr_comp A R"
  unfolding hr_comp_def
  apply (auto simp: fun_eq_iff sep_algebra_simps)
  using assms unfolding rdomp_def by blast
  
  
    
(* TODO: Move *)  
definition "is_commutative f \<equiv> \<forall>a b. f a b = f b a"  

lemma is_commutativeI[intro?]: "\<lbrakk> \<And>a b. f a b = f b a \<rbrakk> \<Longrightarrow> is_commutative f" by (auto simp: is_commutative_def)


lemma is_commutative_RETURN[simp]: "is_commutative (Refine_Basic.RETURN \<circ>\<circ> f) = is_commutative f"  
  by (auto simp: is_commutative_def)
    
lemmas is_comm_simps = is_commutative_RETURN True_implies_equals 
  
  
lemma hfref_commute_op:
  assumes R: "(uncurry opi, uncurry op) \<in> [P]\<^sub>a [C]\<^sub>c Ax\<^sub>1 *\<^sub>a Ax\<^sub>2 \<rightarrow>\<^sub>d A [CP]\<^sub>c"
  assumes C: "is_commutative op"
  shows "(uncurry (\<lambda>x y. opi y x), uncurry op) \<in> [\<lambda>(a,b). P (b,a)]\<^sub>a [\<lambda>(a,b). C (b,a)]\<^sub>c Ax\<^sub>2 *\<^sub>a Ax\<^sub>1 \<rightarrow>\<^sub>d (\<lambda>(a,b). A (b,a)) [\<lambda>(ai,bi) ri. CP (bi,ai) ri]\<^sub>c"  
  apply (rule hfrefI)
  apply (rule hn_refineI)
  apply clarsimp
  subgoal for ai bi a b
    apply (rule cons_rule)
    supply R' = R[THEN hfrefD, THEN hn_refineD, of "(b,a)" "(bi,ai)", simplified]
    apply (rule R')
    using C
    apply (auto simp: is_commutative_def sep_algebra_simps)
    apply (metis sep.mult_commute)
    subgoal for r s x
      apply (rule exI[where x=x])
      apply auto
      by (simp only: sep_conj_ac)
    done  
  done
      
lemma hfref_ttnd_commute_op:
  assumes R: "(uncurry opi, uncurry op) \<in> Ax\<^sub>1 *\<^sub>a Ax\<^sub>2 \<rightarrow>\<^sub>a A"
  assumes C: "is_commutative op"
  shows "(uncurry (\<lambda>x y. opi y x), uncurry op) \<in> Ax\<^sub>2 *\<^sub>a Ax\<^sub>1 \<rightarrow>\<^sub>a A"  
  using hfref_commute_op[OF R C]
  apply (rule hfref_cons)
  by auto

(* TODO: Move *)
lemma Un_is_commutative[simp]: 
  "is_commutative (\<union>)"  
  "is_commutative op_set_union"
  "is_commutative mop_set_union"
  by (auto simp: is_commutative_def)

lemma Inter_is_commutative[simp]: 
  "is_commutative (\<inter>)"  
  "is_commutative op_set_inter"
  "is_commutative mop_set_inter"
  by (auto simp: is_commutative_def)


(* TODO: Move *)
lemma Range_prod_eq: "Range (a \<times>\<^sub>r b) = Range a \<times> Range b"
  apply auto
  apply rule
  apply (rule prod_relI)
  .

(* TODO: Move *)
lemma rdomp_al_assn_len_bound: "rdomp (al_assn' TYPE('l::len2) A) c \<Longrightarrow> 4<LENGTH('l)"
  unfolding al_assn_def arl_assn_def arl_assn'_def rdomp_def
  apply (rule ccontr)
  by (auto simp: hr_comp_def)
  
  


(* TODO: Move *)
lemma param_card[param]:
  assumes "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A"
  shows "(card,card) \<in> \<langle>A\<rangle>set_rel \<rightarrow> nat_rel" 
  apply (rule rel2pD)
  unfolding rel2p
  apply (rule card_transfer)
  by (simp add: p2prop assms)

(* TODO: Move *)
sepref_decl_op set_card: "card" :: "\<langle>A\<rangle>set_rel \<rightarrow> nat_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .


section "Interval Lists" 

(* Quite specific operations. Maybe move them up? *)
sepref_decl_op set_range: "\<lambda>l h. {l..<h}" :: "(Id::'a::ord rel) \<rightarrow> (Id::'a rel) \<rightarrow> \<langle>Id::'a rel\<rangle>set_rel" .
sepref_decl_op set_range_lb: "\<lambda>l. {l..}" :: "(Id::'a::ord rel) \<rightarrow> \<langle>Id::'a rel\<rangle>set_rel" .
sepref_decl_op set_union_disj: "\<lambda>a b. (a\<union>b)" :: "[\<lambda>(a,b::'a set). a\<inter>b={}]\<^sub>f \<langle>Id\<rangle>set_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<rightarrow> \<langle>Id::'a rel\<rangle>set_rel" by simp

sepref_decl_op set_incr_elems: "\<lambda>n s. (+)n`s" :: "(Id::'a::plus rel) \<rightarrow> \<langle>Id::'a rel\<rangle>set_rel \<rightarrow> \<langle>Id::'a rel\<rangle>set_rel" .


lemma pat_set[def_pat_rules]:
  "atLeastLessThan$l$h \<equiv> op_set_range$l$h"
  "atLeast$l \<equiv> op_set_range_lb$l"
  by auto
  

lemma Un_disj_is_commutative[simp]: 
  "is_commutative op_set_union_disj" 
  "is_commutative mop_set_union_disj" 
  by (auto intro!: is_commutativeI simp: Un_commute Int_commute)
  
term mop_set_empty  

(* Intention: split of a suitable subset (e.g. a single interval from an interval list)*)
definition [simp]: "mop_set_rm_subset s \<equiv> doN { ASSERT (s\<noteq>{}); SPEC (\<lambda>(s\<^sub>1,s\<^sub>2). s=s\<^sub>1\<union>s\<^sub>2 \<and> s\<^sub>1\<inter>s\<^sub>2={} \<and> s\<^sub>1\<noteq>{}) }"
sepref_register mop_set_rm_subset

(* Intention: split of a subset with exactly n elements *)
definition [simp]: "mop_set_split_card n s \<equiv> doN { ASSERT (s\<noteq>{} \<and> finite s \<and> n \<le> card s); SPEC (\<lambda>(s\<^sub>1,s\<^sub>2). s=s\<^sub>1\<union>s\<^sub>2 \<and> s\<^sub>1\<inter>s\<^sub>2={} \<and> card s\<^sub>1 = n ) }"
sepref_register mop_set_split_card

  
type_synonym iv = "nat \<times> nat"

definition iv_\<alpha> :: "iv \<Rightarrow> nat set" where "iv_\<alpha> \<equiv> \<lambda>(l,h). {l..<h}"

definition "iv_rel \<equiv> br iv_\<alpha> (\<lambda>_. True)"

definition iv_range :: "nat \<Rightarrow> nat \<Rightarrow> iv" where "iv_range l h \<equiv> (l,h)" 
definition iv_is_empty :: "iv \<Rightarrow> bool" where "iv_is_empty \<equiv> \<lambda>(l,h). l\<ge>h"
definition iv_inter :: "iv \<Rightarrow> iv \<Rightarrow> iv" where "iv_inter \<equiv> \<lambda>(l\<^sub>1,h\<^sub>1) (l\<^sub>2,h\<^sub>2). (max l\<^sub>1 l\<^sub>2, min h\<^sub>1 h\<^sub>2)"

definition iv_card :: "iv \<Rightarrow> nat" where "iv_card \<equiv> \<lambda>(l,h). if h<l then 0 else h-l"

definition "iv_split_card \<equiv> \<lambda>n (l,h). doN {
  ASSERT (l+n \<le> h);
  RETURN ((l,l+n), (l+n,h))
}"

definition iv_incr_elems where "iv_incr_elems \<equiv> \<lambda>n (l,h). if l<h then (l+n, h+n) else (l,h)"


context
  notes [simp] = iv_rel_def in_br_conv iv_\<alpha>_def
begin

lemma iv_range_refine: "(iv_range,op_set_range) \<in> Id \<rightarrow> Id \<rightarrow> iv_rel"
  by (auto simp: iv_range_def)

lemma iv_is_empty_refine: "(iv_is_empty, op_set_is_empty) \<in> iv_rel \<rightarrow> bool_rel"  
  by (auto simp: iv_is_empty_def)
  
lemma iv_inter_refine: "(iv_inter, op_set_inter) \<in> iv_rel \<rightarrow> iv_rel \<rightarrow> iv_rel"
  by (auto simp: iv_inter_def)

lemma iv_card_refine: "(iv_card, op_set_card) \<in> iv_rel \<rightarrow> nat_rel"  
  by (auto simp: iv_card_def)

lemma iv_incr_elems_refine: "(iv_incr_elems, op_set_incr_elems) \<in> nat_rel \<rightarrow> iv_rel \<rightarrow> iv_rel"  
  by (auto simp: iv_incr_elems_def)
  
     
lemma iv_\<alpha>_finite[simp,intro!]: "finite (iv_\<alpha> iv)" by (cases iv) auto
  
end

lemma iv_split_card_refine: "(iv_split_card, mop_set_split_card) \<in> nat_rel \<rightarrow> iv_rel \<rightarrow> \<langle>iv_rel \<times>\<^sub>r iv_rel\<rangle>nres_rel"  
  unfolding iv_split_card_def
  apply clarsimp
  apply (refine_vcg RETURN_SPEC_refine)
  unfolding iv_rel_def
  by (auto simp: in_br_conv iv_\<alpha>_def)
  




definition "iv_lb_rel \<equiv> { (l,{l..}) |l. True }"

lemma iv_lb_refine: "(id,op_set_range_lb) \<in> Id \<rightarrow> iv_lb_rel"
  by (auto simp: iv_lb_rel_def)


definition "iv_inter_lb \<equiv> \<lambda>l (l',h'). (max l l', h')"

lemma iv_inter_lb_refine: "(iv_inter_lb, op_set_inter) \<in> iv_lb_rel \<rightarrow> iv_rel \<rightarrow> iv_rel"
  by (auto simp: iv_inter_lb_def iv_lb_rel_def iv_rel_def in_br_conv iv_\<alpha>_def)
  
  



type_synonym ivl = "nat set list"

definition ivl_\<alpha> :: "ivl \<Rightarrow> nat set" where "ivl_\<alpha> ivl = \<Union>( set ivl )"

locale ivl_invar =
  fixes ivl :: ivl
  assumes distinct: "distinct ivl"
  assumes non_empty: "{}\<notin>set ivl"
  assumes finite: "iv\<in>set ivl \<Longrightarrow> finite iv"
  assumes non_overlapping: "\<lbrakk>i\<^sub>1\<in>set ivl; i\<^sub>2\<in>set ivl; i\<^sub>1\<noteq>i\<^sub>2\<rbrakk> \<Longrightarrow> i\<^sub>1 \<inter> i\<^sub>2 = {}"
begin

  lemma in_set_ivlsD: "\<lbrakk> iv\<in>set ivl \<rbrakk> \<Longrightarrow> iv \<subseteq> ivl_\<alpha> ivl \<and> iv\<noteq>{}"
    using non_empty
    by (auto simp: ivl_\<alpha>_def)

  lemma ivl_\<alpha>_finite[simp, intro!]: "finite (ivl_\<alpha> ivl)"  
    using finite unfolding ivl_\<alpha>_def
    by blast
    
      
end  

lemmas [simp, intro] = ivl_invar.ivl_\<alpha>_finite


definition "ivl_rel \<equiv> br ivl_\<alpha> ivl_invar"


lemma ivl_\<alpha>_empty_list[simp]: "ivl_\<alpha> [] = {}" by (simp add: ivl_\<alpha>_def)

lemma ivl_\<alpha>_Cons[simp]: "ivl_\<alpha> (iv#ivls) = iv \<union> ivl_\<alpha> ivls"
  by (auto simp: ivl_\<alpha>_def)
  
lemma ivl_\<alpha>_append[simp]: "ivl_\<alpha> (ivl\<^sub>1@ivl\<^sub>2) = ivl_\<alpha> ivl\<^sub>1 \<union> ivl_\<alpha> ivl\<^sub>2"
  by (auto simp: ivl_\<alpha>_def)

lemma in_ivl_\<alpha>_conv: "x\<in>ivl_\<alpha> ivl \<longleftrightarrow> (\<exists>iv\<in>set ivl. x\<in>iv)"  
  unfolding ivl_\<alpha>_def 
  by (auto)
  
lemma iv_dj_ivl_\<alpha>_conv: "s \<inter> ivl_\<alpha> ivl = {} \<longleftrightarrow> (\<forall>s'\<in>set ivl. s \<inter> s' = {})"  
  by (auto 0 3 simp: in_ivl_\<alpha>_conv)
  
lemma in_set_ivls_\<alpha>: "s\<in>set ivl \<Longrightarrow> s \<subseteq> ivl_\<alpha> ivl"  
  by (auto simp: in_set_conv_decomp)
  
lemma ivl_\<alpha>_dj_conv: "ivl_\<alpha> ivl\<^sub>1 \<inter> ivl_\<alpha> ivl\<^sub>2 = {} \<longleftrightarrow> (\<forall>s\<in>set ivl\<^sub>1. \<forall>s'\<in>set ivl\<^sub>2. s \<inter> s' = {})"
  by (auto 0 4 simp: in_set_conv_decomp in_ivl_\<alpha>_conv) 
  
  
lemma ivl_invar_empty_list[simp]: "ivl_invar []" by (simp add: ivl_invar_def) 
  
lemma ivl_invar_Cons[simp]: "ivl_invar (s#ivl) \<longleftrightarrow> s\<noteq>{} \<and> finite s \<and> s \<inter> ivl_\<alpha> ivl = {} \<and> ivl_invar ivl"  
  unfolding ivl_invar_def
  apply (intro conjI iffI)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal apply (simp add: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv) by auto
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  subgoal by (auto 0 3 simp: in_ivl_\<alpha>_conv iv_dj_ivl_\<alpha>_conv)
  done
  
lemma ivl_invar_append[simp]: "ivl_invar (ivls\<^sub>1@ivls\<^sub>2) \<longleftrightarrow> ivl_invar ivls\<^sub>1 \<and> ivl_invar ivls\<^sub>2 \<and> ivl_\<alpha> ivls\<^sub>1 \<inter> ivl_\<alpha> ivls\<^sub>2 = {}" 
  unfolding ivl_invar_def
  apply (intro conjI iffI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal apply (auto simp: in_ivl_\<alpha>_conv) by (metis disjoint_iff)
  subgoal by (fastforce simp: ivl_\<alpha>_dj_conv) 
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: ivl_\<alpha>_dj_conv) fast
  done  


lemma ivl_invar_sort[simp]: "ivl_invar (sort_key f xs) = ivl_invar xs"
  unfolding ivl_invar_def
  by auto 

  
definition iv_maxl :: "nat set \<Rightarrow> nat" where "iv_maxl iv \<equiv> if iv={} \<or> infinite iv then 0 else 2 + Max iv"

definition "ivl_maxl ivl \<equiv> if \<not>ivl_invar ivl then 0 else if ivl=[] then 1 else Max (iv_maxl`set ivl)"

lemma Max_UN_eq: "{}\<notin>S \<Longrightarrow> finite S \<Longrightarrow> (\<forall>s\<in>S. finite s) \<Longrightarrow> Max (\<Union>S) = Max (Max`S)" 
  apply (cases "S={}"; simp)
  by (smt (verit) Max_eq_iff Union_iff empty_iff finite_Union finite_imageI imageE image_eqI)
  

lemma Suc2_Max_commute: "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> Suc (Suc (Max A)) = Max ((Suc o Suc) ` A)"
  by (simp add: Inf.INF_image mono_Max_commute mono_Suc)

lemma ivl_maxl_alt: "ivl_maxl ivl = (if \<not>ivl_invar ivl then 0 else if ivl=[] then 1 else 2 + Max (ivl_\<alpha> ivl))"
  unfolding ivl_maxl_def ivl_\<alpha>_def iv_maxl_def
  apply (auto simp: )
  apply (simp add: image_constant_conv)
  apply (intro allI impI conjI)
  subgoal
    apply (subgoal_tac "(set ivl \<inter> {iv. iv \<noteq> {} \<and> finite iv}) = set ivl")
    apply (simp add: Max_UN_eq ivl_invar.finite ivl_invar.non_empty Suc2_Max_commute image_image)
    using ivl_invar.non_empty ivl_invar.finite
    by blast
  subgoal using ivl_invar.non_empty ivl_invar.finite by blast
  done


lemma ivl_length_bound:
  assumes "ivl_invar ivl"
  shows "length ivl < ivl_maxl ivl"
  using assms
proof (induction ivl rule: length_induct[case_names A])
  case (A ivl)

  interpret ivl_invar ivl by fact
  
  show ?case proof (cases "ivl = []")
    case True thus ?thesis by (simp add: ivl_maxl_def)
  next
    case False
    
    with A.prems have "ivl_\<alpha> ivl \<noteq> {}" by (auto simp: neq_Nil_conv) 
    hence 
      IN: "Max (ivl_\<alpha> ivl) \<in> ivl_\<alpha> ivl" and 
      MAX: "\<forall>x\<in>ivl_\<alpha> ivl. x \<le> Max (ivl_\<alpha> ivl)" 
      by (auto simp: A.prems(1))
    
    from IN obtain iv ivl\<^sub>1 ivl\<^sub>2 where IN_IV: "Max (ivl_\<alpha> ivl) \<in> iv" and [simp]: "ivl = ivl\<^sub>1@iv#ivl\<^sub>2" 
      by (auto simp: in_ivl_\<alpha>_conv in_set_conv_decomp)
      
    from A.prems A.IH[rule_format, of "ivl\<^sub>1@ivl\<^sub>2"] have L: "length (ivl\<^sub>1 @ ivl\<^sub>2) < ivl_maxl (ivl\<^sub>1 @ ivl\<^sub>2)" 
      by auto
      
    have "ivl_maxl (ivl\<^sub>1 @ ivl\<^sub>2) < ivl_maxl (ivl)"  
      using \<open>ivl_invar ivl\<close> IN_IV
      apply (auto 0 0 simp add: ivl_maxl_alt neq_Nil_conv nat_less_le)
      subgoal by (metis IntI UnCI UnE emptyE eq_Max_iff infinite_Un ivl_invar.ivl_\<alpha>_finite)
      subgoal by (metis IntI UnCI UnE emptyE eq_Max_iff infinite_Un ivl_invar.ivl_\<alpha>_finite)
      done
    
    thus ?thesis using L by simp  
  qed
qed  




lemma ivl_max_append: "ivl_invar (ivl@[iv]) \<Longrightarrow> ivl_maxl (ivl@[iv]) = max (ivl_maxl ivl) (iv_maxl iv)"
  unfolding ivl_maxl_alt iv_maxl_def
  apply (clarsimp simp: neq_Nil_conv)
  by (metis Max.union Un_empty ivl_\<alpha>_Cons ivl_invar.ivl_\<alpha>_finite ivl_invar_Cons)


  
lemma "(\<forall>x\<in>s. x<N) \<Longrightarrow> card s \<le> N" for s :: "nat set"
  by (simp add: subsetI subset_eq_atLeast0_lessThan_card)
    
context ivl_invar begin

  lemma set_ivl_inter_simps[simp]:
    "set ivl \<inter> {iv. iv = {} \<or> infinite iv} = {}"
    "(set ivl \<inter> {iv. iv \<noteq> {} \<and> finite iv}) = set ivl"
    using finite non_empty 
    by auto

  lemma ivl_max_notZ[simp]: "ivl_maxl ivl \<noteq> 0"
    unfolding ivl_maxl_def
    by (auto simp add: ivl_invar_axioms iv_maxl_def non_empty neq_Nil_conv Max_gr_iff)

    
  lemma ivl_member_bound: "x\<in>ivl_\<alpha> ivl \<Longrightarrow> x+1<ivl_maxl ivl"
    unfolding ivl_\<alpha>_def ivl_maxl_def iv_maxl_def
    apply (auto simp: ivl_invar_axioms Max_gr_iff)
    by (metis Max_less_iff all_not_in_conv lessI local.finite)

  lemma ivl_\<alpha>_bound: "ivl_\<alpha> ivl \<subseteq> {0..<ivl_maxl ivl - 1}"
    using ivl_member_bound
    by fastforce
    
  lemma ivl_\<alpha>_card_bound: "card (ivl_\<alpha> ivl) < ivl_maxl ivl"
    using ivl_\<alpha>_bound
    by (metis One_nat_def ivl_max_notZ less_imp_diff_less linorder_not_le minus_eq nat.simps(3) nat_neq_iff subset_eq_atLeast0_lessThan_card)
    
    

end  
  
    
  
  
  
definition "ivl_empty = []"
definition "ivl_is_empty ivls \<longleftrightarrow> ivls=[]"



lemma ivl_empty_invar[simp]: "ivl_invar ivl_empty" 
  and ivl_empty_\<alpha>[simp]: "ivl_\<alpha> ivl_empty = {}"
  unfolding ivl_\<alpha>_def ivl_invar_def ivl_empty_def
  by auto

lemma ivl_is_empty_\<alpha>[simp]: "ivl_invar ivls \<Longrightarrow> ivl_is_empty ivls \<longleftrightarrow> ivl_\<alpha> ivls={}"  
  unfolding ivl_\<alpha>_def ivl_invar_def ivl_is_empty_def
  apply auto 
  by (metis ex_in_conv set_empty)
  
    
(*lemma 
  assumes INV: "ivl_invar ivls" and PRE: "l<h" "{l..<h} \<inter> ivl_\<alpha> ivls = {}"
  shows ivl_add_invar[simp]: "ivl_invar (ivl_add l h ivls)"
    and ivl_add_\<alpha>[simp]: "ivl_\<alpha> (ivl_add l h ivls) = {l..<h} \<union> ivl_\<alpha> ivls"
  using assms
  unfolding ivl_add_def  
  by auto
*)  

  
lemma ivl_empty_refine: "(ivl_empty,op_set_empty) \<in> ivl_rel"  
  by (auto simp: ivl_rel_def in_br_conv)

lemma ivl_is_empty_refine: "(ivl_is_empty, op_set_is_empty) \<in> ivl_rel \<rightarrow> bool_rel"  
  by (auto simp: ivl_rel_def in_br_conv)
    
definition "ivl_add iv ivl \<equiv> doN { 
  if (op_set_is_empty iv) then 
    RETURN ivl 
  else doN {
    ASSERT (length ivl+1 < max (ivl_maxl ivl) (iv_maxl iv));
    RETURN (ivl@[iv])
  }
}"
  

lemma m_ivl_add_bound_aux: 
  assumes "ivl_invar ivl" "iv\<noteq>{}" "iv \<inter> ivl_\<alpha> ivl = {}" "finite iv"
  shows "Suc (length ivl) < max (ivl_maxl ivl) (iv_maxl iv)"
proof -
  from assms have "ivl_invar (ivl@[iv])" by auto
  from ivl_length_bound[OF this] ivl_max_append[OF this] show ?thesis by simp
qed    

term b_rel


lemma ivl_add_refine: "(ivl_add, mop_set_union_disj) \<in> b_rel Id finite \<rightarrow> ivl_rel \<rightarrow> \<langle>ivl_rel\<rangle>nres_rel"
  unfolding ivl_add_def
  apply clarsimp
  apply refine_vcg
  by (auto simp: iv_rel_def ivl_rel_def in_br_conv m_ivl_add_bound_aux)
  
  

  
definition "ivl_rm_subset (ivl::ivl) \<equiv> doN {
  mop_list_pop_last ivl
}"  
  

lemma ivl_rm_subset_refine: "(ivl_rm_subset,mop_set_rm_subset) \<in> ivl_rel \<rightarrow> \<langle>Id \<times>\<^sub>r ivl_rel\<rangle>nres_rel"
  unfolding ivl_rm_subset_def mop_set_rm_subset_def
  apply (refine_vcg RETURN_SPEC_refine)
  apply (auto simp: ivl_rel_def in_br_conv) []
  apply (clarsimp simp: ivl_rel_def in_br_conv) 
  subgoal for ivl by (cases ivl rule: rev_cases; auto)
  done
  

definition "ivl_card (ivl::ivl) \<equiv> doN {
  nfoldli ivl (\<lambda>_. True) (\<lambda>s acc. doN {
    c \<leftarrow> mop_set_card s;
    ASSERT (acc + c < ivl_maxl ivl);
    RETURN (acc+c)
  }) 0
}"
  
lemma ivl_card_refine: "(ivl_card,mop_set_card) \<in> ivl_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  unfolding ivl_card_def
  apply clarsimp
  apply (refine_vcg RETURN_SPEC_refine nfoldli_rule[where I="\<lambda>l1 l2 r. r = card (ivl_\<alpha> l1)"])
  apply (simp_all add: ivl_rel_def in_br_conv)
  subgoal for ivl iv l1 l2 r
    using ivl_invar.ivl_\<alpha>_card_bound[of ivl] 
    by (auto simp: card_Un_disjoint)
  apply (subst card_Un_disjoint)
  apply auto
  done
  
  
(*abbreviation (input) iv_assn' :: "'l itself \<Rightarrow> nat \<times> nat \<Rightarrow> 'l::len2 word \<times> 'l word \<Rightarrow> ll_assn" 
  where "iv_assn' TYPE('l) \<equiv> iv_assn"
*)  

context ivl_invar begin
(* TODO: Move *)
lemma finite_Un_ivl[simp, intro!]: "finite (\<Union> (set ivl))"
  using ivl_\<alpha>_def ivl_\<alpha>_finite by presburger

end

lemma ivl_max_bound_aux:
  assumes "Suc 0 \<le> N"
  assumes "\<And>s. s\<in>set ivl \<Longrightarrow> iv_maxl s \<le> N"    
  shows "ivl_maxl ivl \<le> N"
  using assms
  unfolding ivl_maxl_def 
  by auto


  
context
  fixes L
  defines "L \<equiv> LENGTH ('l::len2)" (* Workaround: Trick to hide type-length in constant. 
                                      Otherwise, sepref_decl_impl generalizes too much when 
                                      trying to prove parametricity of LENGTH('l) precond *)
begin

  private abbreviation (input) "sA \<equiv> snat_assn' TYPE('l)"
  definition "iv_assn_raw \<equiv> sA \<times>\<^sub>a sA"
  private abbreviation (input) "ivA \<equiv> iv_assn_raw :: _ \<Rightarrow> 'l word \<times> _ \<Rightarrow> _"
  
  sepref_definition iv_range_impl [llvm_inline] is "uncurry (RETURN oo iv_range)" :: "sA\<^sup>k*\<^sub>asA\<^sup>k \<rightarrow>\<^sub>a ivA"
    unfolding iv_range_def iv_assn_raw_def by sepref

  sepref_definition iv_is_empty_impl [llvm_inline] is "(RETURN o iv_is_empty)" :: "ivA\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding iv_is_empty_def iv_assn_raw_def by sepref
  
  sepref_definition iv_inter_impl [llvm_inline] is "uncurry (RETURN oo iv_inter)" :: "ivA\<^sup>k *\<^sub>a ivA\<^sup>k \<rightarrow>\<^sub>a ivA"
    unfolding iv_inter_def iv_assn_raw_def max_def min_def by sepref

  sepref_definition iv_card_impl [llvm_inline] is "RETURN o iv_card" :: "ivA\<^sup>k \<rightarrow>\<^sub>a sA"
    unfolding iv_card_def iv_assn_raw_def 
    apply (annot_snat_const "TYPE('l)")
    by sepref
    
  sepref_definition iv_range_lb_impl [llvm_inline] is "RETURN o id" :: "sA\<^sup>k \<rightarrow>\<^sub>a sA"
    by sepref
  
  sepref_definition iv_inter_lb_impl [llvm_inline] is "uncurry (RETURN oo iv_inter_lb)" :: "sA\<^sup>k *\<^sub>a ivA\<^sup>k \<rightarrow>\<^sub>a ivA"
    unfolding iv_inter_lb_def iv_assn_raw_def max_def
    by sepref
    
  sepref_definition iv_split_card_impl [llvm_inline] is "uncurry (iv_split_card)" :: "sA\<^sup>k *\<^sub>a ivA\<^sup>k \<rightarrow>\<^sub>a ivA \<times>\<^sub>a ivA"
    unfolding iv_split_card_def iv_assn_raw_def
    by sepref

  definition "iv_incr_elems_pre_aux \<equiv> \<lambda>n (l,h) L. l<h \<longrightarrow> h+n < L"  
    
  sepref_definition iv_incr_elems_impl [llvm_inline] is "uncurry (RETURN oo iv_incr_elems)" :: "[\<lambda>(n,iv). iv_incr_elems_pre_aux n iv (max_snat L)]\<^sub>a sA\<^sup>k *\<^sub>a ivA\<^sup>k \<rightarrow> ivA"  
    unfolding iv_incr_elems_def iv_assn_raw_def iv_incr_elems_pre_aux_def L_def
    by sepref
    
  definition "iv_assn \<equiv> hr_comp ivA iv_rel"  
  abbreviation "iv_assn' TYPE('l) \<equiv> iv_assn"
  
  definition "iv_lb_assn \<equiv> hr_comp sA iv_lb_rel"
  abbreviation "iv_lb_assn' TYPE('l) \<equiv> iv_lb_assn"
  
  lemma iv_assn_pure[safe_constraint_rules,simp]: "is_pure iv_assn"
    unfolding iv_assn_def iv_assn_raw_def
    by solve_constraint 

  lemma iv_lb_assn_pure[safe_constraint_rules,simp]: "is_pure iv_lb_assn"
    unfolding iv_lb_assn_def
    by solve_constraint 
    
  lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF iv_assn_pure] mk_free_is_pure[OF iv_lb_assn_pure]
    
    
        
  lemma rdomp_iv_assn_strong: "rdomp iv_assn s \<Longrightarrow> finite s \<and> iv_maxl s \<le> max_snat LENGTH('l)"
    apply (auto 
      simp: iv_assn_def iv_assn_raw_def iv_rel_def in_br_conv iv_maxl_def iv_\<alpha>_def
      dest!: in_snat_rel_boundsD)
    done
    
  lemma rdomp_iv_assn[sepref_bounds_dest]: "rdomp iv_assn s \<Longrightarrow> finite s"
    by (auto simp: iv_assn_def iv_rel_def in_br_conv)
      
  lemma iv_lb_assn_norm: "pure (snat_rel O iv_lb_rel) = iv_lb_assn"  
    unfolding iv_lb_assn_def 
    by (simp add: hr_comp_pure)
    

  definition iv_incr_elems_pre :: "nat set \<Rightarrow> _" where "iv_incr_elems_pre s n N \<equiv> s\<noteq>{} \<longrightarrow> 1 + Max s + n < N"
    
  lemma iv_incr_elems_norm_pre: "(iv,s)\<in>iv_rel \<Longrightarrow> iv_incr_elems_pre_aux n iv N \<longleftrightarrow> iv_incr_elems_pre s n N"
    unfolding iv_incr_elems_pre_def iv_incr_elems_pre_aux_def iv_maxl_def iv_rel_def iv_\<alpha>_def
    by (auto simp: in_br_conv)
      
  context 
    notes [fcomp_norm_simps] = iv_assn_def[symmetric] iv_lb_assn_norm set_rel_id_simp
    notes [fcomp_prenorm_simps] = iv_incr_elems_norm_pre
  begin
    sepref_decl_impl iv_range_impl.refine[FCOMP iv_range_refine] .
    sepref_decl_impl iv_is_empty_impl.refine[FCOMP iv_is_empty_refine] uses op_set_is_empty.fref[of Id] .
    sepref_decl_impl iv_inter_impl.refine[FCOMP iv_inter_refine] uses op_set_inter.fref[of Id, simplified id_set_constraint_simps] .
    sepref_decl_impl iv_range_lb_impl.refine[FCOMP iv_lb_refine] .
    sepref_decl_impl iv_inter_lb_impl.refine[FCOMP iv_inter_lb_refine] uses op_set_inter.fref[of Id, simplified id_set_constraint_simps] .
    
    sepref_decl_impl iv_card_impl.refine[FCOMP iv_card_refine] uses op_set_card.fref[of Id, simplified id_set_constraint_simps] .
    
    sepref_decl_impl iv_inter_impl.refine[FCOMP iv_inter_refine, THEN hfref_ttnd_commute_op, simplified is_comm_simps Inter_is_commutative] uses op_set_inter.fref[of Id, simplified id_set_constraint_simps] .
    sepref_decl_impl iv_inter_lb_impl.refine[FCOMP iv_inter_lb_refine, THEN hfref_ttnd_commute_op, simplified is_comm_simps Inter_is_commutative] uses op_set_inter.fref[of Id, simplified id_set_constraint_simps] .
    
    thm auto_weaken_pre_comp_PRE_I
    thm fcomp_prenorm_simps
    
    
    sepref_decl_impl iv_incr_elems_impl.refine[FCOMP iv_incr_elems_refine] by simp
    
    
    lemmas [sepref_fr_rules] = iv_split_card_impl.refine[FCOMP iv_split_card_refine]
  end

  
  definition "ivl_assn_raw \<equiv> al_assn' TYPE('l::len2) iv_assn"  
  private abbreviation (input) "ivlA \<equiv> ivl_assn_raw"
      
  sepref_definition ivl_empty_impl [llvm_inline] is "uncurry0 (RETURN ivl_empty)" :: "[\<lambda>_. 4<L]\<^sub>a unit_assn\<^sup>k \<rightarrow> ivlA"
    unfolding ivl_empty_def ivl_assn_raw_def al_fold_custom_empty[where 'l='l] L_def
    by sepref
    
  sepref_definition ivl_is_empty_impl [llvm_inline] is "RETURN o ivl_is_empty" :: "ivlA\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding ivl_is_empty_def ivl_assn_raw_def
    by sepref
    
    
  lemma rdomp_al_assn_iv_assn[sepref_bounds_dest]: "rdomp (al_assn' TYPE('l) iv_assn) ivl \<Longrightarrow> length ivl < max_snat LENGTH('l) \<and> ivl_maxl ivl \<le> max_snat LENGTH('l) \<and> 4<LENGTH('l)"
    apply (frule rdomp_al_assn_len_bound)
    apply (drule rdomp_al_dest')
    apply simp
    by (metis (no_types, opaque_lifting) Suc_leI in_set_conv_nth ivl_max_bound_aux le_less_trans rdomp_iv_assn_strong zero_order(1))
    
  sepref_definition ivl_add_impl [llvm_inline] is "uncurry ivl_add" :: "iv_assn\<^sup>k *\<^sub>a ivlA\<^sup>d \<rightarrow>\<^sub>a ivlA"  
    unfolding ivl_add_def ivl_assn_raw_def
    supply [sepref_bounds_dest] = rdomp_iv_assn_strong
    by sepref
    
  sepref_definition ivl_rm_subset_impl [llvm_inline] is "ivl_rm_subset" :: "ivlA\<^sup>d \<rightarrow>\<^sub>a iv_assn \<times>\<^sub>a ivlA"  
    unfolding ivl_rm_subset_def ivl_assn_raw_def by sepref

    
  sepref_definition ivl_card_impl [llvm_code] is "ivl_card" :: "ivlA\<^sup>k \<rightarrow>\<^sub>a sA" 
    unfolding ivl_card_def ivl_assn_raw_def
    apply (rewrite nfoldli_by_idx)
    apply (rewrite nfoldli_upt_by_while)
    apply (annot_snat_const "TYPE('l)")
    by sepref
    
          
  definition "ivl_assn \<equiv> hr_comp ivlA ivl_rel"
  abbreviation "ivl_assn' TYPE('l) \<equiv> ivl_assn"
  
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure ivl_assn]
  
  lemma ivl_assn_free[sepref_frame_free_rules]: "MK_FREE (ivl_assn) arl_free"
    unfolding ivl_assn_def ivl_assn_raw_def by (rule sepref_frame_free_rules)+

    
  lemma rdomp_ivl_assn[sepref_bounds_dest]: "rdomp (ivl_assn' TYPE('l::len2)) s \<Longrightarrow> finite s \<and> 4<LENGTH('l)"
    unfolding ivl_assn_def ivl_rel_def ivl_assn_raw_def
    by (clarsimp simp: in_br_conv rdomp_al_assn_len_bound) 
    
  lemma iv_assn_comp_finite_eq: "hr_comp iv_assn (b_rel Id finite) = iv_assn"
    apply (subst hr_comp_elim_b_rel)
    apply (simp add: rdomp_iv_assn)
    by simp
  
  context 
    notes [fcomp_norm_simps] = ivl_assn_def[symmetric] set_rel_id_simp iv_assn_comp_finite_eq
  begin
    thm ivl_empty_impl.refine[FCOMP ivl_empty_refine]
    
    sepref_decl_impl (no_register) ivl_empty: ivl_empty_impl.refine[FCOMP ivl_empty_refine] uses op_set_empty.fref[where A=Id] by simp
    sepref_decl_impl ivl_is_empty_impl.refine[FCOMP ivl_is_empty_refine] uses op_set_is_empty.fref[where A=Id] .
    
    sepref_decl_impl (ismop) ivl_add_impl.refine[FCOMP ivl_add_refine] .
    sepref_decl_impl (ismop) ivl_add_impl.refine[FCOMP ivl_add_refine, THEN hfref_ttnd_commute_op, simplified is_comm_simps Un_disj_is_commutative] .
    
    sepref_decl_impl (ismop) ivl_card_impl.refine[FCOMP ivl_card_refine] uses mop_set_card.fref[of Id, simplified id_set_constraint_simps] .
        
    lemmas [sepref_fr_rules] = ivl_rm_subset_impl.refine[FCOMP ivl_rm_subset_refine]
    
    
  end    

end


context  
  fixes L
  defines "L \<equiv> LENGTH ('l::len2)"
begin  

definition [simp]: "op_ivl_empty TYPE('l) = op_set_empty"
definition [simp]: "mop_ivl_empty TYPE('l) = mop_set_empty"
sepref_register 
  "op_ivl_empty TYPE('l)"
  "mop_ivl_empty TYPE('l)"

lemma ivl_empty_fold_aux:
  "op_set_empty = PR_CONST (op_ivl_empty TYPE('l))"
  "mop_set_empty = PR_CONST (mop_ivl_empty TYPE('l))" 
  by auto
  
lemmas [sepref_fr_rules] = 
  ivl_empty_hnr[where 'l='l,unfolded ivl_empty_fold_aux]
  ivl_empty_hnr_mop[where 'l='l,unfolded ivl_empty_fold_aux]
  
lemma ivl_fold_custom_empty:
  "{} = op_ivl_empty TYPE('l)"  
  "op_set_empty = op_ivl_empty TYPE('l)"  
  "mop_set_empty = mop_ivl_empty TYPE('l)"  
  by auto

end

definition "set_finite_inter s\<^sub>1 s\<^sub>2 \<equiv> doN {
  ASSERT (finite s\<^sub>2);
  
  (r,s) \<leftarrow> WHILEIT (\<lambda>(r,s). r \<union> s\<^sub>1\<inter>s = s\<^sub>1 \<inter> s\<^sub>2 \<and> r\<inter>s={} \<and> finite s ) (\<lambda>(r,s). \<not>op_set_is_empty s) (\<lambda>(r,s). doN {
    (ss,s') \<leftarrow> mop_set_rm_subset s;
    let ss = (ss\<inter>s\<^sub>1);
    r \<leftarrow> mop_set_union_disj ss r;
    RETURN (r,s')
  }) ({},s\<^sub>2);
  
  RETURN r
}"

lemma set_finite_inter_refine: "(set_finite_inter, mop_set_inter) \<in> Id \<rightarrow> b_rel Id finite \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding set_finite_inter_def
  apply clarsimp
  apply (refine_vcg WHILEIT_rule[where R="measure (card o snd)"])
  apply (auto simp: card_Un_disjoint) 
  done
  
  
sepref_definition set_finite_inter_iv_ivl_impl [llvm_code] is "uncurry set_finite_inter" 
  :: "(iv_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (ivl_assn' TYPE('l))\<^sup>d \<rightarrow>\<^sub>a ivl_assn' TYPE('l)"
  unfolding set_finite_inter_def
  apply (simp only: ivl_fold_custom_empty[where 'l='l])
  by sepref

sepref_definition set_finite_inter_lb_ivl_impl [llvm_code] is "uncurry set_finite_inter" 
  :: "(iv_lb_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (ivl_assn' TYPE('l))\<^sup>d \<rightarrow>\<^sub>a ivl_assn' TYPE('l)"
  unfolding set_finite_inter_def
  apply (simp only: ivl_fold_custom_empty[where 'l='l])
  by sepref_dbg_keep
    

lemma ivl_assn_comp_finite_eq: "hr_comp ivl_assn (b_rel Id finite) = ivl_assn"  
  apply (subst hr_comp_elim_b_rel)
  by (auto simp: ivl_assn_def ivl_rel_def in_br_conv)
  
context
  notes [fcomp_norm_simps] = ivl_assn_comp_finite_eq set_rel_id_simp
begin  

  private lemmas iv_ivl_refine = set_finite_inter_iv_ivl_impl.refine[FCOMP set_finite_inter_refine]
  private lemmas ivl_iv_refine = iv_ivl_refine[THEN hfref_ttnd_commute_op, simplified is_comm_simps Inter_is_commutative]
  
  private lemmas lb_ivl_refine = set_finite_inter_lb_ivl_impl.refine[FCOMP set_finite_inter_refine]
  private lemmas ivl_lb_refine = lb_ivl_refine[THEN hfref_ttnd_commute_op, simplified is_comm_simps Inter_is_commutative]
  
  private lemmas mop_set_inter_id_fref = mop_set_inter.fref[of Id, simplified id_set_constraint_simps]

  sepref_decl_impl (ismop) iv_ivl_refine uses mop_set_inter_id_fref .
  sepref_decl_impl (ismop) ivl_iv_refine uses mop_set_inter_id_fref .
  
  sepref_decl_impl (ismop) lb_ivl_refine uses mop_set_inter_id_fref .
  sepref_decl_impl (ismop) ivl_lb_refine uses mop_set_inter_id_fref .
end


definition "set_finite_incr_elems (n::nat) s\<^sub>0 \<equiv> doN {
  ASSERT (finite s\<^sub>0);
  
  (r,s) \<leftarrow> WHILEIT (\<lambda>(r,s). (+)n`s\<^sub>0 = r \<union> (+)n`s \<and> r \<inter> (+)n`s = {} \<and> finite s \<and> s \<subseteq> s\<^sub>0) (\<lambda>(r,s). \<not>op_set_is_empty s) (\<lambda>(r,s). doN {
    (ss,s') \<leftarrow> mop_set_rm_subset s;
    ASSERT(ss \<subseteq> s\<^sub>0);
    let ss = op_set_incr_elems n ss;
    r \<leftarrow> mop_set_union_disj ss r;
    RETURN (r,s')
  }) ({},s\<^sub>0);
  
  RETURN r
}"


lemma set_finite_incr_elems_refine: "(set_finite_incr_elems, mop_set_incr_elems) \<in> Id \<rightarrow> b_rel Id finite \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding set_finite_incr_elems_def
  apply clarsimp
  apply (refine_vcg WHILEIT_rule[where R="measure (card o snd)"])
  by (auto simp: card_Un_disjoint)

  
find_theorems "Max" "(\<subseteq>)" 
  
lemma iv_incr_elems_pre_mono: "iv_incr_elems_pre s n N \<Longrightarrow> finite s \<Longrightarrow> s'\<subseteq>s \<Longrightarrow> iv_incr_elems_pre s' n N" for n :: nat 
  unfolding iv_incr_elems_pre_def
  by (auto dest: Max_mono)


definition "iv_incr_elems_abs_bound (s::nat set) n N \<equiv> s\<noteq>{} \<longrightarrow> Max s + n < N"  
  
lemma iv_incr_elems_pre_from_abs_boundI[elim!]: "iv_incr_elems_abs_bound s n N \<Longrightarrow> N<N' \<Longrightarrow> iv_incr_elems_pre s n N'"
  unfolding iv_incr_elems_abs_bound_def iv_incr_elems_pre_def by auto
  
lemma iv_incr_elems_abs_bound_card_boundI:   
  "s \<subseteq> {0..<N} \<Longrightarrow> N+n\<le>N' \<Longrightarrow> iv_incr_elems_abs_bound s n N'"
  unfolding iv_incr_elems_abs_bound_def
  apply clarsimp
  apply (frule Max_mono)
  by auto
  

lemma iv_incr_elems_abs_bound_card_boundI': "(+)n`s \<subseteq> {0..<N} \<Longrightarrow> iv_incr_elems_abs_bound s n N"  
  unfolding iv_incr_elems_abs_bound_def
  apply clarsimp
  apply (subgoal_tac "n\<le>N" "s\<subseteq>{0..<N-n}")
  apply (frule Max_mono[of s]; simp?)
  by auto
  
    
lemma "s \<subseteq> {0..<N} \<Longrightarrow> N+n<N' \<Longrightarrow> iv_incr_elems_pre s n N'"  
  unfolding iv_incr_elems_pre_def
  apply clarsimp
  apply (frule Max_mono)
  by auto
    
lemma "(+)n`s \<subseteq> {0..<N} \<Longrightarrow> N<N' \<Longrightarrow> iv_incr_elems_pre s n N'"  
  unfolding iv_incr_elems_pre_def
  apply clarsimp
  apply (subgoal_tac "n\<le>N" "s\<subseteq>{0..<N-n}")
  apply (frule Max_mono[of s]; simp?)
  by auto
  
  
  
context
  fixes L
  defines "L \<equiv> LENGTH('l::len2)"
begin  
sepref_definition set_finite_incr_elems_ivl_impl [llvm_code] is "uncurry set_finite_incr_elems" 
  :: "[\<lambda>(n,s). iv_incr_elems_pre s n (max_snat L) ]\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (ivl_assn' TYPE('l))\<^sup>d \<rightarrow> ivl_assn' TYPE('l)"
  unfolding set_finite_incr_elems_def L_def
  apply (simp only: ivl_fold_custom_empty[where 'l='l])
  supply [elim] = iv_incr_elems_pre_mono
  by sepref
  

  context
    notes [fcomp_norm_simps] = ivl_assn_comp_finite_eq set_rel_id_simp
  begin  
    sepref_decl_impl (ismop) set_finite_incr_elems_ivl_impl.refine[FCOMP set_finite_incr_elems_refine] by simp
  end

end

end
