section \<open>Reasoning about Values\<close>
theory Sep_Value_RS
imports Sep_Value
begin

  subsection \<open>Lifting Scheme on Maps\<close>
  definition "prefix_map1 i m \<equiv> \<lambda>[] \<Rightarrow> None | i'#as \<Rightarrow> if i=i' then m as else None"
  definition "project_map1 i m \<equiv> \<lambda>a. m (i#a)"  
  definition "carve_map1 i m \<equiv> \<lambda>[] \<Rightarrow> m [] | i'#a \<Rightarrow> if i=i' then None else m (i'#a)"  
  definition "prefix_adom1 va d = (#)va`d"
    
  
  lemma prefix_map1_apply: "prefix_map1 i m xs = (case xs of [] \<Rightarrow> None | j#as \<Rightarrow> if i=j then m as else None)"  
    by (auto simp: prefix_map1_def)
    
  lemma project_map1_apply: "project_map1 i m xs = m (i#xs)"  
    by (auto simp: project_map1_def)
    
  lemmas lift_map_apply = prefix_map1_apply project_map1_apply
  
  
  (* Lemmas for prefix_map *)
  lemma prefix_map1_empty[simp]: 
    "prefix_map1 i Map.empty = Map.empty"
    "prefix_map1 i m = Map.empty \<longleftrightarrow> m=Map.empty"
    by (auto simp: prefix_map1_def fun_eq_iff split: if_splits list.splits)

  lemma prefix_map1_add_distrib[simp]: "prefix_map1 i (a\<^sub>1 ++ a\<^sub>2) = prefix_map1 i a\<^sub>1 ++ prefix_map1 i a\<^sub>2"  
    apply (rule ext)
    by (auto simp: prefix_map1_def map_add_def split: list.splits option.splits)
    
  lemma prefix_map_complete_eq_iff[simp]:
    "prefix_map1 PFST a ++ prefix_map1 PSND b = prefix_map1 PFST a' ++ prefix_map1 PSND b'
    \<longleftrightarrow> a=a' \<and> b=b'"
    apply (auto simp: fun_eq_iff map_add_def prefix_map1_def split: option.split list.split)
    by (metis option.exhaust va_item.distinct(1))
    
  (* Lemmas for project_map *)
  lemma project_map1_empty[simp]: "project_map1 i Map.empty = Map.empty"
    by (auto simp: project_map1_def)
  
  lemma dom_project_map1_iff[simp]: "dom (project_map1 i b) = { a. i#a \<in> dom b}"  
    by (auto simp: project_map1_def)
    
  lemma project_map_add_distrib[simp]: "project_map1 i (b\<^sub>1 ++ b\<^sub>2) = project_map1 i b\<^sub>1 ++ project_map1 i b\<^sub>2"
    apply (rule ext)
    by (auto simp: project_map1_def map_add_def)
    
  lemma project_map_prefix_id[simp]: "project_map1 i (prefix_map1 i a) = a"
    apply (rule ext)
    by (auto simp: project_map1_def prefix_map1_def)
  
  (* Lemmas for carve_map *)
  
  lemma carve_map1_empty[simp]:
    "carve_map1 i Map.empty = Map.empty"
    by (rule ext) (auto simp: carve_map1_def split: list.splits)
  
  lemma carve_map1_dom[simp]: "dom (carve_map1 i v) = dom v - {i # as |as. True}"  
    by (auto simp: carve_map1_def split: list.splits if_splits)

  lemma carve_map_add_distrib[simp]: "carve_map1 i (b\<^sub>1 ++ b\<^sub>2) = carve_map1 i b\<^sub>1 ++ carve_map1 i b\<^sub>2"
    apply (rule ext)
    by (auto simp: carve_map1_def map_add_def split: list.splits if_splits)
    
  lemma project_carve_empty[simp]: "project_map1 i (carve_map1 i b) = Map.empty"
    apply (rule ext)
    by (auto simp: carve_map1_def project_map1_def split: list.splits if_splits)
    
  lemma carve_prefix_empty[simp]: "carve_map1 i (prefix_map1 i a) = Map.empty"
    apply (rule ext)
    by (auto simp: carve_map1_def prefix_map1_def split: list.splits if_splits)

  (* Lemmas for prefix-domain *)  
  lemma prefix_adom_empty[simp]: 
    "prefix_adom1 i {} = {}"
    by (auto simp: prefix_adom1_def)
  
  lemma prefix_adom_empty_iff[simp]:
    "prefix_adom1 i d = {} \<longleftrightarrow> d={}"  
    by (auto simp: prefix_adom1_def)
  
  lemma prefix_adom_insert[simp]:
    "prefix_adom1 i (insert d e) = insert (i#d) (prefix_adom1 i e)"
    by (auto simp: prefix_adom1_def)
        
  lemma prefix_adom_union[simp]:
    "prefix_adom1 i (d\<union>e) = prefix_adom1 i d \<union> prefix_adom1 i e"
    by (auto simp: prefix_adom1_def)
    
  lemma in_prefix_adom_conv[simp]:
    "x\<in>prefix_adom1 i d \<longleftrightarrow> (\<exists>va'\<in>d. x=i#va')"
    by (auto simp: prefix_adom1_def)
    
  lemma prefix_map1_dom[simp]: "dom (prefix_map1 i m) = prefix_adom1 i (dom m)"  
    by (auto simp: prefix_map1_def split: list.splits if_splits)
    
  lemma map1_split_complete: "prefix_map1 i (project_map1 i b) ++ carve_map1 i b = b"
    apply (rule ext)
    apply (auto simp: prefix_map1_def project_map1_def carve_map1_def map_add_def split: list.splits option.splits)
    done
    
  lemma project_map1_prefix_diff[simp]: "i\<noteq>j \<Longrightarrow> project_map1 i (prefix_map1 j a) = Map.empty"
    apply (rule ext)
    apply (auto simp: project_map1_def prefix_map1_def)
    done

  lemma carve_map1_prefix_diff[simp]: "i\<noteq>j \<Longrightarrow> carve_map1 i (prefix_map1 j a) = prefix_map1 j a"
    apply (rule ext)
    apply (auto simp: prefix_map1_def carve_map1_def split: list.splits)
    done
    
  subsection \<open>Independence of Addresses\<close>
  
  lemma lens_of_item_indepI: "i\<noteq>i' \<Longrightarrow> lens_of_item i \<bowtie> lens_of_item i'"
    apply (cases i; cases i')
    apply (simp_all add: lens_indep_sym)
    done
    
  lemma lens_of_item_indepD: "lens_of_item i \<bowtie> lens_of_item i' \<Longrightarrow> i\<noteq>i'"
    apply (cases i; cases i')
    apply (simp_all add: lens_indep_sym)
    apply (meson hlens_def lens.pre_get_imp_putI rnl_indep_not_refl rnlensI val.discI(1) val.distinct(1) val.fst\<^sub>L_lens val.fst\<^sub>L_pre_disc)
    by (meson hlens_def lens.pre_get_imp_putI rnl_indep_not_refl rnlensI val.discI(1) val.distinct(1) val.snd\<^sub>L_lens val.snd\<^sub>L_pre_disc)
  
  lemma lens_of_item_indep_eq[simp]: "lens_of_item i \<bowtie> lens_of_item i' \<longleftrightarrow> i\<noteq>i'"  
    using lens_of_item_indepI lens_of_item_indepD by blast

    
    
  definition "vaddr_indep va va' \<longleftrightarrow> (lens_of_vaddr va :: unit val \<Longrightarrow> _) \<bowtie> lens_of_vaddr va'"  
      
  lemma "\<not>(lens_of_vaddr [] \<bowtie> lens_of_vaddr va)" by simp 
  lemma "\<not>(lens_of_vaddr va \<bowtie> lens_of_vaddr [])" by simp 
  
  lemma lens_of_vaddr_indep_Cons: "(lens_of_vaddr (i#is) :: 'a val \<Longrightarrow> _) \<bowtie> lens_of_vaddr (j#js) 
    \<longleftrightarrow> i\<noteq>j \<or> (lens_of_vaddr is :: 'a val \<Longrightarrow> _) \<bowtie> lens_of_vaddr js"
    apply (cases "i=j")
    by (auto simp: lens_indep_extend2)
    
  lemma lens_of_vaddr_indep_normalize:
    assumes "NO_MATCH TYPE(unit) TYPE('a)"
    shows "lens_of_vaddr va \<bowtie> (lens_of_vaddr va' :: 'a val \<Longrightarrow> _) \<longleftrightarrow> lens_of_vaddr va \<bowtie> (lens_of_vaddr va' :: unit val \<Longrightarrow> _)"  
  proof (induction va arbitrary: va')
    case Nil
    then show ?case by auto
  next
    case (Cons a va)
    then show ?case 
      apply (cases va')
      apply simp
      apply (simp only: lens_of_vaddr_indep_Cons)
      done
    
  qed

  lemma vaddr_indep_alt: "vaddr_indep a b \<longleftrightarrow> lens_of_vaddr a \<bowtie> lens_of_vaddr b"  
    using lens_of_vaddr_indep_normalize vaddr_indep_def by auto
    
  lemma vaddr_indep_irrefl[simp, intro!]: "\<not>vaddr_indep a a"
    unfolding vaddr_indep_def by auto
    
  lemma vaddr_indep_sym: "vaddr_indep a b \<Longrightarrow> vaddr_indep b a"
    unfolding vaddr_indep_def
    using lens_indep_sym by auto


  lemma vaddr_indep_Nil:
    "\<not>vaddr_indep [] va"
    "\<not>vaddr_indep va []"
    by (simp_all add: vaddr_indep_def)
  
  lemma vaddr_indep_Cons:
    "vaddr_indep (a#va\<^sub>1) (b#va\<^sub>2) \<longleftrightarrow> (a\<noteq>b \<or> vaddr_indep va\<^sub>1 va\<^sub>2)"
    using lens_of_vaddr_indep_Cons vaddr_indep_def by auto
    
  lemmas vaddr_indep_simps[simp] = vaddr_indep_Nil vaddr_indep_Cons
    
  lemma vaddr_indep_prefix[simp]: "vaddr_indep (va@va\<^sub>1) (va@va\<^sub>2) \<longleftrightarrow> vaddr_indep va\<^sub>1 va\<^sub>2"
    by (induction va) auto
  
  definition "s_indep s1 s2 \<equiv> \<forall>x\<in>s1. \<forall>y\<in>s2. vaddr_indep x y"

  lemma s_indep_irrefl[simp]: "s_indep m m \<longleftrightarrow> m={}"
    by (force simp: s_indep_def) 
  
  lemma s_indep_sym: "s_indep s1 s2 \<Longrightarrow> s_indep s2 s1"
    by (auto simp: s_indep_def vaddr_indep_sym)
  
  lemma s_indep_imp_disj: "s_indep s1 s2 \<Longrightarrow> s1 \<inter> s2 = {}"
    by (force simp: s_indep_def)
  
  lemma s_indep_simps[simp]:
    "s_indep {} s"  
    "s_indep s {}"  
    "s_indep (insert x s) r \<longleftrightarrow> (\<forall>y\<in>r. vaddr_indep x y) \<and> s_indep s r"
    "s_indep r (insert x s) \<longleftrightarrow> (\<forall>y\<in>r. vaddr_indep y x) \<and> s_indep r s"
    by (auto simp: s_indep_def)
    
  lemma s_indep_union[simp]:  
    "s_indep (a\<union>b) c \<longleftrightarrow> s_indep a c \<and> s_indep b c"
    "s_indep a (b\<union>c) \<longleftrightarrow> s_indep a b \<and> s_indep a c"
    by (auto simp: s_indep_def)

  lemma s_indep_ne[simp, intro]: 
    "[]\<in>s\<^sub>1 \<Longrightarrow> s_indep s\<^sub>1 s\<^sub>2 \<longleftrightarrow> s\<^sub>2={}"  
    "[]\<in>s\<^sub>2 \<Longrightarrow> s_indep s\<^sub>1 s\<^sub>2 \<longleftrightarrow> s\<^sub>1={}"  
    by (all \<open>force simp: s_indep_def\<close>)
      
  lemma s_indep_projectI: "s_indep s\<^sub>1 s\<^sub>2 \<Longrightarrow> s_indep {a. i # a \<in> s\<^sub>1} {a. i # a \<in> s\<^sub>2}"
    apply (auto simp: s_indep_def)
    using vaddr_indep_Cons by blast

  lemma s_indep_mono: "s_indep s\<^sub>1 s\<^sub>2 \<Longrightarrow> s\<^sub>1'\<subseteq>s\<^sub>1 \<Longrightarrow> s\<^sub>2'\<subseteq>s\<^sub>2 \<Longrightarrow> s_indep s\<^sub>1' s\<^sub>2'"  
    by (auto simp: s_indep_def)
  
    
  lemma s_indep_Cons[simp]: "s_indep (prefix_adom1 a s\<^sub>1) (prefix_adom1 b s\<^sub>2) \<longleftrightarrow> a\<noteq>b \<or> s_indep s\<^sub>1 s\<^sub>2"
    by (auto simp: s_indep_def prefix_adom1_def)

  lemma s_indep_project_shift_prefix:  
    "\<lbrakk>[] \<notin> dom b; s_indep (dom a) (dom (project_map1 i b))\<rbrakk>
       \<Longrightarrow> s_indep (dom (prefix_map1 i a)) (dom b)"
    apply (clarsimp simp: s_indep_def) 
    by (metis domI neq_Nil_conv option.distinct(1) vaddr_indep_Cons vaddr_indep_sym)
       
  lemma s_indep_carve_prefix:
    "[] \<notin> dom b \<Longrightarrow> s_indep (dom (carve_map1 i b)) (dom (prefix_map1 i a))"
    apply (clarsimp simp: s_indep_def) 
    by (metis neq_Nil_conv option.distinct(1) vaddr_indep_Cons)
    


  subsection \<open>Separation Algebra for Values\<close>  
          
  typedef 'a aval = "{ m :: vaddr \<rightharpoonup> 'a. \<forall>va\<in>dom m. \<forall>va'\<in>dom m. va\<noteq>va' \<longrightarrow> vaddr_indep va va' }" by auto
  
  setup_lifting type_definition_aval  
    
  instantiation aval :: (type) unique_zero_sep_algebra
  begin
    lift_definition sep_disj_aval :: "'a aval \<Rightarrow> 'a aval \<Rightarrow> bool" is "\<lambda>x y. s_indep (dom x) (dom y)" .
    lift_definition plus_aval :: "'a aval \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is "\<lambda>m1 m2. if s_indep (dom m1) (dom m2) then m1 ++ m2 else Map.empty"
      apply (auto split: if_splits simp: s_indep_def) apply blast apply blast
      by (meson domI vaddr_indep_sym)
  
    lift_definition zero_aval :: "'a aval" is "Map.empty" by simp
      
    instance
      apply standard
      apply (determ transfer; auto simp: s_indep_def)
      apply (determ transfer; auto simp: s_indep_def dom_def; metis vaddr_indep_sym)
      apply (determ transfer; auto simp: s_indep_def)
      apply (determ transfer; auto simp: s_indep_imp_disj simp: map_add_comm s_indep_sym)
      apply (determ transfer; clarsimp; meson UnE s_indep_def)
      apply (determ transfer; unfold s_indep_def; auto simp: domI)
      apply (determ transfer; simp)
      done
    
  end
      
    
  subsection \<open>Lifting Scheme on \<open>aval\<close>\<close>
  lift_definition prefix_aval1 :: "va_item \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is prefix_map1 by auto auto
  lift_definition prim_aval :: "'a \<Rightarrow> 'a aval" is "\<lambda>x. [[] \<mapsto> x]" by simp
  lift_definition adom :: "'a aval \<Rightarrow> vaddr set" is "dom" .
  lift_definition project_aval1 :: "va_item \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is project_map1
    apply (auto simp: project_map1_def)
    by (meson domI list.inject vaddr_indep_Cons)

  lift_definition carve_aval1 :: "va_item \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is carve_map1
    by (fastforce simp: carve_map1_def split: list.splits if_splits)

  lemma indep_prefix_aux1: "[]\<notin>dom b \<Longrightarrow> s_indep (prefix_adom1 i {a. i # a \<in> dom b}) (dom b - {as'. \<exists>as. as' = i # as})"  
    apply (auto simp: prefix_adom1_def s_indep_def)
    by (metis neq_Nil_conv option.distinct(1) vaddr_indep_Cons)
    
  lemma carve_indep_id_aux1: "\<lbrakk>\<forall>va\<in>dom i. \<forall>va'\<in>dom i. va \<noteq> va' \<longrightarrow> vaddr_indep va va'; \<not> [] \<notin> dom i\<rbrakk> \<Longrightarrow> carve_map1 b i = i"  
    apply (rule ext)
    apply (auto simp: carve_map1_def split: list.split)
    by (metis domIff list.distinct(1) option.distinct(1) vaddr_indep_simps(1))
    
  interpretation aval_lifting_scheme: sep_lifting_scheme "prefix_aval1 i" "project_aval1 i" "carve_aval1 i" "\<lambda>x. []\<notin>adom x"
    apply unfold_locales
    apply (all \<open>determ transfer\<close>)
    apply (all \<open>(simp;fail)?\<close>)
    subgoal by (auto simp: domI) []
    subgoal by (auto ) []
    subgoal by (auto simp: domI s_indep_projectI) []
    subgoal by (auto simp: domI s_indep_projectI) []
    subgoal by (auto intro: s_indep_mono)
    subgoal by (auto intro: s_indep_mono)
    subgoal by (rule s_indep_project_shift_prefix)
    subgoal by (rule s_indep_carve_prefix)
    subgoal by (auto simp: map1_split_complete indep_prefix_aux1) []
    subgoal by (auto simp: carve_indep_id_aux1)
    done

  subsubsection \<open>Additional Lemmas\<close>  
  lemma adomZ[simp]: "adom 0 = {}"
    apply transfer by auto
    
  lemma adom_Z_iff[simp]: "adom v = {} \<Longrightarrow> v = 0"
    by (determ transfer) auto
  
  lemma disj_eq_adom: "a##b \<longleftrightarrow> s_indep (adom a) (adom b)"
    apply transfer by (auto simp: s_indep_def)
  
  lemma adom_plus[simp]: "a##b \<Longrightarrow> adom (a+b) = adom a \<union> adom b"
    apply transfer by auto
  
  lemma adom_primval[simp]: "adom (prim_aval x) = {[]}"
    apply transfer by auto
    
  lemma adom_prefix[simp]: "adom (prefix_aval1 i v) = (prefix_adom1 i (adom v))"  
    by (determ transfer) auto
    
  lemma aval_project_prefix_diff[simp]: "i\<noteq>j \<Longrightarrow> project_aval1 i (prefix_aval1 j a) = 0"  
    apply transfer by auto 
    
  lemma carve_aval_prefix_diff[simp]: "i\<noteq>j \<Longrightarrow> carve_aval1 i (prefix_aval1 j a) = prefix_aval1 j a"
    apply transfer by auto
    
  lemma adom_cases: obtains (primitive) "adom a = {[]}" | (compound) "[]\<notin>adom a"
    by transfer force    
    
  lemma va_item_complete:
    "i\<noteq>PFST \<Longrightarrow> i=PSND"
    "i\<noteq>PSND \<Longrightarrow> i=PFST"
    "PFST\<noteq>i \<Longrightarrow> i=PSND"
    "PSND\<noteq>i \<Longrightarrow> i=PFST"
    by (all \<open>cases i; auto\<close>)
  
    
  lemma aval_cases:
    obtains (primitive) x where "v = prim_aval x" 
          | (compound) v\<^sub>1 v\<^sub>2 where "v = prefix_aval1 PFST v\<^sub>1 + prefix_aval1 PSND v\<^sub>2"
  proof -
    have "(\<exists>x. v = prim_aval x) \<or> (\<exists>v\<^sub>1 v\<^sub>2. v = prefix_aval1 PFST v\<^sub>1 + prefix_aval1 PSND v\<^sub>2)"
    proof (transfer, goal_cases)
      case (1 v)
      assume INDEP: "\<forall>vaa\<in>dom v. \<forall>va'\<in>dom v. vaa \<noteq> va' \<longrightarrow> vaddr_indep vaa va'"
      then consider (primitive) "dom v = {[]}" | (compound) "[]\<notin>dom v" by force
      then show ?case proof cases
        case primitive
        then show ?thesis
          apply (rule_tac disjI1)
          by (simp add: dom_eq_singleton_conv)
        
      next
        case compound
        then show ?thesis 
          apply (rule_tac disjI2)
          apply (rule bexI[where x="project_map1 PFST v"])
          apply (rule bexI[where x="project_map1 PSND v"])
          subgoal
            apply (rule ext)
            subgoal for x
              apply (cases x)
              apply (auto simp add: map_add_def lift_map_apply dest: va_item_complete split: option.splits)
              done
            done
          using INDEP  
          apply clarsimp_all
          apply (meson domI list.inject vaddr_indep_Cons)+
          done  
            
      qed
    qed
    thus ?thesis using that by blast
  qed
    
  lemma prim_aval_complete[simp]: 
    "prim_aval x ## v \<longleftrightarrow> v=0"
    "v ## prim_aval x \<longleftrightarrow> v=0"
    by (auto simp: disj_eq_adom)
    
  lemma prim_aval_neqZ[simp]: "prim_aval x \<noteq> 0"  
    by (metis adomZ adom_primval empty_iff insert_iff)
  
  lemma prefix_aval_complete_eq_iff[simp]:
    "prefix_aval1 PFST a + prefix_aval1 PSND b = prefix_aval1 PFST a' + prefix_aval1 PSND b'
    \<longleftrightarrow> a=a' \<and> b=b'"
    apply transfer
    apply auto
    done
    
  lemma prefix_aval_split_ne_prim: "prefix_aval1 PFST a + prefix_aval1 PSND b \<noteq> prim_aval x"  
  proof -
    have "adom (prefix_aval1 PFST a + prefix_aval1 PSND b) \<noteq> {[]}"
      by (metis aval_lifting_scheme.carve_disj_lift(2) aval_lifting_scheme.splittable_add_distrib aval_lifting_scheme.splittable_lift carve_aval_prefix_diff insertI1 va_item.distinct(1))
    then show ?thesis
      by (rule_tac ccontr; simp)
  qed    
    
  lemma prim_aval_inj[simp]: "prim_aval x = prim_aval y \<longleftrightarrow> x = y"
    apply transfer
    apply (auto simp: fun_eq_iff split: if_splits)
    done
    
    
  subsection \<open>Lifter for Value Address Items\<close>  
  
  fun val_dom where
    "val_dom (PRIMITIVE x) = {[]}"  
  | "val_dom (PAIR x y) = prefix_adom1 PFST (val_dom x) \<union> prefix_adom1 PSND (val_dom y)"
  
  fun val_\<alpha> where
    "val_\<alpha> (PRIMITIVE x) = prim_aval x"  
  | "val_\<alpha> (PAIR x y) = prefix_aval1 PFST (val_\<alpha> x) + prefix_aval1 PSND (val_\<alpha> y)"
  
  lemma ne_prefix_disjI[simp, intro]: "i\<noteq>j \<Longrightarrow> prefix_aval1 i v\<^sub>1 ## prefix_aval1 j v\<^sub>2"
    by (auto simp add: disj_eq_adom)  
  
  lemma adom_val_\<alpha>[simp]: "adom (val_\<alpha> x) = val_dom x"
    by (induction x) (auto)
  
    
  definition "val_item_lifter i \<equiv> \<lparr>
    sep_lifter.lift = prefix_aval1 i,
    sep_lifter.project = project_aval1 i,
    sep_lifter.carve = carve_aval1 i,
    sep_lifter.splittable = \<lambda>a. [] \<notin> adom a,
    sep_lifter.L = lens_of_item i,
    sep_lifter.\<alpha>b = val_\<alpha>,
    sep_lifter.\<alpha>s = val_\<alpha>,
    sep_lifter.tyb = \<lambda>_. (),
    sep_lifter.tys = \<lambda>_. ()
  \<rparr>"
  
  lemma val_item_lifter_simps[simp]:
    "sep_lifter.lift (val_item_lifter i) = prefix_aval1 i"
    "sep_lifter.project (val_item_lifter i) = project_aval1 i"
    "sep_lifter.carve (val_item_lifter i) = carve_aval1 i"
    "sep_lifter.splittable (val_item_lifter i) = (\<lambda>a. [] \<notin> adom a)"
    "sep_lifter.L (val_item_lifter i) = lens_of_item i"
    "sep_lifter.\<alpha>b (val_item_lifter i) = val_\<alpha>"
    "sep_lifter.\<alpha>s (val_item_lifter i) = val_\<alpha>"
    "sep_lifter.tyb (val_item_lifter i) = (\<lambda>_. ())"
    "sep_lifter.tys (val_item_lifter i) = (\<lambda>_. ())"
    by (auto simp: val_item_lifter_def)
  
  
  lemma val_item_lifter[simp, intro!]: "sep_lifter (val_item_lifter i)"
    apply intro_locales
    subgoal by (simp add: val_item_lifter_def) unfold_locales
    subgoal
      apply (rule sep_lifter_axioms.intro)
      apply (clarsimp_all simp: val_item_lifter_def)
    
      subgoal for cb by (cases cb; cases i) auto
      subgoal for cb 
        apply (cases cb; cases i)
        apply (auto simp:  )
        done          
      subgoal for cb x
        apply (cases cb; cases i)
        apply (auto simp: sep_algebra_simps)
        done          
      done
    done
      
  
      
    
  lemma val_\<alpha>_neqZ[simp]: "val_\<alpha> x \<noteq> 0"
    by (induction x) auto
    
  lemma val_\<alpha>_complete[simp]: "val_\<alpha> v ## x \<longleftrightarrow> x=0"
  proof (induction v arbitrary: x)
    case (PAIR v1 v2)
    show ?case 
      apply (cases x rule: aval_cases)
      apply (auto simp: PAIR.IH)
      done
    
  next
    case (PRIMITIVE y)
    then show ?case 
      by (cases x rule: aval_cases) auto
  qed
    
  lemma val_\<alpha>_inj[simp]: "val_\<alpha> v = val_\<alpha> v' \<longleftrightarrow> v=v'"
  proof (induction v arbitrary: v')
    case (PAIR v1 v2)
    then show ?case 
      by (cases v') (auto simp: prefix_aval_split_ne_prim)
    
  next
    case (PRIMITIVE x)
    then show ?case
      apply (cases v')
      apply auto
      by (metis prefix_aval_split_ne_prim)
  qed
  
    
    
    
    
  subsection \<open>Lifter for Value Addresses\<close>  
  
  definition "vaddr_lifter addr = foldr (\<lambda>i l. l \<bullet>\<^sub>l\<^sub>f\<^sub>t val_item_lifter i) addr (id_lifter (\<lambda>_. ()) val_\<alpha>)"  
    
  lemma vaddr_lifter_rec_simps:
    "vaddr_lifter [] = id_lifter (\<lambda>_. ()) val_\<alpha>"
    "vaddr_lifter (i#a) = vaddr_lifter a \<bullet>\<^sub>l\<^sub>f\<^sub>t val_item_lifter i"
    unfolding vaddr_lifter_def by auto
  
  lemma vaddr_lifter_\<alpha>s_simp: "sep_lifter.\<alpha>s (vaddr_lifter addr) = val_\<alpha>"
    apply (induction addr) apply (auto simp: vaddr_lifter_rec_simps compose_lifter_simps) done

  lemma vaddr_lifter_\<alpha>b_simp: "sep_lifter.\<alpha>b (vaddr_lifter addr) = val_\<alpha>"
    apply (induction addr) apply (auto simp: vaddr_lifter_rec_simps compose_lifter_simps) done
  
  lemma vaddr_lifter_L_simp: "sep_lifter.L (vaddr_lifter addr) = lens_of_vaddr addr"  
    apply (induction addr)
    apply (auto simp: vaddr_lifter_rec_simps compose_lifter_simps)
    done

  lemmas vaddr_lifter_simps[simp] = vaddr_lifter_\<alpha>s_simp vaddr_lifter_\<alpha>b_simp vaddr_lifter_L_simp
    
  lemma vaddr_lifter[simp, intro!]: "sep_lifter (vaddr_lifter addr)"
    apply (induction addr) apply (auto simp: vaddr_lifter_rec_simps compose_lifter_simps) done

    
  interpretation val_item_lifter: sep_lifter "val_item_lifter i" for i by simp  
  interpretation vaddr_lifter: sep_lifter "vaddr_lifter addr" for addr by simp
    
    
  lemma vaddr_lift_Nil[simp]: "vaddr_lifter.lift [] = id"
    by (auto simp: vaddr_lifter_def id_lifter_def)
    
  lemma vaddr_lift_Cons[simp]: "vaddr_lifter.lift (i#as) = prefix_aval1 i o vaddr_lifter.lift as"  
    apply (rule ext)
    apply (auto simp: vaddr_lifter_rec_simps compose_lifter_simps)
    done
    
  lemma vaddr_lift_append[simp]: "vaddr_lifter.lift (as\<^sub>1@as\<^sub>2) = vaddr_lifter.lift as\<^sub>1 o vaddr_lifter.lift as\<^sub>2"  
    by (induction as\<^sub>1) auto
    
    
  subsection \<open>Points-To Assertion for Values\<close>  
    
  definition "vpto_assn v addr \<equiv> vaddr_lifter.lift_assn addr (EXACT (val_\<alpha> v))"
  
  lemma vpto_assn_split: "vpto_assn (PAIR a b) addr = (vpto_assn a (addr@[PFST]) ** vpto_assn b (addr@[PSND]))" 
    by (auto simp: vpto_assn_def EXACT_split)
  
  lemma vpto_assn_notZ[simp]: "\<not> vpto_assn x a 0"
    by (auto simp: vpto_assn_def)
    
  lemma vpto_assn_this[simp]: "vpto_assn v [] av = (av = val_\<alpha> v)"
    by (auto simp: vpto_assn_def)
    
    
  subsection \<open>Hoare-Triples for Load and Store\<close>  
    
  
  lemma get_aval_rule: "htriple val_\<alpha> (EXACT (val_\<alpha> v)) Monad.get (\<lambda>r. \<up>(r=v) ** EXACT (val_\<alpha> v))"
    apply (rule htripleI')
    apply (auto simp: wp_def run_simps)
    apply (auto simp: sep_algebra_simps)
    done
  
  lemma set_aval_rule: "htriple val_\<alpha> (EXACT (val_\<alpha> v)) (Monad.set v') (\<lambda>_. EXACT (val_\<alpha> v'))"
    apply (rule htripleI')
    apply (auto simp: wp_def run_simps)
    done
  
  
  lemma vload_rule: "htriple val_\<alpha> (vpto_assn v a) (vload err a) (\<lambda>r. \<up>(r=v) ** vpto_assn v a)"  
    unfolding vload_def vpto_assn_def
    apply (rule cons_post_rule)
    apply (rule vaddr_lifter.lift_operation[simplified])
    apply simp
    apply (rule get_aval_rule)
    by auto
    
  lemma vstore_rule: "htriple val_\<alpha> (vpto_assn v a) (vstore err v' a) (\<lambda>_. vpto_assn v' a)"
    unfolding vstore_def vpto_assn_def
    apply (rule cons_post_rule)
    apply (rule vaddr_lifter.lift_operation[simplified])
    apply simp
    apply (rule set_aval_rule)
    by auto
  
    
  lifting_forget aval.lifting

end
