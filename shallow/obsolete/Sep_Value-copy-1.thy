theory Sep_Value
imports Sep_Lift
begin

  (* Prototype value model *)
  
  datatype 'a val = PAIR (fst: "'a val") (snd: "'a val") | PRIMITIVE (the: 'a)
  hide_const (open) fst snd the
  define_lenses (open) val
  
  datatype va_item = PFST | PSND
  type_synonym vaddr = "va_item list"
  
  fun lens_of_item where
    "lens_of_item PFST = val.fst\<^sub>L"  
  | "lens_of_item PSND = val.snd\<^sub>L"
  
  definition "lens_of_vaddr vp = foldr (\<lambda>i L. lens_of_item i \<bullet>\<^sub>L L) vp id\<^sub>L"
  
  lemma lens_of_vaddr_simps[simp]:
    "lens_of_vaddr [] = id\<^sub>L"
    "lens_of_vaddr (i#is) = lens_of_item i \<bullet>\<^sub>L lens_of_vaddr is"
    unfolding lens_of_vaddr_def
    by auto
  
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

  lemma ex_two_vals[simp, intro]: "\<exists>a b::'a val. a \<noteq> b" by auto

  lemma lens_of_item_rnl[simp, intro!]: "rnlens (lens_of_item i :: 'a val \<Longrightarrow> 'a val)"  
  proof -
    have A: "is_PAIR (PAIR undefined undefined :: 'a val)" by simp
  
    show ?thesis
      by (cases i) (auto intro!: rnlensI A)
  qed

  lemma lens_of_item_hlens[simp, intro!]: "hlens (lens_of_item i :: 'a val \<Longrightarrow> 'a val)"  
    by (cases i) (auto)
  
  
  lemma lens_of_vaddr_rnl[simp, intro!]: "rnlens (lens_of_vaddr vp)"
    by (induction vp) auto
  
  lemma lens_of_vaddr_hlens[simp, intro!]: "hlens (lens_of_vaddr vp)"
    by (induction vp) auto
    
  lemma lens_of_item_complete[simp, intro!]: "complete_lens (lens_of_item i)"
    apply (rule)
    apply (simp; fail)
    using val.discI(1)
    by (cases i; fastforce)
    
    
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

    
  definition "prefix_adom1 va d = (#)va`d"
  definition "prefix_adom va d = (@)va`d"
    
  lemma prefix_adom_empty[simp]: 
    "prefix_adom [] d = d"
    "prefix_adom a {} = {}"
    "prefix_adom1 i {} = {}"
    by (auto simp: prefix_adom_def prefix_adom1_def)
  
  lemma in_prefix_adom_conv[simp]:
    "x\<in>prefix_adom va d \<longleftrightarrow> (\<exists>va'\<in>d. x=va@va')"
    "x\<in>prefix_adom1 i d \<longleftrightarrow> (\<exists>va'\<in>d. x=i#va')"
    by (auto simp: prefix_adom_def prefix_adom1_def)
    
  lemma prefix_adom_empty_iff[simp]:
    "prefix_adom va d = {} \<longleftrightarrow> d={}"  
    "prefix_adom1 i d = {} \<longleftrightarrow> d={}"  
    by (auto simp: prefix_adom_def prefix_adom1_def)
    
    
  lemma prefix_adom_Cons[simp]: "prefix_adom (i#a) d = prefix_adom1 i (prefix_adom a d)"  
    by (auto simp: prefix_adom_def prefix_adom1_def)
    
  lemma prefix_adom_append[simp]: "prefix_adom (a@b) s = prefix_adom a (prefix_adom b s)"
    by (auto simp: prefix_adom_def)
  
  lemma prefix_adom_insert[simp]:
    "prefix_adom a (insert d e) = insert (a@d) (prefix_adom a e)"
    "prefix_adom1 i (insert d e) = insert (i#d) (prefix_adom1 i e)"
    by (auto simp: prefix_adom_def prefix_adom1_def)
        
  lemma prefix_adom_union[simp]:
    "prefix_adom a (d\<union>e) = prefix_adom a d \<union> prefix_adom a e"
    "prefix_adom1 i (d\<union>e) = prefix_adom1 i d \<union> prefix_adom1 i e"
    by (auto simp: prefix_adom_def prefix_adom1_def)
  
    
    
  lemma s_indep_Cons[simp]: "s_indep (prefix_adom1 a s\<^sub>1) (prefix_adom1 b s\<^sub>2) \<longleftrightarrow> a\<noteq>b \<or> s_indep s\<^sub>1 s\<^sub>2"
    by (auto simp: s_indep_def prefix_adom1_def)
    
  lemma s_indep_prefix[simp]: "s_indep (prefix_adom a s\<^sub>1) (prefix_adom a s\<^sub>2) \<longleftrightarrow> s_indep s\<^sub>1 s\<^sub>2"
    by (auto simp: s_indep_def prefix_adom_def)
        
    
    
  lemma s_indep_union[simp]:  
    "s_indep (a\<union>b) c \<longleftrightarrow> s_indep a c \<and> s_indep b c"
    "s_indep a (b\<union>c) \<longleftrightarrow> s_indep a b \<and> s_indep a c"
    by (auto simp: s_indep_def)
    
      
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
      
  definition "prefix_map1 i m \<equiv> \<lambda>[] \<Rightarrow> None | i'#as \<Rightarrow> if i=i' then m as else None"
  definition "prefix_map xs m = foldr prefix_map1 xs m"

  lemma prefix_map1_empty[simp]: 
    "prefix_map1 i Map.empty = Map.empty"
    "prefix_map1 i m = Map.empty \<longleftrightarrow> m=Map.empty"
    by (auto simp: prefix_map1_def fun_eq_iff split: if_splits list.splits)
    
  lemma prefix_map_simps[simp]:
    "prefix_map [] m = m"
    "prefix_map (i#as) m = prefix_map1 i (prefix_map as m) "
    by (auto simp: prefix_map_def)

  lemma prefix_map_empty[simp]: 
    "prefix_map as Map.empty = Map.empty" 
    by (induction as) auto
      
  lemma prefix_map_empty_iff[simp]: 
    "prefix_map as m = Map.empty \<longleftrightarrow> m = Map.empty"
    by (induction as) auto

  lemma prefix_map1_dom[simp]: "dom (prefix_map1 i m) = prefix_adom1 i (dom m)"  
    by (auto simp: prefix_map1_def split: list.splits if_splits)
      
  lemma prefix_map_dom[simp]: "dom (prefix_map as m) = prefix_adom as (dom m)"  
    by (induction as) auto
    
    
  lift_definition prefix_aval1 :: "va_item \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is prefix_map1
    by auto auto

  lift_definition prefix_aval :: "vaddr \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is prefix_map
    by auto auto
      
  lift_definition prim_aval :: "'a \<Rightarrow> 'a aval" is "\<lambda>x. [[] \<mapsto> x]" by simp
  lift_definition adom :: "'a aval \<Rightarrow> vaddr set" is "dom" .

  lemma prefix_aval_simps[simp]:
    "prefix_aval1 i 0 = 0"
    "prefix_aval1 i v = 0 \<longleftrightarrow> v=0"
    "prefix_aval [] v = v"
    "prefix_aval a 0 = 0"
    "prefix_aval a v = 0 \<longleftrightarrow> v = 0"
    "prefix_aval (i#a) v = prefix_aval1 i (prefix_aval a v)"
    
    "adom (prefix_aval1 i v) = prefix_adom1 i (adom v)"
    "adom (prefix_aval a v) = prefix_adom a (adom v)"
    apply (determ \<open>transfer\<close>; auto; fail)+
    done
      
  
  lemma adomZ[simp]: "adom 0 = {}"
    apply transfer by auto
  
  lemma disj_eq_adom: "a##b \<longleftrightarrow> s_indep (adom a) (adom b)"
    apply transfer by (auto simp: s_indep_def)
  
  lemma adom_plus[simp]: "a##b \<Longrightarrow> adom (a+b) = adom a \<union> adom b"
    apply transfer by auto
  
  lemma adom_primval[simp]: "adom (prim_aval x) = {[]}"
    apply transfer by auto
    
    
    
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
    
    
  lemma lens_of_vaddr_append[simp]: "lens_of_vaddr (va\<^sub>1@va\<^sub>2) = lens_of_vaddr va\<^sub>1 \<bullet>\<^sub>L lens_of_vaddr va\<^sub>2"  
    by (induction va\<^sub>1) auto
  
  lemma vaddr_indep_suffixI: "vaddr_indep va va' \<Longrightarrow> vaddr_indep (va@sfx) (va'@sfx')"
  proof (induction va arbitrary: va')
    case Nil
    then show ?case by auto
  next
    case (Cons a va)
    then show ?case by (cases va') (auto simp: )
  qed
  
  lemma s_indep_suffixI: "vaddr_indep va va' \<Longrightarrow> s_indep (prefix_adom va s\<^sub>1) (prefix_adom va' s\<^sub>2)"
    by (auto simp: s_indep_def vaddr_indep_suffixI)

  lemma disj_suffixI: "vaddr_indep a b \<Longrightarrow> prefix_aval a v\<^sub>1 ## prefix_aval b v\<^sub>2"  
    by (determ transfer) (auto simp: s_indep_suffixI)
    
  lemma val_dom_ne[simp]: "val_dom x \<noteq> {}" 
    by (induction x) auto
    
  lemma val_dom_not_indep1: "s_indep (val_dom x) s \<longleftrightarrow> s={}"
  proof -
    {
      have "s\<noteq>{} \<Longrightarrow> \<not>s_indep (val_dom x) s"
      proof (induction x arbitrary: s)
        case (PAIR x1 x2)
        
        then obtain va s' where [simp]: "s = insert va s'" by auto
        
        {
          assume "va = []"
          hence ?case using val_dom_ne by (fastforce simp: s_indep_def simp del: val_dom_ne)
        } moreover {
          fix va'
          assume "va = PFST#va'"
          hence ?case apply (auto simp: s_indep_def Bex_def)
          by (metis (mono_tags, hide_lams) PAIR.IH(1) empty_iff insert_iff s_indep_def vaddr_indep_Cons)
        } moreover {
          fix va'
          assume "va = PSND#va'"
          hence ?case apply (auto simp: s_indep_def Bex_def)
          by (metis (mono_tags, hide_lams) PAIR.IH(2) empty_iff insert_iff s_indep_def vaddr_indep_Cons)
        } ultimately show ?case
          by (metis (full_types) neq_Nil_conv va_item.exhaust)
      next
        case (PRIMITIVE x)
        then show ?case by auto
      qed
    }
    then show ?thesis by auto
  qed    
    
  lemma val_dom_not_indep2: "s_indep s (val_dom x) \<longleftrightarrow> s={}"
    using s_indep_sym val_dom_not_indep1 by blast

  lemmas val_dom_not_indep[simp] = val_dom_not_indep1 val_dom_not_indep2
    
  lemma indep_prefix_val_dom_iff[simp]: 
    "s_indep (prefix_adom va (val_dom x)) (prefix_adom va' (val_dom y)) \<longleftrightarrow> vaddr_indep va va'"    
  proof -
    have "s_indep (prefix_adom va (val_dom x)) (prefix_adom va' (val_dom y)) \<Longrightarrow> vaddr_indep va va'"    
    proof (induction va arbitrary: va')
      case Nil
      then show ?case by auto
    next
      case (Cons a va)
      then show ?case by (cases va') auto
    qed
    thus ?thesis by (auto simp: s_indep_suffixI)
  qed
    
  lemma indep_val_\<alpha>_iff: "prefix_aval va (val_\<alpha> x) ## prefix_aval va' (val_\<alpha> y) \<longleftrightarrow> vaddr_indep va va'"
    by (auto simp: disj_eq_adom s_indep_suffixI)
    
    
  definition "project_map1 i m \<equiv> \<lambda>a. m (i#a)"  
  
  lemma project_map1_empty[simp]: "project_map1 i Map.empty = Map.empty"
    by (auto simp: project_map1_def)
  
  definition "carve_map1 i m \<equiv> \<lambda>[] \<Rightarrow> m [] | i'#a \<Rightarrow> if i=i' then None else m (i'#a)"  
    
  lift_definition project_aval1 :: "va_item \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is project_map1
    apply (auto simp: project_map1_def)
    by (meson domI list.inject vaddr_indep_Cons)

  lift_definition carve_aval1 :: "va_item \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is carve_map1
    by (fastforce simp: carve_map1_def split: list.splits if_splits)
      
  lemma project_aval1_simps[simp]: "project_aval1 i 0 = 0"
    apply (determ transfer; auto)
    done
        
  lemma prefix_aval_add_distrib: "a\<^sub>1 ## a\<^sub>2 \<Longrightarrow> prefix_aval1 i (a\<^sub>1 + a\<^sub>2) = prefix_aval1 i a\<^sub>1 + prefix_aval1 i a\<^sub>2"  
    apply (determ \<open>transfer\<close>; auto)
    apply (rule ext)
    by (auto simp: prefix_map1_def s_indep_def map_add_def split: list.splits option.splits)
    
  (* TODO: Move *)  
  lemma dom_project_map1_iff[simp]: "dom (project_map1 i b) = { a. i#a \<in> dom b}"  
    by (auto simp: project_map1_def)
    
  lemma adom_project_aval1[simp]: "adom (project_aval1 i v) = {a. i#a \<in> adom v}"  
    by (determ transfer) auto
    
  (* TODO: Move *)  
  lemma s_indep_projectI: "s_indep s\<^sub>1 s\<^sub>2 \<Longrightarrow> s_indep {a. i # a \<in> s\<^sub>1} {a. i # a \<in> s\<^sub>2}"
    apply (auto simp: s_indep_def)
    using vaddr_indep_Cons by blast
    
  lemma project_aval_add_distrib: "b\<^sub>1 ## b\<^sub>2 \<Longrightarrow> project_aval1 i (b\<^sub>1 + b\<^sub>2) = project_aval1 i b\<^sub>1 + project_aval1 i b\<^sub>2"  
    apply (determ \<open>transfer\<close>; auto intro: s_indep_projectI)
    apply (rule ext)
    apply (auto simp: project_map1_def map_add_def)
    done
    
  lemma carve_aval1Z[simp]: "carve_aval1 i 0 = 0"  
    apply transfer
    apply (rule ext)
    apply (auto simp: carve_map1_def split: list.splits)
    done
    
  lemma carve_map1_dom[simp]: "dom (carve_map1 i v) = dom v - {i # as |as. True}"  
    by (auto simp: carve_map1_def split: list.splits if_splits)

  lemma carve_aval1_dom: "adom (carve_aval1 i v) = adom v - {i#as | as. True}"
    apply transfer by auto
        
  lemma carve_aval1_add_distrib: "b\<^sub>1 ## b\<^sub>2 \<Longrightarrow> carve_aval1 i (b\<^sub>1 + b\<^sub>2) = carve_aval1 i b\<^sub>1 + carve_aval1 i b\<^sub>2"  
    apply transfer
    apply (rule ext)
    apply (auto split: if_split)
    subgoal by (auto simp: s_indep_def carve_map1_def map_add_def split: list.split)
    subgoal by (auto simp: s_indep_def)
    done
  
  lemma project_prefix_id: "project_aval1 i (prefix_aval1 i a) = a"  
    apply transfer
    apply (rule ext)
    apply (auto simp: project_map1_def prefix_map1_def)
    done

  lemma project_prefix_diff: "i\<noteq>j \<Longrightarrow> project_aval1 i (prefix_aval1 j a) = 0"  
    apply transfer
    apply (rule ext)
    apply (auto simp: project_map1_def prefix_map1_def)
    done
    
      
  lemma project_carveZ: "project_aval1 i (carve_aval1 i b) = 0"  
    apply transfer
    apply (rule ext)
    apply (auto simp: project_map1_def carve_map1_def)
    done
  
  lemma carve_prefixZ: "carve_aval1 i (prefix_aval1 i a) = 0"
    apply transfer
    apply (rule ext)
    apply (auto simp: prefix_map1_def carve_map1_def split: list.splits)
    done
    
  lemma carve_prefix_diff: "i\<noteq>j \<Longrightarrow> carve_aval1 i (prefix_aval1 j a) = prefix_aval1 j a"
    apply transfer
    apply (rule ext)
    apply (auto simp: prefix_map1_def carve_map1_def split: list.splits)
    done
    
    
  lemma project_primitive[simp]: "project_aval1 i (prim_aval v) = 0"  
    apply transfer
    apply (rule ext)
    apply (auto simp: project_map1_def)
    done
  
  lemma carve_primitive[simp]: "carve_aval1 i (prim_aval v) = prim_aval v"  
    apply transfer
    apply (rule ext)
    apply (auto simp: carve_map1_def split: list.split)
    done
    
  lemma adom_cases: obtains (primitive) "adom a = {[]}" | (compound) "[]\<notin>adom a"
    by transfer force    
    
  lemma prefix_adom1_no_primv[simp]: "prefix_adom1 i s \<noteq> {[]}"  
    by (simp add: prefix_adom1_def) auto
    
  definition "val_item_lifter i \<equiv> \<lparr>
    sep_lifter.lift = prefix_aval1 i,
    sep_lifter.project = project_aval1 i,
    sep_lifter.carve = carve_aval1 i,
    sep_lifter.splittable = \<lambda>a. [] \<notin> adom a,
    sep_lifter.L = lens_of_item i,
    sep_lifter.\<alpha>b = val_\<alpha>,
    sep_lifter.\<alpha>s = val_\<alpha>
  \<rparr>"
    
  lemma null_not_indep[simp]:
    "[]\<in>s \<Longrightarrow> s_indep s s' \<longleftrightarrow> s'={}"
    "[]\<in>s \<Longrightarrow> s_indep s' s \<longleftrightarrow> s'={}"
    by (force simp: s_indep_def)+
  
  lemma adom_empty_imp_project_empty[simp]: "adom b\<^sub>1 = {} \<Longrightarrow> project_aval1 i b\<^sub>1 = 0"
    apply transfer apply auto done
  
  lemma prefix_aval1_disj_distrib[simp]: "prefix_aval1 i a\<^sub>1 ## prefix_aval1 i a\<^sub>2 = a\<^sub>1 ## a\<^sub>2"
    by (auto simp: disj_eq_adom) []
    
  lemma project_aval_disj_distrib[simp]: "b\<^sub>1 ##  b\<^sub>2 \<Longrightarrow> project_aval1 i b\<^sub>1 ## project_aval1 i b\<^sub>2"  
    by (auto simp: disj_eq_adom s_indep_projectI) []

  lemma carve_aval_disj_distrib[simp]: "b\<^sub>1 ##  b\<^sub>2 \<Longrightarrow> carve_aval1 i b\<^sub>1 ## carve_aval1 i b\<^sub>2"  
    by (auto simp: disj_eq_adom carve_aval1_dom s_indep_def) []
    
  lemma aval1_disj_project_imp_lift: "\<lbrakk>[] \<notin> adom b; a ## project_aval1 i b\<rbrakk> \<Longrightarrow> prefix_aval1 i a ## b  "
    apply (auto simp: disj_eq_adom) []
    apply (cases b rule: adom_cases)
    apply simp
    apply (auto simp: s_indep_def )
    by (metis (full_types) list.exhaust vaddr_indep_Cons)
    
  lemma "[] \<notin> adom b \<Longrightarrow> carve_aval1 i b ## prefix_aval1 i a"
    xxx: ctd here. Skipped to move stuff on lift,project,carve to own locale,
      and use this
    
        
  lemma val_item_lifter[simp, intro!]: "sep_lifter (val_item_lifter i)"
    apply unfold_locales
    apply (clarsimp_all simp: val_item_lifter_def)
    apply (auto simp: prefix_aval_add_distrib) []
    apply (auto simp: disj_eq_adom) []
    apply (auto simp: project_aval_add_distrib) []
    apply (auto simp: carve_aval1_add_distrib) []
    apply (auto simp: project_prefix_id) []
    apply (auto simp: project_carveZ) []
    apply (auto simp: carve_prefixZ) []
    apply (auto simp: aval1_disj_project_imp_lift) []
    
    subgoal for b a  
      apply (auto simp: disj_eq_adom carve_aval1_dom prefix_adom1_def s_indep_def) []
      by (metis neq_Nil_conv vaddr_indep_Cons)
      
    subgoal  
      apply transfer
      apply (rule ext)
      apply (auto simp: map_add_def carve_map1_def prefix_map1_def project_map1_def split: list.splits option.splits)
      apply (auto simp: s_indep_def split: list.splits option.splits if_splits)      
      done
      
    subgoal  
      apply transfer
      apply (rule ext)
      apply (auto simp: carve_map1_def split: list.splits) 
      by (metis domI domIff list.distinct(1) vaddr_indep_simps(1))
    
    subgoal for cb by (cases cb; cases i) auto
    subgoal for cb 
      apply (cases cb; cases i)
      apply (auto simp: project_aval_add_distrib project_prefix_id project_prefix_diff)
      done          
    subgoal for cb x
      apply (cases cb; cases i)
      apply (auto simp: carve_aval1_add_distrib project_prefix_id project_prefix_diff carve_prefixZ carve_prefix_diff sep_algebra_simps)
      done          
    done      

    
    
  definition "vaddr_lifter addr = foldr (\<lambda>i l. l \<bullet>\<^sub>l\<^sub>f\<^sub>t val_item_lifter i) addr (id_lifter val_\<alpha>)"  
    
  lemma vaddr_lifter_simps:
    "vaddr_lifter [] = id_lifter val_\<alpha>"
    "vaddr_lifter (i#a) = vaddr_lifter a \<bullet>\<^sub>l\<^sub>f\<^sub>t val_item_lifter i"
    unfolding vaddr_lifter_def by auto
    
  
  (* TODO: Move! *)
  lemma [simp]: "sep_lifter.\<alpha>s (val_item_lifter a) = val_\<alpha>" by (auto simp: val_item_lifter_def)
  lemma [simp]: "sep_lifter.\<alpha>b (val_item_lifter a) = val_\<alpha>" by (auto simp: val_item_lifter_def)
  
  (* TODO: Move! *)
  lemma [simp]: "sep_lifter.\<alpha>s (id_lifter \<alpha>) = \<alpha>" by (auto simp: id_lifter_def)
  lemma [simp]: "sep_lifter.\<alpha>b (id_lifter \<alpha>) = \<alpha>" by (auto simp: id_lifter_def)
  lemma [simp]: "sep_lifter.\<alpha>s (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.\<alpha>s l\<^sub>1" by (auto simp: compose_lifter_def)
  lemma [simp]: "sep_lifter.\<alpha>b (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.\<alpha>b l\<^sub>2" by (auto simp: compose_lifter_def)
  
  lemma [simp]: "sep_lifter.\<alpha>s (vaddr_lifter addr) = val_\<alpha>"
    apply (induction addr) apply (auto simp: vaddr_lifter_simps) done

  lemma [simp]: "sep_lifter.\<alpha>b (vaddr_lifter addr) = val_\<alpha>"
    apply (induction addr) apply (auto simp: vaddr_lifter_simps) done
  
  lemma vaddr_lifter[simp, intro!]: "sep_lifter (vaddr_lifter addr)"
    apply (induction addr) apply (auto simp: vaddr_lifter_simps) done

  lemma vaddr_lifter_L[simp]: "sep_lifter.L (vaddr_lifter addr) = lens_of_vaddr addr"  
    apply (induction addr)
    apply (auto simp: vaddr_lifter_simps id_lifter_def compose_lifter_def val_item_lifter_def)
    done
    
  interpretation val_item_lifter: sep_lifter "val_item_lifter i" for i by simp  
    
  interpretation vaddr_lifter: sep_lifter "vaddr_lifter addr" for addr by simp
    

  lemma vaddr_lift_Nil[simp]: "vaddr_lifter.lift [] = id"
    by (auto simp: vaddr_lifter_def id_lifter_def)
    
  lemma vaddr_lift_Cons[simp]: "vaddr_lifter.lift (i#as) = prefix_aval1 i o vaddr_lifter.lift as"  
    apply (rule ext)
    apply (auto simp: vaddr_lifter_simps)
    apply (auto simp: compose_lifter_def)
    apply (auto simp: val_item_lifter_def)
    done
    
  lemma vaddr_lift_append[simp]: "vaddr_lifter.lift (as\<^sub>1@as\<^sub>2) = vaddr_lifter.lift as\<^sub>1 o vaddr_lifter.lift as\<^sub>2"  
    by (induction as\<^sub>1) auto
    
  definition "vpto_assn v addr \<equiv> vaddr_lifter.lift_assn addr (EXACT (val_\<alpha> v))"
  
  lemma vaddr_lift_assn_Nil[simp]: "vaddr_lifter.lift_assn [] P = P"
    apply (rule ext)
    apply (auto simp: vaddr_lifter.lift_assn_def)
    apply (auto simp: vaddr_lifter_def id_lifter_def)
    done
  
  lemma vaddr_lift_assn_Cons[simp]: "vaddr_lifter.lift_assn (i#as) P = val_item_lifter.lift_assn i (vaddr_lifter.lift_assn as P)"
    apply (rule ext)
    apply (simp add: vaddr_lifter_simps lift_assn_compose)
    done
    
  lemma vaddr_lift_assn_append[simp]: "vaddr_lifter.lift_assn (as\<^sub>1@as\<^sub>2) P = vaddr_lifter.lift_assn as\<^sub>1 (vaddr_lifter.lift_assn as\<^sub>2 P)"  
    by (induction as\<^sub>1) auto
    
  lemma pto_split: "vpto_assn (PAIR a b) addr = (vpto_assn a (addr@[PFST]) ** vpto_assn b (addr@[PSND]))" 
    by (auto simp: vpto_assn_def EXACT_split)
  
  
  definition "vload err a \<equiv> zoom (lift_lens err (lens_of_vaddr a)) get"  
  definition "vstore err a x \<equiv> zoom (lift_lens err (lens_of_vaddr a)) (set x)"
  
  
  lemma "val_\<alpha> v ## x \<longleftrightarrow> x=0"
    apply (induction v arbitrary: x)
    apply clarsimp []
    find_theorems prefix_aval1 "(##)"
    
    
  
  lemma "(EXACT (val_\<alpha> v) \<and>* F) (val_\<alpha> v') \<longleftrightarrow> v'=v \<and> (\<exists>\<Phi>. F=\<up>\<Phi>)"
    apply (auto simp: sep_conj_def)
  
  lemma "htriple val_\<alpha> (EXACT (val_\<alpha> v)) Monad.get (\<lambda>r. \<up>(r=v) ** EXACT (val_\<alpha> v))"
    apply (rule htripleI)
    apply simp
  
    
  (* TODO: Move *)
  lemma val_\<alpha>_nZ[simp]: "val_\<alpha> v \<noteq> 0"
    by (metis adomZ adom_val_\<alpha> val_dom_ne)
  
  lemma "htriple val_\<alpha> (vpto_assn v a) (vload err a) (\<lambda>r. \<up>(r=v) ** vpto_assn v a)"  
    unfolding vload_def vpto_assn_def
    apply (rule cons_post_rule)
    apply (rule vaddr_lifter.lift_operation[simplified])
    apply simp
    
    
oops    
  xxx: prove hoare-triples for basic load/store!  
    
    
  term "vaddr_lifter.lift_assn addr (EXACT (val_\<alpha> v))"
    This is points-to assertion!
  
  How to split it?  
    
    
  
  thm sep_lifter.lift_operation[OF vaddr_lifter]  
    
    
oops    
  xxx: Show that lens of addr_lifter is addr lens. We may have to reverse composition direction!  
    
      
oops    
  xxx, derive lifter for address, by composing val_item_lifter

  
    
oops    

  find_theorems "(\<bowtie>)" "(\<bullet>\<^sub>L)"

oops

  xxx, ctd here:  
    address independence via lens independence.
    then separation algebra and val_\<alpha>, 
    lifters for fst, snd, and []
    try to derive lifter for any pointer from that, by induction!
  
        
      
    
oops    
    
  xxx: How to terminate lifter nesting? 
    wrap lifter into typedef, and define operations on lifters:
    
    
    element access
    composition
    

end
