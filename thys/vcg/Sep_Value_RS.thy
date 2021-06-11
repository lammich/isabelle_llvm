section \<open>Reasoning about Values\<close>
theory Sep_Value_RS
imports Sep_Lift "../basic/LLVM_Basic_Main"
begin


  locale path_sep_defs =
    fixes sep :: "'p \<Rightarrow> 'p \<Rightarrow> bool"
      and pCons :: "'i \<Rightarrow> 'p \<Rightarrow> 'p"
      and val_\<alpha> :: "'v \<Rightarrow> 'p set"
      and elem\<^sub>L :: "'i \<Rightarrow> 'v \<Longrightarrow> 'v"
  begin
  
    definition "valid S \<equiv> \<forall>x\<in>S. \<forall>y\<in>S. x\<noteq>y \<longrightarrow> sep x y"
    definition "seps A B \<equiv> \<forall>x\<in>A. \<forall>y\<in>B. sep x y"
    definition "path\<^sub>L vp = foldr (\<lambda>i L. elem\<^sub>L i \<bullet>\<^sub>L L) vp id\<^sub>L"
    
    (*definition pto' :: "'i list \<Rightarrow> 'p set \<Rightarrow> 'p set" 
      where "pto' p x = foldr (\<lambda>i x. pCons i`x) p x"
    *)
    
    definition pConss where "pConss is p = foldr pCons is p"  
      
    definition pto where "pto p x \<equiv> pConss p ` x"
    
    lemma valid_empty[simp]: "valid {}" by (auto simp: valid_def)
    lemma valid_sng[simp]: "valid {x}" by (auto simp: valid_def)
    
    lemma seps_simps[simp]: 
      "seps {} a"
      "seps a {}"
      by (auto simp: seps_def)
        
    lemma seps_Un[simp]: 
      "seps a (b\<union>c) \<longleftrightarrow> seps a b \<and> seps a c"  
      "seps (a\<union>b) c \<longleftrightarrow> seps a c \<and> seps b c"  
      by (auto simp: seps_def)
    
    lemma pConss_simps[simp]: 
      "pConss [] p = p"  
      "pConss (i#is) p = pCons i (pConss is p)"  
      unfolding pConss_def by auto

    lemma pto_this[simp]: "pto [] P = P"  
      by (auto simp: pto_def)
      
  end

  locale path_sep_stage1 = path_sep_defs sep pCons val_\<alpha> elem\<^sub>L 
    for sep :: "'p \<Rightarrow> 'p \<Rightarrow> bool"
    and pCons :: "'i \<Rightarrow> 'p \<Rightarrow> 'p"
    and val_\<alpha> :: "'v \<Rightarrow> 'p set"
    and elem\<^sub>L :: "'i \<Rightarrow> 'v \<Longrightarrow> 'v" +
    assumes pCons_inj[simp]: "pCons i x = pCons i' x' \<longleftrightarrow> i=i' \<and> x=x'"
    assumes sep_irrefl[simp, intro!]: "\<not>sep x x"
        and sep_sym[sym]: "sep x y \<Longrightarrow> sep y x"
        and sep_pCons[iff]: "sep (pCons i x) (pCons i' y) \<longleftrightarrow> i\<noteq>i' \<or> sep x y"
        and sep_locality: "(\<nexists>i y'. y=pCons i y') \<Longrightarrow> sep (pCons i x) y \<Longrightarrow> sep (pCons i x') y"
    assumes val_\<alpha>_valid[simp,intro!]: "valid (val_\<alpha> v)"
        and val_\<alpha>_complete: "\<exists>x\<in>val_\<alpha> v. \<not>sep x y"
        and val_\<alpha>_inj: "val_\<alpha> v = val_\<alpha> v' \<Longrightarrow> v=v'"
  begin
  
    lemma path_cases: 
      obtains (pCons) i y' where "y=pCons i y'" 
            | (noCons) "\<nexists>i y'. y=pCons i y'" 
      by blast
  
    lemma seps_irrefl[simp]: 
      "seps a a \<longleftrightarrow> a={}"
      by (meson not_empty_eq sep_irrefl seps_def)
  
    lemma valid_Un[simp]: "valid a \<Longrightarrow> valid b \<Longrightarrow> seps a b \<Longrightarrow> valid (a\<union>b)"
      apply (auto simp: seps_def valid_def)
      by (meson sep_sym)
      
    
    lemma unique_zero_lemmas:  
      "seps x {}"
      "seps x y \<Longrightarrow> seps y x"
      "x \<union> {} = x"
      "seps x y \<Longrightarrow> x \<union> y = y \<union> x"
      "\<lbrakk>seps x y; seps y z; seps x z\<rbrakk> \<Longrightarrow> x \<union> y \<union> z = x \<union> (y \<union> z)"
      "seps y z \<Longrightarrow> seps x (y \<union> z) = (seps x y \<and> seps x z)"
      "seps x x \<Longrightarrow> x = {}"
      apply (auto simp: seps_def dest: sep_sym)
      done
      
    lemma "class.unique_zero_sep_algebra (\<union>) {} seps"  
      apply unfold_locales
      apply (auto simp: unique_zero_lemmas)
      done
      
    lemma val_\<alpha>_complete'[simp]: 
      "seps (val_\<alpha> v) x \<Longrightarrow> x={}"  
      "seps x (val_\<alpha> v) \<Longrightarrow> x={}"  
      by (meson seps_def seps_irrefl unique_zero_lemmas(2) val_\<alpha>_complete)+

    lemma val_\<alpha>_non_empty[simp]: "val_\<alpha> v \<noteq> {}"  
      using val_\<alpha>_complete by auto
            
    lemma val_\<alpha>_inj'[simp]: "val_\<alpha> vi \<subseteq> val_\<alpha> v \<Longrightarrow> vi = v"  
      by (metis subset_antisym subset_iff val_\<alpha>_complete val_\<alpha>_inj val_\<alpha>_valid valid_def)

    lemma val_\<alpha>_nseps[simp]: "\<not>seps (val_\<alpha> a) (val_\<alpha> b)"  
      apply (auto simp: seps_def)
      by (meson val_\<alpha>_complete)
      
    lemma path\<^sub>L_simps[simp]: 
      "path\<^sub>L [] = id\<^sub>L"
      "path\<^sub>L (i#is) = elem\<^sub>L i \<bullet>\<^sub>L path\<^sub>L is"
      unfolding path\<^sub>L_def by auto

    (*lemma pto'_simps[simp]: 
      "pto' [] v = v"
      "pto' (i#is) v = pCons i ` pto' is v"
      unfolding pto'_def by auto
    *)

    lemma valid_pCons[iff]: "valid (pCons i`ps) \<longleftrightarrow> valid ps"
      unfolding valid_def
      by auto
          
    lemma valid_pConss[simp, intro]: "valid (pConss is ` ps) \<longleftrightarrow> valid ps"  
      apply (induction "is" arbitrary: ps) 
      apply simp
      apply (simp flip: image_image)
      done

    lemma seps_pCons[iff]: "seps (pCons i`ps) (pCons i'`ps') \<longleftrightarrow> i\<noteq>i' \<or> seps ps ps'"  
      by (auto simp: seps_def)
                  
    lemma seps_pConss[iff]: "seps (pConss is`ps) (pConss is`ps') \<longleftrightarrow> seps ps ps'"  
      apply (induction "is" arbitrary: ps) 
      apply simp
      apply (simp flip: image_image)
      done

    lemma pto_empty[simp]: "pto p {} = {}"  
      unfolding pto_def
      by auto
      
    lemma pto_empty_iff[simp]: "pto p x = {} \<longleftrightarrow> x={}"  
      unfolding pto_def
      by auto
      
    lemma pto_add_distrib[simp]: 
      "pto p (a\<union>b) = pto p a \<union> pto p b"  
      "seps (pto p a) (pto p b) \<longleftrightarrow> seps a b"
      unfolding pto_def
      by auto

    lemma pto_valid[simp]: "valid (pto p a) = valid a"  
      unfolding pto_def
      by auto
            
    lemma val_pto_not_same[simp]: "\<not>seps (pto p (val_\<alpha> a)) (pto p (val_\<alpha> b))"  
      apply (induction p)
      apply (auto)
      done
      
      
    (*  
    lemma pto'_nonempty[simp]: "pto' p x = {} \<longleftrightarrow> x={}"
      apply (induction p)
      apply (auto)
      done
      
    lemma pto'_empty[simp]: "pto' p {} = {}" by simp 
    *)
      
      
  end
   

  locale path_sep = path_sep_stage1 sep pCons val_\<alpha> elem\<^sub>L 
    for sep :: "'p \<Rightarrow> 'p \<Rightarrow> bool"
    and pCons :: "'i \<Rightarrow> 'p \<Rightarrow> 'p"
    and val_\<alpha> :: "'v \<Rightarrow> 'p set"
    and elem\<^sub>L :: "'i \<Rightarrow> 'v \<Longrightarrow> 'v" +
    assumes elem\<^sub>L_lens[simp,intro!]: "lens (elem\<^sub>L i)"
        (*and elem\<^sub>L_get: "pCons i ` val_\<alpha> vi \<subseteq> val_\<alpha> v \<Longrightarrow> get (elem\<^sub>L i) v = Some vi"*)
        and elem\<^sub>L_get: "pCons i p \<in> val_\<alpha> v \<Longrightarrow> \<exists>vi. get (elem\<^sub>L i) v = Some vi \<and> p\<in>val_\<alpha> vi \<and> pCons i ` val_\<alpha> vi \<subseteq> val_\<alpha> v"
        and elem\<^sub>L_put: "pCons i ` val_\<alpha> vi \<subseteq> val_\<alpha> v \<Longrightarrow> \<exists>v'. put (elem\<^sub>L i) vi' v = Some v' \<and> val_\<alpha> v' = val_\<alpha> v - pCons i ` val_\<alpha> vi \<union> pCons i ` val_\<alpha> vi'"
  begin
    lemma path\<^sub>L_lens[simp, intro!]: "lens (path\<^sub>L p)"  
      apply (induction p)
      apply (auto)
      done

    lemma path\<^sub>L_get: "\<lbrakk>pConss p x \<in> val_\<alpha> v\<rbrakk> \<Longrightarrow> \<exists>vi. get (path\<^sub>L p) v = Some vi \<and> x \<in> val_\<alpha> vi"
      apply (induction p arbitrary: x v)
      apply (auto dest: elem\<^sub>L_get)
      done

    lemma path\<^sub>L_get_val: "pto p (val_\<alpha> vp) \<subseteq> val_\<alpha> v \<Longrightarrow> get (path\<^sub>L p) v = Some vp"  
      unfolding pto_def
      by (smt (z3) image_subset_iff option.inject path\<^sub>L_get subset_iff val_\<alpha>_complete val_\<alpha>_inj')

    lemma path\<^sub>L_get_val': "val_\<alpha> v = pto p (val_\<alpha> vp) \<union> F  \<Longrightarrow> pre_get (path\<^sub>L p) v \<and> get' (path\<^sub>L p) v  = vp"  
      by (metis Un_upper1 lens.simp_rls(5) path\<^sub>L_get_val path_sep.path\<^sub>L_lens path_sep_axioms)
            
    lemma path\<^sub>L_put_val: "pto p (val_\<alpha> vp) \<subseteq> val_\<alpha> v \<Longrightarrow> 
      \<exists>v'. put (path\<^sub>L p) vp' v = Some v' \<and> val_\<alpha> v' = val_\<alpha> v - pto p (val_\<alpha> vp) \<union> pto p (val_\<alpha> vp')"
    proof (induction p arbitrary: v)
      case Nil
      then show ?case 
        apply (auto simp: pto_def)
        using val_\<alpha>_inj' by blast
    next
      case (Cons i p)
      
      from Cons.prems obtain vi where 
        "get (elem\<^sub>L i) v = Some vi" 
        and ISS: "pCons i ` val_\<alpha> vi \<subseteq> val_\<alpha> v"
        and SSI: "pto p (val_\<alpha> vp) \<subseteq> val_\<alpha> vi"
        apply (auto simp: pto_def)
        by (smt (z3) elem\<^sub>L_get elem\<^sub>L_lens image_subset_iff lens.simp_rls(5) val_\<alpha>_complete)
      hence [simp]: "pre_get (elem\<^sub>L i) v" "get' (elem\<^sub>L i) v = vi" by auto
      
      from Cons.IH[OF SSI] obtain vi' where
        "put (path\<^sub>L p) vp' vi = Some vi'" and
        [simp]: "val_\<alpha> vi' = val_\<alpha> vi - pto p (val_\<alpha> vp) \<union> pto p (val_\<alpha> vp')"
        by auto
        
      hence [simp]: "pre_put (path\<^sub>L p) vi" "put' (path\<^sub>L p) vp' vi = vi'" by auto 
        
      from elem\<^sub>L_put[OF ISS, of vi'] obtain v' where 
        "put (elem\<^sub>L i) vi' v = Some v'" and [simp]: "val_\<alpha> v' = val_\<alpha> v - pCons i ` val_\<alpha> vi \<union> pCons i ` val_\<alpha> vi'"
        by auto
      hence [simp]: "pre_put (elem\<^sub>L i) v" "put' (elem\<^sub>L i) vi' v = v'" by auto
      
      
      show ?case
        apply (simp add: pto_def)
        apply auto
        subgoal using ISS by blast
        subgoal 
          by (metis \<open>get (elem\<^sub>L i) v = Some vi\<close> elem\<^sub>L_get image_eqI option.sel)
        done
        
    qed
      
    lemma val_\<alpha>_seps_complete: "seps (val_\<alpha> x) F \<Longrightarrow> seps (val_\<alpha> y) F"
      apply (auto simp: seps_def)
      using val_\<alpha>_complete by blast
    
      
    definition "proj_Cons i F \<equiv> {p . pCons i p \<in> F}"
    definition "proj_nCons i F \<equiv> { p\<in>F. \<nexists>p'. p=pCons i p' }"
      
    lemma split_F_pCons: "F = pCons i ` proj_Cons i F \<union> proj_nCons i F"
      by (auto simp: proj_Cons_def proj_nCons_def)
      
    lemma seps_proj_nCons_change: 
      "\<lbrakk>seps (pCons i`ps) (proj_nCons i F); ps\<noteq>{} \<rbrakk>
        \<Longrightarrow> seps (pCons i`ps') (proj_nCons i F)"
      apply (auto simp: seps_def proj_Cons_def proj_nCons_def)
      by (metis sep_locality sep_pCons)

      
    lemma seps_pto_val: "seps (pto p (val_\<alpha> vp)) F \<Longrightarrow> seps (pto p (val_\<alpha> vp')) F"
    proof (induction p arbitrary: F)
      case Nil
      then show ?case by (auto simp: pto_def val_\<alpha>_seps_complete)
    next
      case (Cons i p)
      
      from Cons.prems show ?case
        apply (subst split_F_pCons[of F i])
        apply (subst (asm) split_F_pCons[of F i])
        apply (auto elim: seps_proj_nCons_change simp: pto_def simp flip: image_image)
        by (metis Cons.IH pto_def)
      
    qed
      
    lemma seps_irrefl_disj: "seps A B \<Longrightarrow> A\<inter>B = {}"
      by (force simp: seps_def)
    
    
    lemma path\<^sub>L_put_val': 
      assumes A: "val_\<alpha> v = pto p (val_\<alpha> vp) \<union> F" and S: "seps (pto p (val_\<alpha> vp)) F"
      shows "pre_put (path\<^sub>L p) v" (is ?G1)
        and "seps (pto p (val_\<alpha> vp')) F" (is ?G2)
        and "val_\<alpha> (put' (path\<^sub>L p) vp' v) = pto p (val_\<alpha> vp') \<union> F" (is ?G3)
    proof -
    
      have "pto p (val_\<alpha> vp) \<inter> F = {}" using seps_irrefl_disj[OF S] by auto
      with path\<^sub>L_put_val[of p vp v] show ?G1 ?G3
        apply (simp_all add: A)
        by auto
        
      show ?G2 using S seps_pto_val by blast  
    qed    
        
    
    
      
    
    
    
  end  
  
  datatype 'a epath = 
    EP_LEAF 'a 
  | EP_TY nat
  | EP_IDX nat "'a epath"


  fun ep_sep :: "'a epath \<Rightarrow> 'a epath \<Rightarrow> bool"  where
    "ep_sep (EP_LEAF _) _ = False"
  | "ep_sep _ (EP_LEAF _) = False"
  | "ep_sep (EP_IDX i p) (EP_IDX i' p') \<longleftrightarrow> i\<noteq>i' \<or> ep_sep p p'"
  | "ep_sep (EP_IDX i p) (EP_TY n) \<longleftrightarrow> i<n"
  | "ep_sep (EP_TY n) (EP_IDX i p) \<longleftrightarrow> i<n"
  | "ep_sep (EP_TY n) (EP_TY n') \<longleftrightarrow> False"
  

  lemma ep_sep_irrefl[simp, intro!]: "\<not>ep_sep a a"
    apply (induction a)
    apply simp_all
    done
  
  lemma ep_sep_sym[sym]: "ep_sep a b \<Longrightarrow> ep_sep b a"  
    apply (induction a b rule: ep_sep.induct)
    apply auto
    done
    
    
  lemma val_\<alpha>_term_aux:"(a, b) \<in> set (List.enumerate 0 fs) \<Longrightarrow> size b < Suc (size_list size fs)"
    by (metis enumerate_eq_zip le_imp_less_Suc less_or_eq_imp_le set_zip_rightD size_list_estimation')
    
  context
    notes [simp] = val_\<alpha>_term_aux
  begin
    fun val_\<alpha>_raw where
      "val_\<alpha>_raw (PRIMITIVE x) = {EP_LEAF x}"
    | "val_\<alpha>_raw (STRUCT fs) = (insert (EP_TY (length fs)) (\<Union>(set (map (\<lambda>(i,fsi). EP_IDX i ` val_\<alpha>_raw (fsi)) (List.enumerate 0 fs)))))"

  end

  lemma val_\<alpha>_alt: 
    "val_\<alpha>_raw (STRUCT fs :: 'a val) = insert (EP_TY (length fs)) (\<Union>{EP_IDX i ` val_\<alpha>_raw (fs!i) | i. i<length fs})"
  proof -
    have aux: "{f (i + aa) ((a # fs) ! i) |i. i < Suc (length fs)} 
      = insert (f aa a) ({f (i + 1 + aa) (fs ! i) |i. i < length fs})" for f aa a fs
      apply auto
      subgoal using less_Suc_eq_0_disj by auto
      subgoal by force
      subgoal by force
      done
    
    have aux2: "\<Union>{ f (i+a) (fs!i) | i. i<length fs } =
      \<Union>(set (map (\<lambda>(i,fsi). f i fsi) (List.enumerate a fs)))" for f a
      apply (induction fs arbitrary: a)
      apply simp
      apply (simp add: aux) 
      by (smt (verit, best) Collect_cong add_Suc_right)
      
    note A = aux2[of "\<lambda>i fsi. (EP_IDX i ` val_\<alpha>_raw fsi) :: 'a epath set" 0, simplified]  
    then show ?thesis
      by simp
      
  qed      
      
  lemmas [simp del] = val_\<alpha>_raw.simps(2)
  lemmas [simp] = val_\<alpha>_alt
  
  definition "lens_of_item' \<equiv> lens_of_item o PFLD"
  
  interpretation VAL_PATH_SEP: path_sep_defs ep_sep EP_IDX val_\<alpha>_raw lens_of_item' .
  
  lemma valid_val_\<alpha>_aux: "VAL_PATH_SEP.valid (val_\<alpha>_raw s)"
    apply (induction s)
    apply clarsimp_all
    by (force simp: VAL_PATH_SEP.valid_def in_set_conv_nth)
  
  lemma val_\<alpha>_induct[case_names PRIMITIVE STRUCT]: "\<lbrakk>
    \<And>x. P (PRIMITIVE x);
    \<And>fs. (\<And>i. i<length fs \<Longrightarrow> P (fs!i)) \<Longrightarrow> P (STRUCT fs)\<rbrakk> \<Longrightarrow> P a0"  
    by (metis nth_mem val.induct)
    
  lemma val_\<alpha>_complete_aux: "\<exists>x\<in>val_\<alpha>_raw s. \<not>ep_sep x y"
  proof (induction s arbitrary: y rule: val_\<alpha>_induct)
    case (STRUCT fs)
    then show ?case 
      apply (auto)
      apply (cases y; fastforce)
      done
    
  next
    case (PRIMITIVE x)
    then show ?case by simp
  qed
  
  lemma val_\<alpha>_inj_aux': "val_\<alpha>_raw v \<subseteq> val_\<alpha>_raw v' \<Longrightarrow> v=v'"
  proof (induction v arbitrary: v' rule: val_\<alpha>_induct)
    case (PRIMITIVE x)
    then show ?case 
      apply (cases v')
      apply auto
      done
    
  next
    case (STRUCT fs)
    then show ?case 
      apply (cases v')
      apply (auto simp: list_eq_iff_nth_eq)
      apply (rprems)
      apply auto
      done
    
  qed
  
  lemma val_\<alpha>_inj_aux: "val_\<alpha>_raw v = val_\<alpha>_raw v' \<Longrightarrow> v=v'"
    using val_\<alpha>_inj_aux' by blast

  lemma lens_of_item'[simp, intro!]: "lens (lens_of_item' i)"
    by (simp add: lens_of_item'_def)
    
  lemma ep_sep_locality_aux: "\<lbrakk>\<nexists>i y'. y = EP_IDX i y'; ep_sep (EP_IDX i x) y\<rbrakk> \<Longrightarrow> ep_sep (EP_IDX i x') y"
    apply (cases y)
    apply auto
    done
      
    
  interpretation VAL_PATH_SEP: path_sep_stage1 ep_sep EP_IDX val_\<alpha>_raw lens_of_item'
    apply (rule path_sep_stage1.intro)
    apply (all \<open>(rule valid_val_\<alpha>_aux val_\<alpha>_complete_aux val_\<alpha>_inj_aux ep_sep_locality_aux ep_sep_sym; blast; fail)?\<close>)
    apply (simp_all add: ep_sep_sym)
    done
    
    
  lemma item_get_aux: "EP_IDX i p \<in> val_\<alpha>_raw v \<Longrightarrow> \<exists>vi. get (lens_of_item' i) v = Some vi \<and> p \<in> val_\<alpha>_raw vi \<and> EP_IDX i ` val_\<alpha>_raw vi \<subseteq> val_\<alpha>_raw v"  
    apply (cases v)
    apply (auto simp: lens_of_item'_def)
    done

  lemma idxm_nle_leaf[simp]: "EP_IDX i ` S \<subseteq> {EP_LEAF x2} \<longleftrightarrow> S={}"
    by (simp add: image_iff subset_insert)
      
  lemma idx_le_ins_ty_conv[simp]: "EP_IDX i ` S \<subseteq> insert (EP_TY n) S' \<longleftrightarrow> EP_IDX i ` S \<subseteq> S'"
    by auto
  
  lemma idxm_le_map_conv[simp]: "S\<noteq>{} \<Longrightarrow> EP_IDX i ` S \<subseteq> (\<Union> {EP_IDX i ` f i |i. P i} ) \<longleftrightarrow> P i \<and> S \<subseteq> f i"  
    by auto
    
  lemma item_set_aux: "EP_IDX i ` val_\<alpha>_raw vi \<subseteq> val_\<alpha>_raw v \<Longrightarrow> \<exists>v'. put (lens_of_item' i) vi' v 
    = Some v' \<and> val_\<alpha>_raw v' = val_\<alpha>_raw v - EP_IDX i ` val_\<alpha>_raw vi \<union> EP_IDX i ` val_\<alpha>_raw vi'"  
    apply (cases v)
    apply (auto simp: lens_of_item'_def nth_list_update')
    apply (metis imageI VAL_PATH_SEP.val_\<alpha>_inj')
    done
      
  interpretation VAL_PATH_SEP: path_sep ep_sep EP_IDX val_\<alpha>_raw lens_of_item'
    apply (rule path_sep.intro)
    apply (unfold_locales) []
    apply (rule path_sep_axioms.intro)
    apply (all \<open>(rule item_get_aux valid_val_\<alpha>_aux item_set_aux)?\<close>)
    apply (simp_all)
    done
  
  typedef 'a aval = "Collect VAL_PATH_SEP.valid :: 'a epath set set" by auto
  setup_lifting type_definition_aval  
    
  instantiation aval :: (type) unique_zero_sep_algebra
  begin
    lift_definition sep_disj_aval :: "'a aval \<Rightarrow> 'a aval \<Rightarrow> bool" is "VAL_PATH_SEP.seps" .
    lift_definition plus_aval :: "'a aval \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is "\<lambda>m1 m2. if VAL_PATH_SEP.seps m1 m2 then m1 \<union> m2 else {}"
      by (auto split: if_splits simp: )
  
    lift_definition zero_aval :: "'a aval" is "{}" by simp
    
    instance
      apply standard
      apply (determ transfer; (auto simp add: VAL_PATH_SEP.unique_zero_lemmas); assumption )+
      done
  end
  
  term VAL_PATH_SEP.pto
  
  lift_definition val_\<alpha> :: "'a val \<Rightarrow> 'a aval" is val_\<alpha>_raw by simp
  lift_definition val_pto :: "vaddr \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is 
    "\<lambda>p x. VAL_PATH_SEP.pto (map the_va_item_idx p) x"
    by (auto)

  lift_definition val_struct :: "nat \<Rightarrow> 'a aval" is "\<lambda>n. {EP_TY n}" by simp
      
  lemma lens_of_vaddr_cnv_pathL: "lens_of_vaddr p = VAL_PATH_SEP.path\<^sub>L (map the_va_item_idx p)"  
    apply (induction p)
    apply simp
    subgoal for i its
      apply (cases i)
      apply simp
      apply (auto simp: lens_of_item'_def comp_def)
      done
    done
    
  lemma val_get_lemma:
    assumes "val_pto p (val_\<alpha> v) ## F"
    assumes "val_\<alpha> s = val_pto p (val_\<alpha> v) + F"  
    shows "get (lens_of_vaddr p) s = Some v"
    using assms
    apply transfer
    apply (simp add: VAL_PATH_SEP.path\<^sub>L_get_val' lens_of_vaddr_cnv_pathL)
    done

  lemma val_put_lemma:
    assumes "val_pto p (val_\<alpha> v) ## F"
    assumes "val_\<alpha> s = val_pto p (val_\<alpha> v) + F"  
    shows "\<exists>s'. 
        put (lens_of_vaddr p) v' s = Some s' 
      \<and> val_pto p (val_\<alpha> v') ## F
      \<and> val_\<alpha> s' = val_pto p (val_\<alpha> v') + F"
    using assms
    apply transfer
    apply (simp add: lens_of_vaddr_cnv_pathL VAL_PATH_SEP.path\<^sub>L_put_val')  
    done
  
  lemma val_\<alpha>_nzero[simp]: "val_\<alpha> x \<noteq> 0"  
    apply transfer
    apply auto
    done

  lemma val_\<alpha>_complete[simp]: "val_\<alpha> x ## y \<longleftrightarrow> y=0"  
    apply transfer
    apply auto
    using VAL_PATH_SEP.val_\<alpha>_complete'(1) by blast
        
  lemma val_pto_zero[simp]: "val_pto p 0 = 0"  
    apply transfer
    apply auto
    done
    
  lemma val_pto_eq_zero[simp]: "val_pto p x = 0 \<longleftrightarrow> x=0"  
    apply transfer
    apply auto
    done
    
  lemma val_pto_add[simp]: "a ## b \<Longrightarrow> val_pto p (a + b) = val_pto p a + val_pto p b"  
    apply transfer
    apply auto
    done
    
  lemma val_pto_disj[simp]: "val_pto p a ## val_pto p b \<longleftrightarrow> a##b"  
    apply transfer
    apply auto
    done
    
  lemma val_pto_this[simp]: "val_pto [] a = a"  
    apply transfer
    apply simp
    done
    
  locale sep_load_store_pre = 
    fixes \<alpha> :: "'v \<Rightarrow> 'a::sep_algebra"
  begin
    definition "val v \<equiv> EXACT (\<alpha> v)"
  end  
  
    
  locale sep_load_store = sep_load_store_pre \<alpha> 
      for \<alpha> :: "'v \<Rightarrow> 'a::stronger_sep_algebra"
  + fixes vpto :: "'p::this_addr \<Rightarrow> 'a \<Rightarrow> 'a::stronger_sep_algebra"
      and L :: "'p \<Rightarrow> 'v \<Longrightarrow> 'v"
    assumes vpto_additive[simp]: "a##b \<Longrightarrow> vpto p (a+b) = vpto p a + vpto p b"  
        and vpto_additive_dj[iff]: "vpto p a ## vpto p b = a##b"
        and vpto_zero[simp]: "vpto p 0 = 0" "vpto p a = 0 \<longleftrightarrow> a = 0"
        and vpto_this[simp]: "vpto this_addr a = a"
        and \<alpha>_notZ[simp]: "\<alpha> x \<noteq> 0"
        and \<alpha>_complete[simp]: "\<alpha> x ## F \<longleftrightarrow> F=0"
    assumes get_lemma: "vpto p (\<alpha> v) ## F \<Longrightarrow> \<alpha> s = vpto p (\<alpha> v) + F \<Longrightarrow> get (L p) s = Some v"
        and put_lemma: "vpto p (\<alpha> v) ## F \<Longrightarrow> \<alpha> s = vpto p (\<alpha> v) + F \<Longrightarrow> \<exists>s'. put (L p) v' s = Some s' \<and> vpto p (\<alpha> v') ## F \<and> \<alpha> s' = vpto p (\<alpha> v') + F"
  begin  
    
    definition "pto p P s \<equiv> \<exists>s'. s = vpto p s' \<and> P s'"
  
    lemma pto_add[simp]: "pto p (a ** b) = (pto p a ** pto p b)"
      by (force simp: sep_conj_def get_lemma pto_def fun_eq_iff)
  
    lemma pto_Z[simp]: 
      "pto p \<box> = \<box>"  
      "pto p P 0 \<longleftrightarrow> P 0"  
      apply (auto simp: pto_def sep_algebra_simps fun_eq_iff)
      done
      
    lemma pto_this[simp]: "pto this_addr P = P"  
      apply (auto simp: pto_def sep_algebra_simps fun_eq_iff)
      done
      
    lemma val_Z[simp]: "\<not>val x 0"  
      unfolding val_def by auto
      
      
    lemma pto_not_same[simp]: "(pto p (val x) ** pto p (val y)) = sep_false"  
      unfolding pto_def val_def
      by (auto simp: fun_eq_iff sep_conj_def)
      
    lemma pto_not_same_aux: "pto p (val x\<^sub>1) s\<^sub>1 \<Longrightarrow> pto p (val x\<^sub>2) s\<^sub>2 \<Longrightarrow> \<not>s\<^sub>1 ## s\<^sub>2"
      unfolding pto_def val_def
      by auto
      
    lemma get_rule:
      "(pto p (val x) ** F) (\<alpha> s) \<Longrightarrow> get (L p) s = Some x"
      apply (auto simp: sep_conj_def get_lemma pto_def val_def)
      done
  
    lemma put_rule:
      "(pto p (val x) ** F) (\<alpha> s) \<Longrightarrow> \<exists>s'. put (L p) x' s = Some s' \<and> (pto p (val x') ** F) (\<alpha> s')"
      apply (auto simp: sep_conj_def pto_def val_def)
      using put_lemma by blast
    
    lemma vpto_sum_list: "sep_distinct xs \<Longrightarrow> vpto p (sepsum_list xs) = sepsum_list (map (vpto p) xs)"  
      apply (induction xs)
      apply auto
      done
      
    lemma vpto_sep_distinct: "sep_distinct (map (vpto p) xs) = sep_distinct xs"  
      apply (induction xs)
      apply (auto simp flip: vpto_sum_list)
      done
      
      
      
  end
  
  interpretation VAL: sep_load_store val_\<alpha> val_pto lens_of_vaddr
    apply unfold_locales
    apply simp
    apply simp
    apply simp
    apply simp
    apply simp
    apply simp
    apply simp
    apply (rule val_get_lemma; simp)
    apply (rule val_put_lemma; simp)
    done
  
  lemma VAL_pto_this[simp]: "VAL.pto [] P = P" (* TODO: Hack. Clean solution would be to not include this_addr_def into simpset! *)
    using VAL.pto_this[simplified] .
    
    
    
    
  (* TODO: Can probably be done generically in locale *)  
  definition "val_fields_raw bi fs \<equiv> \<Union> {EP_IDX (i+bi) ` val_\<alpha>_raw (fs ! i) |i. i < length fs}"
  
  lemma val_fields_raw_valid: "VAL_PATH_SEP.valid (val_fields_raw bi fs)"
    unfolding val_fields_raw_def
    apply (auto simp: VAL_PATH_SEP.valid_def)
    using VAL_PATH_SEP.valid_def by blast
  
  lemma val_fields_raw_Nil[simp]: "val_fields_raw i [] = {}"  
    by (auto simp: val_fields_raw_def)
    
  lemma val_fields_raw_Cons[simp]: "val_fields_raw i (f#fs) = EP_IDX i ` val_\<alpha>_raw f \<union> val_fields_raw (Suc i) fs"
    apply (auto simp: val_fields_raw_def nth_Cons')
    by (metis Suc_pred add_Suc imageI not_less_eq)
    
  lemma val_fields_raw_sep[simp]: "VAL_PATH_SEP.seps (EP_IDX i ` ps) (val_fields_raw (Suc i) fs)"
    by (auto simp: val_fields_raw_def VAL_PATH_SEP.seps_def)
    
    
    
  lift_definition val_fields :: "nat \<Rightarrow> 'a val list \<Rightarrow> 'a aval" is val_fields_raw
    by (auto simp: val_fields_raw_valid)
    
  lemma val_fields_Nil[simp]: "val_fields i [] = 0"  
    apply transfer apply auto done
    
  lemma val_fields_Cons[simp]: "val_fields i (f#fs) = val_pto [PFLD i] (val_\<alpha> f) + val_fields (Suc i) fs"
    apply transfer apply (auto simp: VAL_PATH_SEP.pto_def)
    done

  lemma val_fields_Sep[simp]: "val_pto [PFLD i] (val_\<alpha> f) ## val_fields (Suc i) fs"
    apply transfer apply (auto simp: VAL_PATH_SEP.pto_def)
    done
    
  lemma val_\<alpha>_struct_unfold[simp]: "val_\<alpha> (STRUCT fs) = val_struct (length fs) + val_fields 0 fs"
    apply transfer
    apply (auto simp: val_fields_raw_def)
    apply (auto simp: VAL_PATH_SEP.seps_def)
    done
    
  lemma val_\<alpha>_struct_unfold_sep[simp]: "val_struct (length fs) ## val_fields 0 fs"
    apply transfer
    apply (auto simp: val_fields_raw_def VAL_PATH_SEP.seps_def)
    done

  definition "STRUCT_assn n \<equiv> EXACT (val_struct n)"
  definition "FIELDS_assn i fs \<equiv> EXACT (val_fields i fs)"
    
  lemma FIELDS_assn_simps[simp]:
    "FIELDS_assn i [] = \<box>"
    "FIELDS_assn i (f#fs) = (VAL.pto [PFLD i] (VAL.val f) ** FIELDS_assn (Suc i) fs)"
    unfolding FIELDS_assn_def VAL.pto_def VAL.val_def
    apply (auto simp: sep_algebra_simps EXACT_split)
    apply (subst EXACT_split)
    apply simp
    unfolding EXACT_def
    apply (auto simp: fun_eq_iff)
    done
    
  
  lemma val_split: "VAL.val (STRUCT fs) = (STRUCT_assn (length fs) ** FIELDS_assn 0 fs)"
    unfolding STRUCT_assn_def FIELDS_assn_def
    apply (auto simp add: VAL.val_def fun_eq_iff sep_conj_def)
    done
      
  
  (*
    can we actually wrap properties on assertions in locale?
  
    val :: 'v \<Rightarrow> assn
    pto :: 'p \<Rightarrow> assn \<Rightarrow> assn
    
    get, put rule
    
  *)  
      
  locale sep_load_store_assn = sep_load_store_pre \<alpha> 
    for \<alpha> :: "'v \<Rightarrow> 'a::sep_algebra"
  +
    fixes pto :: "'p \<Rightarrow> ('a\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow> bool)"
      and L :: "'p \<Rightarrow> 'v \<Longrightarrow> 'v"
    assumes pto_add: "pto p (a**b) = (pto p a ** pto p b)"  
        and pto_zero[simp]: "pto p \<box> = \<box>" "pto p P 0 \<longleftrightarrow> P 0"
        and get_rule: "(pto p (val x) ** F) (\<alpha> s) \<Longrightarrow> get (L p) s = Some x"
        and put_rule: "(pto p (val x) ** F) (\<alpha> s) \<Longrightarrow> \<exists>s'. put (L p) x' s = Some s' \<and> (pto p (val x') ** F) (\<alpha> s')"
      
  begin
    find_consts "(_,_,_,_) M" name: lift
  
  
  end      
        
  context sep_load_store begin      
    sublocale LS: sep_load_store_assn \<alpha> pto L
      apply unfold_locales
      apply simp
      apply simp
      apply simp
      using get_rule apply (simp add: val_def)
      using put_rule apply (simp add: val_def) 
      done
      
  end            
  
  term VAL.pto
  
  thm vcg_normalize_simps
  (* TODO: Move *)
  lemma wp_use[vcg_normalize_simps]: "elens L \<Longrightarrow> wp (use L) P s \<longleftrightarrow> (\<exists>x. eget L s = Inr x \<and> P x s)"
    unfolding wp_def
    by (simp add: run_simps split: option.split)
  
  lemma wp_assign[vcg_normalize_simps]: "elens L \<Longrightarrow> wp (L::=x) P s \<longleftrightarrow> (\<exists>s'. eput L x s = Inr s' \<and> P () s')"
    unfolding wp_def
    by (simp add: run_simps split: option.split)
  
  lemma vload_rule: "htriple val_\<alpha> (VAL.pto p (VAL.val x)) (vload err p) (\<lambda>r. \<up>(r=x) ** VAL.pto p (VAL.val x))"
  proof -
    have A: "pre_get (lens_of_vaddr p) s \<and> get' (lens_of_vaddr p) s = x" 
      if "STATE val_\<alpha> (VAL.pto p (VAL.val x) \<and>* F) s" for F s
      using that
      using VAL.LS.get_rule[of p x F s]
      apply (auto simp: STATE_def)
      done

    show ?thesis    
      apply vcg
      apply (frule A)
      unfolding vload_def 
      apply vcg
      done
      
  qed      
    
  lemma vstore_rule: "htriple val_\<alpha> (VAL.pto p (VAL.val x)) (vstore err x' p) (\<lambda>_. VAL.pto p (VAL.val x'))"  
  proof -
    have A: "pre_put (lens_of_vaddr p) s \<and> STATE val_\<alpha> (VAL.pto p (VAL.val x') \<and>* F) (put' (lens_of_vaddr p) x' s)" 
      if "STATE val_\<alpha> (VAL.pto p (VAL.val x) \<and>* F) s" for F s
      using that
      using VAL.LS.put_rule[of p x F s]
      apply (auto simp: STATE_def)
      done
      
    show ?thesis  
      apply vcg
      apply (frule A)
      unfolding vstore_def
      apply vcg           
      done                                                     
      
  qed    
  
  
(*  
  oops  
        
  xxx: ctd here:
    try lifting to block.
    ideally, we can lift a sep_load_store_assn instance, 
      without any knowledge of sub-structure.
  
  
  
  
   
    
  lemma val_pto_con: "val_\<alpha> x = a+b \<Longrightarrow> val_pto p x = val_pto p a + val_pto p b"
    
    
  definition "sepsum_un xs \<equiv> if (distinct xs \<and> )"
    
  lemma "(rel_fun (list_all2 (pcr_aval (=))) (pcr_aval (=))) (\<Union> o set) sepsum_list"
    unfolding sepsum_list_def
    
  
    
  lemma "val_\<alpha> (STRUCT fs) = val_struct (length fs) + (sepsum_list (map (\<lambda>(i,v). val_pto [] v) (List.enumerate 0 fs)))"
    
    apply transfer
    apply simp
    
  lemma "val_\<alpha>_raw (STRUCT fs) = foo"
    apply simp
    
    
      
    
    
  (* Rules *)
  definition "aval_pto p x \<equiv> EXACT (VAL_PATH_SEP.pto p x)"
  
  
  
  
  
  
  
  
  
  definition "ep_seps S \<equiv> \<forall>x\<in>S. \<forall>y\<in>S. x\<noteq>y \<longrightarrow> ep_sep x y"
  
  lemma ep_seps_empty[simp]: "ep_seps {}" by (auto simp: ep_seps_def)
  lemma ep_seps_sng[simp]: "ep_seps {x}" by (auto simp: ep_seps_def)
  
  lemma val_\<alpha>_seps: "ep_seps (val_\<alpha>_raw s)"
    apply (induction s)
    apply clarsimp_all
    by (force simp: ep_seps_def in_set_conv_nth)

  definition "eps_sep A B \<equiv> \<forall>a\<in>A. \<forall>b\<in>B. ep_sep a b"  
      
  
  lemma val_\<alpha>_complete: "\<not>(\<forall>x\<in>val_\<alpha>_raw s. ep_sep x y)"
  proof (induction s arbitrary: y rule: val_\<alpha>_induct)
    case (STRUCT fs)
    then show ?case 
      apply (auto)
      apply (cases y; fastforce)
      done
    
  next
    case (PRIMITIVE x)
    then show ?case by simp
  qed
  
  lemma "\<forall>x. \<exists>y\<in>val_\<alpha>_raw s. \<not>ep_sep x y"
    by (meson ep_sep_sym val_\<alpha>_complete)
  
          
  (*lemma val_\<alpha>_complete: "\<forall>x\<in>val_\<alpha> s. ep_sep x y \<Longrightarrow> y\<in>val_\<alpha> s"
  proof (induction s arbitrary: y rule: val_\<alpha>_induct)
    case (STRUCT fs)
    then show ?case 
      apply (auto)
      apply (cases y; fastforce)
      done
    
  next
    case (PRIMITIVE x)
    then show ?case by simp
  qed
  *)

  
  lemma eps_sep_empty[simp]: 
    "eps_sep {} a"
    "eps_sep a {}"
    by (auto simp: eps_sep_def)

  lemma eps_sep_irrefl[simp]:
    "eps_sep a a \<longleftrightarrow> a={}"  
    apply (auto simp: eps_sep_def)
    using ep_sep_irrefl by blast

  lemma eps_sep_sym[sym]: "eps_sep a b \<Longrightarrow> eps_sep b a" 
    by (auto simp: eps_sep_def ep_sep_sym)
      
  lemma eps_sep_val_left[simp]: "eps_sep (val_\<alpha>_raw x) F \<longleftrightarrow> F={}"
    apply (auto simp: eps_sep_def)
    using ep_sep_irrefl val_\<alpha>_complete by blast

  lemma eps_sep_val_right[simp]: "eps_sep F (val_\<alpha>_raw x) \<longleftrightarrow> F={}"
    by (meson empty_iff ep_sep_irrefl ep_sep_sym eps_sep_def set_notEmptyE val_\<alpha>_complete)

    
      
    
  typ "_ ptr"
  
  typ vaddr
  
  fun va_pto where
    "va_pto [] v = val_\<alpha>_raw v"
  | "va_pto (PFLD i#ptr) v = EP_IDX i ` va_pto ptr v"  
  

  
  lemma val_\<alpha>_inj: "val_\<alpha>_raw v \<subseteq> val_\<alpha>_raw v' \<Longrightarrow> v=v'"
  proof (induction v arbitrary: v' rule: val_\<alpha>_induct)
    case (PRIMITIVE x)
    then show ?case 
      apply (cases v')
      apply auto
      done
    
  next
    case (STRUCT fs)
    then show ?case 
      apply (cases v')
      apply (auto simp: list_eq_iff_nth_eq)
      apply (rprems)
      apply auto
      done
    
  qed
    
  lemma val_\<alpha>_nempty[simp, intro!]: "val_\<alpha>_raw v \<noteq> {}"
    by (induction v) auto
    
  lemma va_pto_nempty[simp, intro!]: "va_pto p x \<noteq> {}"  
    apply (induction p x rule: va_pto.induct) apply auto done
    
    
  lemma idxm_nle_leaf[simp]: "\<not>EP_IDX i ` va_pto ptr x \<subseteq> {EP_LEAF x2}"
    by (simp add: image_iff subset_insert)
    
  lemma idx_le_ins_ty_conv[simp]: "EP_IDX i ` S \<subseteq> insert (EP_TY n) S' \<longleftrightarrow> EP_IDX i ` S \<subseteq> S'"
    by auto
  
  lemma idxm_le_map_conv[simp]: "S\<noteq>{} \<Longrightarrow> EP_IDX i ` S \<subseteq> (\<Union> {EP_IDX i ` f i |i. P i} ) \<longleftrightarrow> P i \<and> S \<subseteq> f i"  
    by auto
    
  
  lemma va_pto_get: "va_pto p x \<subseteq> val_\<alpha>_raw v \<Longrightarrow> get (lens_of_vaddr p) v = Some x"
  proof (induction p x arbitrary: v rule: va_pto.induct)
    case (1 v)
    then show ?case by (auto simp: val_\<alpha>_inj)
  next
    case (2 i ptr x)
    
    from "2.prems" obtain fs where [simp]: "v=STRUCT fs" "i < length fs"
      by (cases v; auto)
      
    from 2 show ?case by (auto)  
  qed  
    
  lemma
    assumes "eps_sep (va_pto p x) F"
    assumes "va_pto p x \<union> F \<subseteq> val_\<alpha>_raw v"
    obtains v' where "put (lens_of_vaddr p) x' v = Some v'" "va_pto p x' \<union> F \<subseteq> val_\<alpha>_raw v'"
  proof -  
    from assms have "\<exists>v'. put (lens_of_vaddr p) x' v = Some v' \<and> va_pto p x' \<union> F \<subseteq> val_\<alpha>_raw v'"
    proof (induction p x arbitrary: v x' F rule: va_pto.induct)
      case (1 x v')
      then show ?case by (auto)
      
    next
      case (2 i ptr v)
      
      from "2.prems" obtain fs where [simp]: "v=STRUCT fs" "i < length fs"
        by (cases v; auto)
      
      from "2.IH"
        
      show ?case 
        apply (cases v)
        apply auto
      
      
      
    qed
    
    
  
  
  
  oops
  xxx, ctd here: pto-put:
    we need separation!
  
  
  
  
    then show ?case 
      
      
      oops
      subgoal
        by (metis epath.distinct(4) imageE image_is_empty singletonI subset_singletonD va_pto_nempty)
      
    
  qed
    apply (auto simp: val_\<alpha>_inj)
  
    
  oops
  xxx: relation with pointer:
    pto
    
    
    
  
  
  typ "'a \<Longrightarrow> 'b"

oops
  xxx: Reasoning infrastructure needs to change:

    goal: build separation algebra for value structure,
          and allow lifting
    
    sep-algebra:
      set of paths, including type-info for each prefix          
          
    we want:
      load/store rule:
        \<alpha> s = pto p (val x) + F \<Longrightarrow> load p s = x
        \<alpha> s = pto p (val x) + F \<Longrightarrow> store p x' s = s' \<and> \<alpha> s' = pto p (val x') + F
        
      split/join rule
        val (x) = struct (struct_of x) + pto 0 (val x\<^sub>0) + ... + pto n (val x\<^sub>n)
      
  xxx: instantiate this directly for sep-value, no locales this time!
    have two types of paths: value paths and structure paths
    sep-algebra: set of paths!
    \<alpha> generates both, values and structure
    
      
  
    
          
        
            
            

    sep-algebra input?
      value type: 'v
      address type: 'a
      address lens: "'a \<Rightarrow> 'v \<Longrightarrow> 'v"  (defines valid addresses in value)
        (we'll most likely need: compatible values that do not change valid addresses)  
    
                  
  
  







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
    
  (*  
  lemma "prefix_map1 (PFLD i) a ++ x = prefix_map1 (PFLD i) a' ++ x'
    \<longleftrightarrow> a=a' \<and> x=x'"
    
  oops  
    a pply (auto simp: fun_eq_iff map_add_def prefix_map1_def split: option.split list.split)
    
    
  lemma prefix_map_complete_eq_iff[simp]:
    "prefix_map1 PFST a ++ prefix_map1 PSND b = prefix_map1 PFST a' ++ prefix_map1 PSND b'
    \<longleftrightarrow> a=a' \<and> b=b'"
    apply (auto simp: fun_eq_iff map_add_def prefix_map1_def split: option.split list.split)
    by (metis option.exhaust va_item.distinct(1))
  *)
    
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
    apply (simp_all add: lens_indep_sym lens_indep_left_comp)
    done
    
  lemma lens_of_item_indepD: "lens_of_item i \<bowtie> lens_of_item i' \<Longrightarrow> i\<noteq>i'"
    apply (cases i; cases i')
    apply (simp_all add: lens_indep_sym)
    by (metis lens_of_item.simps lens_of_item_rnl rnl_indep_not_refl)
  
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
  
  datatype 'a vp_path = LEAF 'a | FIELD nat nat "'a vp_path"
  
  fun vp_indep where
    "vp_indep (FIELD n i p) (FIELD n' i' p') \<longleftrightarrow> n=n' \<and> (i\<noteq>i' \<or> vp_indep p p')"
  | "vp_indep _ _ \<longleftrightarrow> False"
          
  definition "vps_indep s1 s2 \<equiv> \<forall>x\<in>s1. \<forall>y\<in>s2. vp_indep x y"
  
  lemma vp_indep_sym[sym]: "vp_indep a b \<Longrightarrow> vp_indep b a"
    apply (induction a b rule: vp_indep.induct) by auto
  
  lemma vp_indep_irrefl[simp]: "\<not>vp_indep a a"
  proof -
    have "vp_indep a b \<Longrightarrow> a\<noteq>b" for b
      by (induction a b rule: vp_indep.induct) auto
    thus ?thesis by blast
  qed  
    
  lemma vps_indep_sym[sym]: "vps_indep a b \<Longrightarrow> vps_indep b a"
    unfolding vps_indep_def using vp_indep_sym by auto
  
  lemma vps_indep_empty_simps[simp]:
    "vps_indep a a \<longleftrightarrow> a={}"  
    "vps_indep {} a"
    "vps_indep a {}"
    unfolding vps_indep_def
    apply auto
    by fastforce
  
  typedef 'a aval = "{ m :: 'a vp_path set. \<forall>va\<in>m. \<forall>va'\<in>m. va\<noteq>va' \<longrightarrow> vp_indep va va' }" by auto
  
  setup_lifting type_definition_aval  
    
  instantiation aval :: (type) unique_zero_sep_algebra
  begin
    lift_definition sep_disj_aval :: "'a aval \<Rightarrow> 'a aval \<Rightarrow> bool" is "vps_indep" .
    lift_definition plus_aval :: "'a aval \<Rightarrow> 'a aval \<Rightarrow> 'a aval" is "\<lambda>m1 m2. if vps_indep m1 m2 then m1 \<union> m2 else {}"
      apply (auto split: if_splits simp: vps_indep_def)
      by (meson vp_indep_sym)
  
    lift_definition zero_aval :: "'a aval" is "{}" by simp
      
    instance
      apply standard
      apply (determ transfer; auto simp: vps_indep_def)
      apply (determ transfer; auto simp: vps_indep_def dom_def; metis vp_indep_sym)
      apply (determ transfer; auto simp: vps_indep_def)
      apply (determ transfer; auto simp: simp: map_add_comm vps_indep_sym)
      apply (determ transfer; clarsimp; meson UnE sup_assoc vps_indep_def)
      apply (determ transfer; unfold vps_indep_def; auto simp: domI)
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
    
  (*lemma va_item_complete:
    "i\<noteq>PFST \<Longrightarrow> i=PSND"
    "i\<noteq>PSND \<Longrightarrow> i=PFST"
    "PFST\<noteq>i \<Longrightarrow> i=PSND"
    "PSND\<noteq>i \<Longrightarrow> i=PFST"
    by (all \<open>cases i; auto\<close>)
  *)

  (* TODO: Move *)    
  lemma transfer_enumerate[transfer_rule]: "rel_fun (=) (rel_fun (list_all2 A) (list_all2 (rel_prod (=) A))) List.enumerate List.enumerate"
    unfolding enumerate_eq_zip
    by transfer_prover
  
  lemma aval_cases:
    obtains (primitive) x where "v = prim_aval x" 
          | (compound) vs where "v = fold (+) (map (\<lambda>(i,v). prefix_aval1 (PFLD i) v) (List.enumerate 0 vs)) 0"
  proof -
    have "(\<exists>x. v = prim_aval x) \<or> (\<exists>vs. v = fold (+) (map (\<lambda>(i,v). prefix_aval1 (PFLD i) v) (List.enumerate 0 vs)) 0)"
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
          apply (meso n domI list.inject vaddr_indep_Cons)+
          done  
            
      qed
    qed
    thus ?thesis using that by bla st
  qed
  
  
  
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
          apply (mes on domI list.inject vaddr_indep_Cons)+
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
  
    

*)  

  lifting_forget aval.lifting
  
end
