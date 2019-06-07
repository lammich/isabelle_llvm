theory Sep_Lift
imports Sep_Generic_Wp "HOL-Library.Rewrite"
begin
    
  locale sep_lifting_scheme = 
    fixes lift :: "'asmall::unique_zero_sep_algebra \<Rightarrow> 'abig::unique_zero_sep_algebra"  
      and project :: "'abig \<Rightarrow> 'asmall"
      and carve :: "'abig \<Rightarrow> 'abig"
      and splittable :: "'abig \<Rightarrow> bool"
    assumes lift_pres_zero[simp]: "lift 0 = 0" 
        and lift_add_distrib[simp]: "a\<^sub>1##a\<^sub>2 \<Longrightarrow> lift (a\<^sub>1+a\<^sub>2) = lift a\<^sub>1 + lift a\<^sub>2"
        and lift_disj_distrib[simp]: "lift a\<^sub>1 ## lift a\<^sub>2 \<longleftrightarrow> a\<^sub>1##a\<^sub>2"
        
    assumes splittable_lift[simp]: "splittable (lift a)"    
        and splittable_same_struct: "\<lbrakk>b\<^sub>1##b\<^sub>2; splittable b\<^sub>1; project b\<^sub>1\<noteq>0\<rbrakk> \<Longrightarrow> splittable b\<^sub>2"
        (*and splittable_same_struct: "\<lbrakk>b\<^sub>1##b\<^sub>2; b\<^sub>1\<noteq>0; b\<^sub>2\<noteq>0\<rbrakk> \<Longrightarrow> splittable b\<^sub>2 = splittable b\<^sub>1"*)
        and splittable_add_distrib[simp]: "\<lbrakk>b\<^sub>1##b\<^sub>2\<rbrakk> \<Longrightarrow> splittable (b\<^sub>1 + b\<^sub>2) \<longleftrightarrow> splittable b\<^sub>1 \<and> splittable b\<^sub>2"
        
    assumes project_pres_zero[simp]: "project 0 = 0"
    assumes project_add_distrib[simp]: 
          "\<lbrakk>b\<^sub>1##b\<^sub>2; splittable b\<^sub>1; splittable b\<^sub>2\<rbrakk> \<Longrightarrow> project (b\<^sub>1 + b\<^sub>2) = project b\<^sub>1 + project b\<^sub>2"
        and project_disj_distrib[simp]: "\<lbrakk>b\<^sub>1##b\<^sub>2; splittable b\<^sub>1; splittable b\<^sub>2\<rbrakk> \<Longrightarrow> project b\<^sub>1 ## project b\<^sub>2"     
    assumes carve_pres_zero[simp]: "carve 0 = 0"
    assumes carve_add_distrib[simp]: "\<lbrakk>b\<^sub>1##b\<^sub>2; splittable b\<^sub>1; splittable b\<^sub>2\<rbrakk> \<Longrightarrow> carve (b\<^sub>1 + b\<^sub>2) = carve b\<^sub>1 + carve b\<^sub>2"
        and carve_disj_distrib[simp]: "\<lbrakk>b\<^sub>1##b\<^sub>2; splittable b\<^sub>1; splittable b\<^sub>2\<rbrakk> \<Longrightarrow> carve b\<^sub>1 ## carve b\<^sub>2"
        
    assumes project_lift_id[simp]: "project (lift a) = a"
    assumes project_carve_Z[simp]: "splittable b \<Longrightarrow> project (carve b) = 0"
    assumes carve_lift_Z[simp]: "carve (lift a) = 0"
    
    assumes disj_project_imp_lift: "splittable b \<Longrightarrow> a ## project b \<Longrightarrow> lift a ## b"
    assumes carve_disj_lift1: "splittable b \<Longrightarrow> carve b ## lift a"
                
    assumes complete_split: "splittable b \<Longrightarrow> lift (project b) + carve b = b"
    
    assumes carve_not_splittable[simp]: "\<not> splittable b \<Longrightarrow> carve b = b"
      \<comment> \<open>We force carve to be identity outside splittable range. 
        This is an arbitrary fixation of an otherwise unspecified value, which makes 
        some properties simpler to prove (e.g. assoc of composition)
        \<close>
  begin
    lemma splittableZ[simp]: "splittable 0"
      by (metis lift_pres_zero splittable_lift)
        
    lemma splittable_carve_if[simp]: " splittable p \<Longrightarrow> splittable (carve p)"
      by (metis carve_disj_lift1 complete_split sep_add_commute splittable_add_distrib) 
  
    lemma carve_disj_lift[simp]: 
      assumes "splittable b"
      shows "carve b ## lift a" "lift a ## carve b" 
      using carve_disj_lift1 carve_disj_lift1[THEN sep_disj_commuteI] assms by auto
  
    lemma lift_eqZ_iffZ[simp]: "lift a = 0 \<longleftrightarrow> a=0"
      by (metis lift_pres_zero project_lift_id)
    
    lemma carve_smaller1: "splittable p \<Longrightarrow> p ## f \<Longrightarrow> carve p ## f"  
      by (metis carve_disj_lift(2) sep_add_disjD complete_split)

    lemmas carve_smaller[simp] = carve_smaller1 carve_smaller1[THEN sep_disj_commuteI]
      
    lemma disj_project_eq_lift1: 
      "splittable b \<Longrightarrow> a ## project b \<longleftrightarrow> lift a ## b"
      using disj_project_imp_lift project_disj_distrib by fastforce
      
    lemma disj_project_eq_lift2: 
      "splittable b \<Longrightarrow> project b ## a \<longleftrightarrow> b ## lift a"
      by (meson disj_project_eq_lift1 sep_disj_commuteI)

    lemmas disj_project_eq_lift = disj_project_eq_lift1 disj_project_eq_lift2  
        
    (*  
    lemma proj_Z_imp_disj1:
      assumes "project b = 0"
      shows "lift a ## b"
      by (simp add: assms disj_project_imp_lift)
      
    lemmas proj_Z_imp_disj[simp] = proj_Z_imp_disj1 proj_Z_imp_disj1[THEN sep_disj_commuteI]  
    *)
      
    lemmas split_complete = complete_split[symmetric]

    
    lemma projectZ_add_distrib[simp]: 
      "\<lbrakk>b\<^sub>1##b\<^sub>2; splittable b\<^sub>1; splittable b\<^sub>2\<rbrakk> \<Longrightarrow> project (b\<^sub>1 + b\<^sub>2) = 0 \<longleftrightarrow> project b\<^sub>1=0 \<and> project b\<^sub>2=0"  
      by (auto simp: )
      
    lemma project_add_invE:
      assumes "project b = a\<^sub>1 + a\<^sub>2" "splittable b" "a\<^sub>1##a\<^sub>2" 
      obtains b\<^sub>1 b\<^sub>2 where "b\<^sub>1##b\<^sub>2" "b=b\<^sub>1+b\<^sub>2" "project b\<^sub>1 = a\<^sub>1" "project b\<^sub>2 = a\<^sub>2" "splittable b\<^sub>1" "splittable b\<^sub>2"
      using assms
      by (smt lift_add_distrib lift_disj_distrib project_add_distrib project_carve_Z project_lift_id sep_add_assoc sep_lifting_scheme.carve_disj_lift(2) sep_lifting_scheme.disj_project_eq_lift1 sep_lifting_scheme_axioms split_complete splittable_add_distrib)
  
    lemma carve_project_Z_imp_Z: "\<lbrakk>carve x = 0; project x = 0\<rbrakk> \<Longrightarrow> x = 0"  
      by (metis carve_not_splittable carve_pres_zero complete_split project_pres_zero splittableZ)
      
      
  end        
    
    
  record ('asmall,'csmall,'tsmall,'abig,'cbig,'tbig) sep_lifter =
    lift :: "'asmall::unique_zero_sep_algebra \<Rightarrow> 'abig::unique_zero_sep_algebra"  
    project :: "'abig \<Rightarrow> 'asmall"
    carve :: "'abig \<Rightarrow> 'abig"
    splittable :: "'abig \<Rightarrow> bool"
    
    L :: "'csmall \<Longrightarrow> 'cbig"
    \<alpha>b :: "'cbig \<Rightarrow> 'abig"
    \<alpha>s :: "'csmall \<Rightarrow> 'asmall"
    
    tyb :: "'cbig \<Rightarrow> 'tbig"
    tys :: "'csmall \<Rightarrow> 'tsmall"
    
  hide_const (open) lift project carve splittable L \<alpha>b \<alpha>s tyb tys

  locale pre_sep_lifter = 
    fixes LFT :: "('asmall::unique_zero_sep_algebra,'csmall,'tsmall,'abig::unique_zero_sep_algebra,'cbig,'tbig) sep_lifter"
  begin
    abbreviation lift where "lift \<equiv> sep_lifter.lift LFT"
    abbreviation project where "project \<equiv> sep_lifter.project LFT"
    abbreviation carve where "carve \<equiv> sep_lifter.carve LFT"
    abbreviation splittable where "splittable \<equiv> sep_lifter.splittable LFT"
    abbreviation L where "L \<equiv> sep_lifter.L LFT"
    abbreviation \<alpha>b where "\<alpha>b \<equiv> sep_lifter.\<alpha>b LFT"
    abbreviation \<alpha>s where "\<alpha>s \<equiv> sep_lifter.\<alpha>s LFT"
    abbreviation tyb where "tyb \<equiv> sep_lifter.tyb LFT"
    abbreviation tys where "tys \<equiv> sep_lifter.tys LFT"
    
    
    definition "lift_assn P b \<equiv> splittable b \<and> carve b = 0 \<and> (P (project b))"

    
  end  
  
      
  locale sep_lifter = pre_sep_lifter LFT + sep_lifting_scheme lift project carve splittable
    for LFT :: "('asmall::unique_zero_sep_algebra,'csmall,'tsmall,'abig::unique_zero_sep_algebra,'cbig,'tbig) sep_lifter" +
    
    assumes lensL[simp, intro!]: "hlens L"  
    assumes precond: "\<lbrakk>splittable (\<alpha>b cb); project (\<alpha>b cb)\<noteq>0\<rbrakk> \<Longrightarrow> pre_get L cb \<and> pre_put L cb"
    assumes get_xfer[simp]: "\<lbrakk>splittable (\<alpha>b cb); project (\<alpha>b cb)\<noteq>0\<rbrakk> \<Longrightarrow> \<alpha>s (get' L cb) = project (\<alpha>b cb)"
    assumes put_xfer[simp]: "\<lbrakk>splittable (\<alpha>b cb); project (\<alpha>b cb)\<noteq>0; tys x = tys (get' L cb)\<rbrakk> 
      \<Longrightarrow> \<alpha>b (put' L x cb) = lift (\<alpha>s x) + carve (\<alpha>b cb)"

    assumes ty_put_xfer[simp]: "\<lbrakk>pre_get L cb; tys x = tys (get' L cb) \<rbrakk> \<Longrightarrow> tyb (put' L x cb) = tyb cb"
      
  begin
  
    declare sep_lifter_axioms[simp, intro!]
  

    lemma lift_assn_distrib[simp]: "lift_assn (P**Q) = (lift_assn P ** lift_assn Q)"
      apply (rule ext)
      apply (auto simp: sep_conj_def lift_assn_def)
      apply (erule project_add_invE; auto)
      apply force
      done
      
    lemma lift_assn_EXACT_eq[simp]: "lift_assn (EXACT v) = EXACT (lift v)"
      apply (rule ext)
      apply (auto simp: lift_assn_def)
      using split_complete by fastforce

    lemma lift_assn_pure[simp]: "lift_assn (\<up>\<Phi>) = \<up>\<Phi>"
      apply (rule ext)
      unfolding lift_assn_def
      by (auto simp: pred_lift_extract_simps intro: carve_project_Z_imp_Z)

    lemma lift_assn_empty[simp]: "lift_assn \<box> = \<box>"  
      apply (rule ext)
      unfolding lift_assn_def
      by (auto simp: sep_algebra_simps intro: carve_project_Z_imp_Z)
            
    lemma lift_ty:   
      assumes PRESTY: "\<And>s. wlp c (\<lambda>_ s'. tys s' = tys s) s"
      shows "wlp (zoom (lift_lens e L) c) (\<lambda>_ s'. tyb s' = tyb s) s"
      using PRESTY
      apply (auto simp: wlp_def run_simps split: option.splits)
      apply (drule meta_spec[where x="get' L s"])
      apply (erule mwp_cons)
      apply (auto)
      done
      
      
    lemma infer_pre_get_with_frame:
      assumes "lift_assn P p" "p ## f"  "\<alpha>b s = p + f"
      assumes NZ: "\<not>P 0"
      shows "pre_get L s"
      apply (rule precond[THEN conjunct1])
      using assms splittable_same_struct unfolding lift_assn_def 
      by fastforce+
      
    lemma lift_operation:
      assumes NZ: "\<not>P 0"
      assumes PRESTY: "\<And>s. wlp c (\<lambda>_ s'. tys s' = tys s) s"
      assumes HT: "htriple \<alpha>s P c Q"
      shows "htriple \<alpha>b (lift_assn P) (zoom (lift_lens e L) c) (\<lambda>r. lift_assn (Q r))"
    proof (rule htripleI'; clarsimp simp: lift_assn_def)
      fix p s f
      assume A: "p ## f" and [simp]: "\<alpha>b s = p + f" "splittable p" "carve p = 0" and "P (project p)"
      hence [simp]: "project p\<noteq>0" "p\<noteq>0" "p##f" "f##p" using NZ by (auto simp: sep_algebra_simps)
      
      have [simp]: "splittable f"
        using A \<open>project p \<noteq> 0\<close> \<open>splittable p\<close> splittable_same_struct by blast
      
      from A have OFR: "\<alpha>b s = lift (project (p + f)) + carve (p+f)"
        apply (rewrite in "_ = \<hole>" complete_split) 
        by simp_all
        

      have [simp]: "project (\<alpha>b s) \<noteq> 0" using A by simp 
        
      note HT'= htripleD'[OF HT _ _ \<open>P (project p)\<close>, where f="project f" and s="get' L s", simplified]
      
      from PRESTY HT' have HT': 
        "wp c (\<lambda>r s'. tys s' = tys (get' L s) \<and> (\<exists>p'. p' ## project f \<and> \<alpha>s s' = p' + project f \<and> Q r p')) (get' L s)"
        apply (auto simp: wlp_def wp_def mwp_def split: mres.splits) 
        apply (drule meta_spec[where x="get' L s"]; simp) (* FIXME: Why can't we solve that goal in one line? *)
        done
      
      note HT' = HT'[unfolded wp_def]

      (*from precond have [simp]: "pre_get L s" "pre_put L s" by auto*)
      note [simp] = precond
      
      show "wp (zoom (lift_lens e L) c) (\<lambda>r s'. \<exists>p'. p' ## f \<and> \<alpha>b s' = p' + f \<and> splittable p' \<and> carve p' = 0 \<and> Q r (project p')) s"
        apply (auto simp: wp_def run_simps split: option.splits)
        apply (rule mwp_cons[OF HT'])
        apply (clarsimp_all simp: )
        subgoal for x s' p'
          apply (intro exI[where x="lift p' + carve p"])
          apply (auto simp: disj_project_eq_lift sep_algebra_simps)
          apply (rewrite in "_=\<hole>" split_complete[of f])
          apply (auto simp: disj_project_eq_lift sep_algebra_simps)
          done
        done    
    qed
    
  end


  definition "list\<alpha> \<alpha> l i \<equiv> if i<length l then \<alpha> (l!i) else (0::_::unique_zero_sep_algebra)"  
  
  lemma list\<alpha>_Nil[simp]: "list\<alpha> \<alpha> [] = 0"
    by (auto simp: list\<alpha>_def)
  
  
  lemma list\<alpha>_upd[simp]: 
    "i<length xs \<Longrightarrow> list\<alpha> \<alpha> (xs[i := x]) = (list\<alpha> \<alpha> xs)(i:=\<alpha> x)"
    by (rule ext) (auto simp: list\<alpha>_def)

  definition "idx_lifter tys \<alpha>s i \<equiv> \<lparr> 
    sep_lifter.lift = fun_upd (\<lambda>x. 0) i,
    sep_lifter.project = (\<lambda>f. f i),
    sep_lifter.carve = (\<lambda>f. f(i:=0)),
    sep_lifter.splittable = (\<lambda>f. True),
    sep_lifter.L = idx\<^sub>L i,
    sep_lifter.\<alpha>b = list\<alpha> \<alpha>s,
    sep_lifter.\<alpha>s = \<alpha>s,
    sep_lifter.tyb = map tys,
    sep_lifter.tys = tys
        \<rparr>"

  lemma idx_lifter_simps[simp]:      
    "sep_lifter.lift (idx_lifter tys \<alpha>s i) = fun_upd (\<lambda>x. 0) i"
    "sep_lifter.project (idx_lifter tys \<alpha>s i) = (\<lambda>f. f i)"
    "sep_lifter.carve (idx_lifter tys \<alpha>s i) = (\<lambda>f. f(i:=0))"
    "sep_lifter.splittable (idx_lifter tys \<alpha>s i) = (\<lambda>f. True)"
    "sep_lifter.L (idx_lifter tys \<alpha>s i) = idx\<^sub>L i"
    "sep_lifter.\<alpha>b (idx_lifter tys \<alpha>s i) = list\<alpha> \<alpha>s"
    "sep_lifter.\<alpha>s (idx_lifter tys \<alpha>s i) = \<alpha>s"
    "sep_lifter.tyb (idx_lifter tys \<alpha>s i) = map tys"
    "sep_lifter.tys (idx_lifter tys \<alpha>s i) = tys"
    unfolding idx_lifter_def by auto    
            
  lemma idx_lifter[simp, intro!]: "sep_lifter (idx_lifter tys \<alpha>s i)"
    apply unfold_locales
    apply (simp_all add: idx_lifter_def)
    apply (auto simp: sep_algebra_simps)
    apply (auto simp: sep_disj_fun_def sep_algebra_simps intro!: exI[where x="f(i:=0::'a)" for f])
    apply (auto simp: list\<alpha>_def[abs_def] nth_list_update map_upd_eq split: if_splits)
    done
    
  fun option\<alpha> :: "('c \<Rightarrow> 'a) \<Rightarrow> 'c option \<Rightarrow> 'a::unique_zero_sep_algebra" 
    where "option\<alpha> \<alpha> None = 0" | "option\<alpha> \<alpha> (Some x) = \<alpha> x"
    
  lemma option\<alpha>_alt: "option\<alpha> \<alpha> x = (case x of None \<Rightarrow> 0 | Some y \<Rightarrow> \<alpha> y)" by (cases x) auto 
    
  definition "option_lifter tys \<alpha>s \<equiv> \<lparr>
    sep_lifter.lift = id,
    sep_lifter.project = id,
    sep_lifter.carve = \<lambda>_. 0,
    sep_lifter.splittable = (\<lambda>f. True),
    sep_lifter.L = the\<^sub>L,
    sep_lifter.\<alpha>b = option\<alpha> \<alpha>s,
    sep_lifter.\<alpha>s = \<alpha>s,
    sep_lifter.tyb = map_option tys,
    sep_lifter.tys = tys
  \<rparr>"  
    
  lemma option_lifter_simps[simp]:
    "sep_lifter.lift (option_lifter tys \<alpha>s) = id"
    "sep_lifter.project (option_lifter tys \<alpha>s) = id"
    "sep_lifter.carve (option_lifter tys \<alpha>s) = (\<lambda>_. 0)"
    "sep_lifter.splittable (option_lifter tys \<alpha>s) = (\<lambda>f. True)"
    "sep_lifter.L (option_lifter tys \<alpha>s) = the\<^sub>L"
    "sep_lifter.\<alpha>b (option_lifter tys \<alpha>s) = option\<alpha> \<alpha>s"
    "sep_lifter.\<alpha>s (option_lifter tys \<alpha>s) = \<alpha>s"
    "sep_lifter.tyb (option_lifter tys \<alpha>s) = map_option tys"
    "sep_lifter.tys (option_lifter tys \<alpha>s) = tys"
    unfolding option_lifter_def by auto
  
  
  
  lemma option_lifter[simp, intro!]: "sep_lifter (option_lifter tys \<alpha>s)"
    apply unfold_locales
    apply (auto simp: option_lifter_def)
    apply (auto simp: option\<alpha>_alt split: option.splits)
    done
  
  definition "compose_splittable l\<^sub>1 l\<^sub>2 \<equiv> (\<lambda>x. sep_lifter.splittable l\<^sub>2 x \<and> sep_lifter.splittable l\<^sub>1 (sep_lifter.project l\<^sub>2 x))"  
    
  definition "compose_carve l\<^sub>1 l\<^sub>2 \<equiv> \<lambda>x. 
    if compose_splittable l\<^sub>1 l\<^sub>2 x then
      sep_lifter.carve l\<^sub>2 x + sep_lifter.lift l\<^sub>2 ( sep_lifter.carve l\<^sub>1 (sep_lifter.project l\<^sub>2 x))
    else x"  
    
  definition 
    compose_lifter :: 
    "('as::unique_zero_sep_algebra,'cs,'ts,'ab::unique_zero_sep_algebra,'cb,'tb) sep_lifter 
      \<Rightarrow> ('ab,'cb,'tb,'al::unique_zero_sep_algebra,'cl,'tl) sep_lifter
      \<Rightarrow> ('as, 'cs, 'ts, 'al, 'cl, 'tl) sep_lifter"
    (infixl "\<bullet>\<^sub>l\<^sub>f\<^sub>t" 80)  
  where "compose_lifter l\<^sub>1 l\<^sub>2 \<equiv> \<lparr>
    sep_lifter.lift = sep_lifter.lift l\<^sub>2 o sep_lifter.lift l\<^sub>1,
    sep_lifter.project = sep_lifter.project l\<^sub>1 o sep_lifter.project l\<^sub>2,
    sep_lifter.carve = compose_carve l\<^sub>1 l\<^sub>2,
    sep_lifter.splittable = compose_splittable l\<^sub>1 l\<^sub>2,
    sep_lifter.L = sep_lifter.L l\<^sub>2 \<bullet>\<^sub>L sep_lifter.L l\<^sub>1,
    sep_lifter.\<alpha>b = sep_lifter.\<alpha>b l\<^sub>2,
    sep_lifter.\<alpha>s = sep_lifter.\<alpha>s l\<^sub>1,
    sep_lifter.tyb = sep_lifter.tyb l\<^sub>2,
    sep_lifter.tys = sep_lifter.tys l\<^sub>1
  \<rparr>"  

  lemma compose_lifter_simps:
    "sep_lifter.lift (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.lift l\<^sub>2 o sep_lifter.lift l\<^sub>1"
    "sep_lifter.project (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.project l\<^sub>1 o sep_lifter.project l\<^sub>2"
    "sep_lifter.carve (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = compose_carve l\<^sub>1 l\<^sub>2"
    "sep_lifter.splittable (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = compose_splittable l\<^sub>1 l\<^sub>2"
    "sep_lifter.L (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.L l\<^sub>2 \<bullet>\<^sub>L sep_lifter.L l\<^sub>1"
    "sep_lifter.\<alpha>b (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.\<alpha>b l\<^sub>2"
    "sep_lifter.\<alpha>s (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.\<alpha>s l\<^sub>1"
    "sep_lifter.tyb (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.tyb l\<^sub>2"
    "sep_lifter.tys (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) = sep_lifter.tys l\<^sub>1"
    unfolding compose_lifter_def by auto
                                              
  lemma compose_sep_lifter[simp, intro!]:
    fixes l\<^sub>1 :: "('as::unique_zero_sep_algebra, 'cs, 'ts, 'ab::unique_zero_sep_algebra, 'cb, 'tb) sep_lifter" 
      and l\<^sub>2 :: "('ab, 'cb, 'tb, 'al::unique_zero_sep_algebra, 'cl, 'tl) sep_lifter"
    assumes "sep_lifter l\<^sub>1"  
    assumes "sep_lifter l\<^sub>2"  
    assumes \<alpha>EQ: "sep_lifter.\<alpha>s l\<^sub>2 = sep_lifter.\<alpha>b l\<^sub>1"
    assumes tEQ: "sep_lifter.tys l\<^sub>2 = sep_lifter.tyb l\<^sub>1"
    shows "sep_lifter (compose_lifter l\<^sub>1 l\<^sub>2)"
  proof -
    interpret l1: sep_lifter l\<^sub>1 by fact
    interpret l2: sep_lifter l\<^sub>2 by fact

    show ?thesis
      apply unfold_locales
      apply (clarsimp_all 
        simp: compose_lifter_def compose_carve_def compose_splittable_def
        simp: sep_algebra_simps 
        )
      subgoal for b1 b2
        using l1.splittable_same_struct l2.splittable_same_struct by force
     
      subgoal for b1 b2 by auto
      subgoal by (clarsimp simp: l1.disj_project_eq_lift l2.disj_project_eq_lift sep_algebra_simps)
      subgoal 
        apply (rewrite at "_=\<hole>" l2.split_complete, assumption)
        apply (rewrite in "_=\<hole>" l1.split_complete, assumption)
        by (auto simp: sep_algebra_simps)
      proof goal_cases  
        fix cb
        assume A: 
          "l1.project (l2.project (l2.\<alpha>b cb)) \<noteq> 0"
          "l2.splittable (l2.\<alpha>b cb)"
          "l1.splittable (l2.project (l2.\<alpha>b cb))"
        then show "pre_get l2.L cb \<and> pre_get l1.L (get' l2.L cb)"
          using \<alpha>EQ l2.precond l1.sep_lifter_axioms l2.sep_lifter_axioms sep_lifter.get_xfer sep_lifter.precond 
          by fastforce
          
          
        hence [simp]: "pre_get l2.L cb" "pre_get l1.L (get' l2.L cb)" by auto
          
        from A show "l1.\<alpha>s (get' (l2.L \<bullet>\<^sub>L l1.L) cb) = l1.project (l2.project (l2.\<alpha>b cb))"
          using \<alpha>EQ l2.sep_lifter_axioms sep_lifter.get_xfer by fastforce
        
        fix x  
        assume "l1.tys x = l1.tys (get' (l2.L \<bullet>\<^sub>L l1.L) cb)"
        with A show "l2.\<alpha>b (put' (l2.L \<bullet>\<^sub>L l1.L) x cb) =
            l2.carve (l2.\<alpha>b cb) 
          + (l2.lift (l1.lift (l1.\<alpha>s x)) 
              + l2.lift (l1.carve (l2.project (l2.\<alpha>b cb))))"  
          apply (auto)
          apply (subst l2.put_xfer) apply (auto simp: tEQ) [3]
          apply (subst l1.put_xfer[folded \<alpha>EQ]; (subst l2.get_xfer)?; auto) 
          apply (auto simp: sep_algebra_simps)
          done
          
      qed (simp add: tEQ)
      
  qed    
    
    
  lemma compose_lifter_assoc[simp]:
    assumes "sep_lifter l\<^sub>1" "sep_lifter l\<^sub>2" "sep_lifter l\<^sub>3"
    shows "l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>3 = l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t (l\<^sub>2 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>3)"
  proof -
    interpret l1: sep_lifter l\<^sub>1 by fact
    interpret l2: sep_lifter l\<^sub>2 by fact
    interpret l3: sep_lifter l\<^sub>3 by fact
  
    show ?thesis
      unfolding compose_lifter_def compose_carve_def compose_splittable_def
      by (auto del: ext intro!: ext simp: sep_algebra_simps)
      
  qed
  
  lemma lift_assn_compose: 
    assumes "sep_lifter l\<^sub>1"
    assumes "sep_lifter l\<^sub>2"
    shows "pre_sep_lifter.lift_assn (l\<^sub>1 \<bullet>\<^sub>l\<^sub>f\<^sub>t l\<^sub>2) P = pre_sep_lifter.lift_assn l\<^sub>2 (pre_sep_lifter.lift_assn l\<^sub>1 P)"  
  proof -
    interpret l1: sep_lifter l\<^sub>1 by fact
    interpret l2: sep_lifter l\<^sub>2 by fact
  
    show ?thesis  
      apply (rule ext)
      apply (auto simp: pre_sep_lifter.lift_assn_def)
      apply (auto simp: compose_lifter_def compose_splittable_def compose_carve_def)
      done
  qed
    
  definition "id_lifter ty \<alpha> \<equiv> \<lparr>
    sep_lifter.lift = id,
    sep_lifter.project = id,
    sep_lifter.carve = \<lambda>x. 0,
    sep_lifter.splittable = (\<lambda>f. True),
    sep_lifter.L = id\<^sub>L,
    sep_lifter.\<alpha>b = \<alpha>,
    sep_lifter.\<alpha>s = \<alpha>,
    sep_lifter.tyb = ty,
    sep_lifter.tys = ty
  \<rparr>"
  
  lemma id_lifter_simps[simp]:
    "sep_lifter.lift (id_lifter ty \<alpha>) = id"
    "sep_lifter.project (id_lifter ty \<alpha>) = id"
    "sep_lifter.carve (id_lifter ty \<alpha>) = (\<lambda>x. 0)"
    "sep_lifter.splittable (id_lifter ty \<alpha>) = (\<lambda>f. True)"
    "sep_lifter.L (id_lifter ty \<alpha>) = id\<^sub>L"
    "sep_lifter.\<alpha>b (id_lifter ty \<alpha>) = \<alpha>"
    "sep_lifter.\<alpha>s (id_lifter ty \<alpha>) = \<alpha>"
    "sep_lifter.tyb (id_lifter ty \<alpha>) = ty"
    "sep_lifter.tys (id_lifter ty \<alpha>) = ty"
    unfolding id_lifter_def by auto
    
  
  
  lemma id_lifter[simp, intro!]: "sep_lifter (id_lifter ty \<alpha>)"
    apply unfold_locales
    apply (auto simp: id_lifter_def)
    done
  
  lemma compose_lifter_id_left[simp]:
    assumes "sep_lifter l" shows "id_lifter (sep_lifter.tys l) (sep_lifter.\<alpha>s l) \<bullet>\<^sub>l\<^sub>f\<^sub>t l = l"  
  proof -
    interpret sep_lifter l by fact
    
    have [simp]: "compose_carve (id_lifter (sep_lifter.tys l) (sep_lifter.\<alpha>s l)) l = carve"
      by (rule ext) (auto simp: compose_carve_def compose_splittable_def id_lifter_def)
    
    show ?thesis 
      apply (auto simp: compose_lifter_def)
      apply (auto simp: compose_splittable_def id_lifter_def)
      done
  qed    

  lemma compose_lifter_id_right[simp]:
    assumes "sep_lifter l" shows "l \<bullet>\<^sub>l\<^sub>f\<^sub>t (id_lifter (sep_lifter.tyb l) (sep_lifter.\<alpha>b l)) = l"  
  proof -
    interpret sep_lifter l by fact
    
    have [simp]: "compose_carve l (id_lifter (sep_lifter.tyb l) (sep_lifter.\<alpha>b l)) = carve"
      by (rule ext) (auto simp: compose_carve_def compose_splittable_def id_lifter_def)
    
    show ?thesis
      apply (auto simp: compose_lifter_def)
      apply (auto simp: compose_splittable_def id_lifter_def)
      done
      
  qed    
    
end
