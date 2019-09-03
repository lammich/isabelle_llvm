(*
  Partially inspired by Simon Foster's lens theory
*)
theory Lenses
  imports Main "HOL-Library.Adhoc_Overloading"
  keywords "define_lenses" :: thy_decl
begin

  section \<open>Lenses\<close>


  datatype ('a,'s) lens (infixr "\<Longrightarrow>" 1) =
    LENS (get: "'s \<Rightarrow> 'a option") (put: "'a \<Rightarrow> 's \<Rightarrow> 's option")


  definition "pre_put L s \<equiv> \<forall>x. put L x s \<noteq> None"
  definition "pre_get L s \<equiv> get L s \<noteq> None"
  definition "get' L s = the (get L s)"
  definition "put' L x s = the (put L x s)"

  locale lens =
    fixes L :: "'a \<Longrightarrow> 's"
    (*assumes pre_get_imp: "pre_put L x s \<Longrightarrow> pre_get L s"*)
    assumes pre_get_imp_put: "get L s \<noteq> None \<Longrightarrow> put L x s \<noteq> None"

    assumes pre_put_indep_val: "put L y s\<noteq>None \<Longrightarrow> put L x s \<noteq> None"

    assumes get_put_pre: "pre_put L s \<Longrightarrow> pre_get L (put' L x s)"
    assumes get_put: "pre_put L s \<Longrightarrow> get' L (put' L x s) = x"
    assumes put_get: "pre_get L s \<Longrightarrow> put' L (get' L s) s = s"
    assumes put_put: "pre_put L s \<Longrightarrow> put' L x (put' L y s) = put' L x s"
  begin
    lemmas laws = get_put put_get put_put
    lemmas pre_laws = get_put_pre

    lemma pre_put_indep_val1: "put L y s = Some s' \<Longrightarrow> \<exists>s'. put L x s = Some s'"
      using pre_put_indep_val by fastforce

    lemma pre_put_indep_val2: "put L y s=None \<Longrightarrow> put L x s=None"
      using pre_put_indep_val by blast

    lemma get':
      "get L s = Some v \<longleftrightarrow> pre_get L s \<and> v=get' L s"
      "get L s = None \<longleftrightarrow> \<not>pre_get L s"
      unfolding pre_get_def get'_def
      apply (auto)
      done

    lemma put':
      "put L x s = Some s' \<longleftrightarrow> pre_put L s \<and> s'=put' L x s"
      "put L x s = None \<longleftrightarrow> \<not>pre_put L s"
      unfolding pre_put_def put'_def
      by (auto 0 1 simp: pre_put_indep_val2 intro: pre_put_indep_val1)

    lemma pre_get_imp_putI: "pre_get L s \<Longrightarrow> pre_put L s"
      unfolding pre_get_def
      apply (drule pre_get_imp_put)
      by (simp add: put')

    lemmas simp_rls[simp] = laws pre_laws get' put' pre_get_imp_putI
    (*lemmas intro_rls[intro] = TrueI*)
  end


  locale hlens = lens L for L :: "'a \<Longrightarrow> 's" +
    assumes pre_get_imp_put: "pre_put L s \<Longrightarrow> pre_get L s"
  begin
    lemma pre_put_eq: "pre_put L s \<longleftrightarrow> pre_get L s"
      using pre_get_imp_put by auto

    lemmas hsimp_rls[simp] = pre_put_eq
    lemmas is_lens = lens_axioms
  end

  
  locale lens_for_presentation =
    fixes L :: "'a \<Longrightarrow> 's"
    assumes get_put: "put L x s = Some s' \<Longrightarrow> get L s' = Some x"
    assumes put_get: "get L s = Some x \<Longrightarrow> put L x s = Some s"
    assumes put_put: "\<lbrakk>put L x s = Some s'; put L y s = Some s'' \<rbrakk> \<Longrightarrow> put L x s'' = Some s'"
    
    assumes put_indep: "put L y s\<noteq>None \<longleftrightarrow> get L s \<noteq> None"

  lemma "hlens L = lens_for_presentation L"    
    unfolding hlens_def lens_def hlens_axioms_def lens_for_presentation_def 
    unfolding pre_put_def pre_get_def
    apply clarsimp
    apply (safe)        
    subgoal by (metis get'_def option.sel put'_def)
    subgoal by (metis get'_def option.sel put'_def)
    subgoal by (metis option.case(2) option.the_def put'_def) 
    subgoal by metis
    subgoal by blast
    subgoal by blast
    subgoal by metis
    subgoal by (metis option.sel put'_def)
    subgoal by (metis get'_def option.sel put'_def)
    subgoal by (metis get'_def option.sel put'_def)
    subgoal by (metis option.case(2) option.the_def put'_def)
    subgoal by metis
    done
  
  declare lens.simp_rls[simp]
  declare hlens.hsimp_rls[simp]
  declare hlens.is_lens[simp]

  text \<open>Required for rules where lens-property cannot be assumed, e.g., split rules\<close>
  definition "pre_put_single_point L b a \<longleftrightarrow> put L b a \<noteq> None"
  lemma pre_put_single_point[simp]: "lens L \<Longrightarrow> pre_put_single_point L b a = pre_put L a"
    by (auto simp: pre_put_single_point_def)


  (*declare lens.intro_rls[intro]*)

  lemma LENS_downstage[simp]:
    "pre_get (LENS g p) s \<longleftrightarrow> g s \<noteq> None"
    "pre_put (LENS g p) s \<longleftrightarrow> (\<forall>x. p x s \<noteq> None)"
    "get' (LENS g p) = (\<lambda>s. the (g s))"
    "put' (LENS g p) = (\<lambda>x s. the (p x s))"
    "get (LENS g p) = g"
    "put (LENS g p) = p"
    unfolding pre_get_def pre_put_def get'_def put'_def by auto

  lemma put_get'_combine[simp]:
    "(get L s \<noteq> None) = pre_get L s"
    (*"lens L \<Longrightarrow> (put L x s = None) \<longleftrightarrow> \<not>pre_put L s"*)
    "the (get L s) = get' L s"
    "the (put L x s) = put' L x s"
    unfolding get'_def put'_def pre_get_def pre_put_def by (auto simp: prod_eqI)


  lemma lens_ext[intro?]:
    assumes "lens l1" "lens l2"
    assumes "\<And>s. pre_get l1 s = pre_get l2 s"
    assumes "\<And>s x. pre_put l1 s = pre_put l2 s"
    assumes "\<And>s. pre_get l2 s \<Longrightarrow> get' l1 s = get' l2 s"
    assumes "\<And>s x. pre_put l2 s \<Longrightarrow> put' l1 x s = put' l2 x s"
    shows "l1 = l2"
    using assms
    apply (cases l1; cases l2; simp)
    apply (auto intro!: ext)
    apply (metis option.collapse option.simps(5) option.the_def)
    by (metis LENS_downstage(4) assms(4) assms(6) lens.put'(2) lens.sel(2) option.expand)

  subsection \<open>Lens Algebra\<close>

  subsubsection \<open>Identity Lens\<close>

  definition id\<^sub>L :: "'a \<Longrightarrow> 'a" where "id\<^sub>L \<equiv> LENS (\<lambda>x. Some x) (\<lambda>x s. Some x)"

  lemma [simp, intro!]: "hlens id\<^sub>L"
    by (unfold_locales) (auto simp: id\<^sub>L_def)

  lemma [simp, intro!]:
    "pre_get id\<^sub>L s"
    "pre_put id\<^sub>L s"
    by (auto simp: id\<^sub>L_def)

  lemma [simp]:
    "get' id\<^sub>L s = s"
    "put' id\<^sub>L x s = x"
    by (auto simp: id\<^sub>L_def)

  subsubsection \<open>Lens Composition\<close>

  definition comp\<^sub>L :: "('a,'b) lens \<Rightarrow> ('b,'c) lens \<Rightarrow> ('a,'c) lens"
  where
    "comp\<^sub>L L1 L2 \<equiv> LENS
      (\<lambda>s. Option.bind (get L2 s) (get L1))
      (\<lambda>x s.
        Option.bind (get L2 s) (\<lambda>s'.
        Option.bind (put L1 x s') (\<lambda>s'.
        put L2 s' s)))
      "

  notation (input) comp\<^sub>L (infixr ";\<^sub>L" 80)
  abbreviation bcomp\<^sub>L (infixl "\<bullet>\<^sub>L" 80) where "bcomp\<^sub>L x y \<equiv> comp\<^sub>L y x"

  lemma comp_lens[simp, intro!]:
    assumes [simp, intro!]: "lens l1" "lens l2"
    shows "lens (l1;\<^sub>Ll2)"
    apply (unfold_locales)
    apply (auto simp: comp\<^sub>L_def split: Option.bind_splits prod.splits)
    done

  lemma comp_hlens[simp, intro!]:
    assumes [simp, intro!]: "hlens l1" "hlens l2"
    shows "hlens (l1;\<^sub>Ll2)"
    apply (unfold_locales)
    apply (auto simp: comp\<^sub>L_def split: Option.bind_splits prod.splits)
    done


  lemma compL_pre_get[simp]: "\<lbrakk>lens l1; lens l2\<rbrakk> \<Longrightarrow> pre_get (l1;\<^sub>Ll2) s \<longleftrightarrow> pre_get l2 s \<and> pre_get l1 (get' l2 s)"
    unfolding comp\<^sub>L_def
    by (auto split: option.splits Option.bind_splits)

  lemma compL_pre_put[simp]: "\<lbrakk>lens l1; lens l2\<rbrakk> \<Longrightarrow> pre_put (l1;\<^sub>Ll2) s
    \<longleftrightarrow> pre_get l2 s \<and> pre_put l1 (get' l2 s)"
    unfolding comp\<^sub>L_def
    by (auto split: option.splits Option.bind_splits)


  lemma compL_decomp[simp]:
    assumes [simp]: "lens l1" "lens l2"
    shows
    "pre_get (l1;\<^sub>Ll2) s \<Longrightarrow> get' (l1;\<^sub>Ll2) s = (get' l1 (get' l2 s))"
    "pre_put (l1;\<^sub>Ll2) s \<Longrightarrow> put' (l1;\<^sub>Ll2) x s = put' l2 (put' l1 x (get' l2 s)) s"
    by (auto simp: comp\<^sub>L_def split: prod.splits option.splits Option.bind_splits)


  subsubsection \<open>Monoid Laws\<close>

  thm prod.splits

  lemma id_left_neutral[simp]:
    "hlens a \<Longrightarrow> id\<^sub>L;\<^sub>La = a"
    apply (rule)
    apply (auto simp: )
    done

  lemma id_right_neutral[simp]:
    "lens a \<Longrightarrow> a;\<^sub>Lid\<^sub>L = a"
    by (rule) auto


  lemma assoc_comp_weak: "lens a \<Longrightarrow> lens b \<Longrightarrow> lens c \<Longrightarrow> (a;\<^sub>Lb);\<^sub>Lc = a;\<^sub>Lb;\<^sub>Lc"
    by (rule) auto

  lemma assoc_comp[simp]: "(a;\<^sub>Lb);\<^sub>Lc = a;\<^sub>Lb;\<^sub>Lc"
    unfolding comp\<^sub>L_def by (auto intro!: ext split: Option.bind_splits)


  subsubsection \<open>Independence\<close>

  (* TODO: Move
  lemma option_eq_casesI:
    assumes "a=None \<Longrightarrow> b=None"
    assumes "\<And>x. a=Some x \<Longrightarrow> b=Some x"
    shows "a = b"
    by (cases a; cases b; simp add: assms)
  *)

  locale lens_indep =
    fixes X :: "'a \<Longrightarrow> 'c" and Y :: "'b \<Longrightarrow> 'c"
    assumes get_put_irr1Some: "pre_put Y s \<Longrightarrow> get X (put' Y y s) = Some x \<Longrightarrow> get X s = Some x"
    assumes get_put_irr1None: "pre_put Y s \<Longrightarrow> get X (put' Y y s) = None \<Longrightarrow> get X s = None"
    assumes get_put_irr2Some: "pre_put X s \<Longrightarrow> get Y (put' X x s) = Some y \<Longrightarrow> get Y s = Some y"
    assumes get_put_irr2None: "pre_put X s \<Longrightarrow> get Y (put' X x s) = None \<Longrightarrow> get Y s = None"
    assumes pre_put_irr1:  "pre_put X s \<Longrightarrow> pre_put Y (put' X x s) \<longleftrightarrow> pre_put Y s"
    assumes pre_put_irr2: "pre_put Y s \<Longrightarrow> pre_put X (put' Y y s) \<longleftrightarrow> pre_put X s"
    assumes comm: "\<lbrakk> pre_put X s; pre_put Y s \<rbrakk> \<Longrightarrow> put' X x (put' Y y s) = put' Y y (put' X x s)"
  begin

    lemma get_put_irr1: "pre_put Y s \<Longrightarrow> get X (put' Y y s) = get X s"
      using get_put_irr1None get_put_irr1Some by fastforce

    lemma get_put_irr2: "pre_put X s \<Longrightarrow> get Y (put' X x s) = get Y s"
      using get_put_irr2None get_put_irr2Some by fastforce

    lemma lens_indep_get':
      "pre_put X s \<Longrightarrow> get' Y (put' X x s) = get' Y s"
      "pre_put Y s \<Longrightarrow> get' X (put' Y y s) = get' X s"
      apply (metis get'_def get_put_irr2)
      apply (metis get'_def get_put_irr1)
      done

    lemma lens_indep_pre_get':
      "pre_put Y s \<Longrightarrow> pre_get X (put' Y y s) \<longleftrightarrow> pre_get X s"
      "pre_put X s \<Longrightarrow> pre_get Y (put' X x s) \<longleftrightarrow> pre_get Y s"
      by (auto simp add: get_put_irr1 get_put_irr2 pre_get_def)

    lemmas simps[simp] = lens_indep_get' lens_indep_pre_get' pre_put_irr1 pre_put_irr2

  end

  declare lens_indep.simps[simp]

  notation lens_indep (infix "\<bowtie>" 50)

  lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
    unfolding lens_indep_def by simp

  lemmas lens_indep_comm = lens_indep.comm

  lemma lens_indep_left_comp:
    assumes [simp]: "x \<bowtie> y" "lens x" "lens y" "lens z"
    shows "(x ;\<^sub>L z) \<bowtie> (y ;\<^sub>L z)"
    apply (unfold_locales)
    apply (auto simp: comp\<^sub>L_def lens_indep_comm split!: Option.bind_splits)
    done

  lemma lens_indep_right_comp:
    assumes [simp]: "y \<bowtie> z" "lens x" "lens y" "lens z"
    shows "(x ;\<^sub>L y) \<bowtie> (x ;\<^sub>L z)"
    apply (unfold_locales)
    apply (auto simp: comp\<^sub>L_def lens_indep_comm split!: Option.bind_splits)
    done

  lemma lens_indep_left_ext:
    assumes [simp]: "y \<bowtie> z" "lens x" "lens y" "lens z"
    shows "(x ;\<^sub>L y) \<bowtie> z"
    apply (unfold_locales)
    apply (auto simp: comp\<^sub>L_def lens_indep_comm split!: Option.bind_splits)
    done

  lemma lens_indep_right_ext:
    assumes [simp]: "x \<bowtie> z" "lens x" "lens y" "lens z"
    shows "x \<bowtie> (y ;\<^sub>L z)"
    by (simp add: lens_indep_left_ext lens_indep_sym)

  lemma lens_indep_extend2:
    assumes [simp]: "x \<bowtie> y" "lens x" "lens y" "lens a" "lens b"
    shows "a ;\<^sub>L x \<bowtie> b ;\<^sub>L y"
    apply (unfold_locales)
    apply (auto simp: comp\<^sub>L_def lens_indep_comm split!: Option.bind_splits)
    done

  definition rnlens :: "('a \<Longrightarrow> 'b) \<Rightarrow> bool" where "rnlens L \<equiv> lens L \<and> (\<exists>x y::'a. \<exists>s. x\<noteq>y \<and> pre_put L s)"

  lemma rnlensI[intro?]:
    fixes L :: "'a \<Longrightarrow> 'b"
    assumes "lens L"
    assumes "(x::'a) \<noteq> y"
    assumes "pre_put L s"
    shows "rnlens L"
    using assms unfolding rnlens_def by auto
  
  lemma rnlens_compI[simp, intro]: "\<lbrakk>rnlens A; rnlens B\<rbrakk> \<Longrightarrow> rnlens (A\<bullet>\<^sub>LB)"
    apply (auto simp: rnlens_def)
    using lens.get_put_pre by fastforce
  
  lemma rnlens_id_iff[simp]: "rnlens (id\<^sub>L :: 'a \<Longrightarrow> 'a) \<longleftrightarrow> (\<exists>a b::'a. a\<noteq>b)"  
    by (auto simp: rnlens_def)
  
  lemma rnlens_imp_lens[simp]: "rnlens L \<Longrightarrow> lens L"
    by (auto simp: rnlens_def)
    
  lemma rnl_indep_not_refl[simp, intro]:
    "rnlens L \<Longrightarrow> \<not>(L \<bowtie> L)"
    unfolding rnlens_def
    by (metis (full_types) lens.get_put lens_indep.lens_indep_get'(2))

  lemma rnl_indep_not_id[simp, intro]:
    assumes "rnlens L"
    shows "\<not>(id\<^sub>L \<bowtie> L)" "\<not>(L \<bowtie> id\<^sub>L)" 
  proof -
    show "\<not>(id\<^sub>L \<bowtie> L)"
      using assms unfolding rnlens_def
      by (metis (mono_tags, lifting) id\<^sub>L_def lens.get_put lens.sel(1) lens_indep.get_put_irr1 option.sel)
    thus "\<not>(L \<bowtie> id\<^sub>L)"
      using lens_indep_sym by auto
  qed
    
  subsubsection \<open>Complete Lenses\<close>
  definition "complete_lens L \<equiv> lens L \<and> (\<forall>x. \<exists>y. pre_get L y \<and> get' L y = x)"
  
  lemma complete_lens_is_lens[simp, intro]: "complete_lens L \<Longrightarrow> lens L"
    by (auto simp: complete_lens_def)

  lemma complete_lensI[intro?]: 
    assumes "lens L"  
    assumes "\<And>x. \<exists>y. pre_get L y \<and> get' L y = x"
    shows "complete_lens L"
    using assms by (auto simp: complete_lens_def)

  lemma complete_lensE:
    assumes "complete_lens L"  
    obtains y where "pre_get L y" "get' L y = x"
    using assms by (auto simp: complete_lens_def)
      
  lemma lens_indep_shrink_left:
    assumes [simp, intro!]: "lens L\<^sub>1" "lens L\<^sub>2"
    assumes COMPL[simp, intro!]: "complete_lens L"
    assumes INDEP: "L \<bullet>\<^sub>L L\<^sub>1 \<bowtie> L \<bullet>\<^sub>L L\<^sub>2"
    shows "L\<^sub>1 \<bowtie> L\<^sub>2"
    apply standard  
  proof -
    fix s
    obtain ss where [simp]: "pre_get L ss" "get' L ss = s" using COMPL by (rule complete_lensE)
  
    interpret lens_indep "L \<bullet>\<^sub>L L\<^sub>1" "L \<bullet>\<^sub>L L\<^sub>2" by fact
    
    {
      fix x y
      assume "pre_put L\<^sub>2 s" "lens.get L\<^sub>1 (put' L\<^sub>2 y s) = Some x"
      with get_put_irr1Some[of ss y x] show "lens.get L\<^sub>1 s = Some x" by auto
    }    
    
    {
      fix y
      assume "pre_put L\<^sub>2 s" "lens.get L\<^sub>1 (put' L\<^sub>2 y s) = None"
      with get_put_irr1None[of ss y] show "lens.get L\<^sub>1 s = None" by auto
    }    
    
    {
      fix x y
      assume "pre_put L\<^sub>1 s" "lens.get L\<^sub>2 (put' L\<^sub>1 x s) = Some y"
      with get_put_irr2Some[of ss x y] show "lens.get L\<^sub>2 s = Some y" by auto
    }    
    
    {
      fix x
      assume "pre_put L\<^sub>1 s" "lens.get L\<^sub>2 (put' L\<^sub>1 x s) = None"
      with get_put_irr2None[of ss x] show "lens.get L\<^sub>2 s = None" by auto
    }    

    {
      fix x
      assume "pre_put L\<^sub>1 s" 
      with pre_put_irr1[of ss x] show "pre_put L\<^sub>2 (put' L\<^sub>1 x s) = pre_put L\<^sub>2 s" by auto
    } note n_pre_put_irr1 = this
    
    {
      fix y
      assume "pre_put L\<^sub>2 s" 
      with pre_put_irr2[of ss y] show "pre_put L\<^sub>1 (put' L\<^sub>2 y s) = pre_put L\<^sub>1 s" by auto
    } note n_pre_put_irr2 = this
    
    {
      fix x y
      assume [simp]: "pre_put L\<^sub>1 s" "pre_put L\<^sub>2 s" 

      note comm[of ss x y]
      
      have "put' L\<^sub>1 x (put' L\<^sub>2 y s) = get' L (put' (L\<bullet>\<^sub>LL\<^sub>1) x (put' (L\<bullet>\<^sub>LL\<^sub>2) y ss))"
        by (auto simp: n_pre_put_irr2)
      also from comm[of ss x y] have "\<dots> = get' L (put' (L\<bullet>\<^sub>LL\<^sub>2) y (put' (L\<bullet>\<^sub>LL\<^sub>1) x ss))" by simp
      also have "\<dots> = put' L\<^sub>2 y (put' L\<^sub>1 x s)" by (auto simp: n_pre_put_irr1)
      finally show "put' L\<^sub>1 x (put' L\<^sub>2 y s) = put' L\<^sub>2 y (put' L\<^sub>1 x s)" .
    }
  qed
    
  lemma lens_indep_left_comp_complete_iff[simp]:
    assumes "complete_lens z" "lens x" "lens y"
    shows "z \<bullet>\<^sub>L x \<bowtie> z \<bullet>\<^sub>L y \<longleftrightarrow> x \<bowtie> y"
    by (meson assms complete_lens_def lens_indep_left_comp lens_indep_shrink_left)
  
  
  
  subsubsection \<open>Transfer of Values\<close>
  text \<open>Relation that indicates that \<open>s'\<close> originated from \<open>s\<close> by changing \<open>L\<close>\<close>
  definition ltrans where "ltrans L s s' \<equiv> lens L \<and> (\<exists>x. put L x s = Some s')"

  lemma ltransI[simp]: "lens L \<Longrightarrow> pre_put L s \<Longrightarrow> ltrans L s (put' L x s)"
    unfolding ltrans_def by auto

  lemma ltrans_trans[simp]: "ltrans L OO ltrans L = ltrans L"
    unfolding ltrans_def by fastforce

  lemma ltrans_push_indep:
    assumes "L \<bowtie> L'"
    assumes "ltrans L' s s'"
    shows "get L s = get L s'"
    using assms
    by (auto simp: ltrans_def lens_indep.get_put_irr1)

  text \<open>Predicate to indicate that all states in relation \<open>R\<close> are equal on \<open>L\<close>\<close>
  definition eq_on\<^sub>L where "eq_on\<^sub>L R L \<equiv> \<forall>s s'. R s s' \<longrightarrow> get L s = get L s'"

  lemma eq_on_compI: "eq_on\<^sub>L R\<^sub>1 L \<Longrightarrow> eq_on\<^sub>L R\<^sub>2 L \<Longrightarrow> eq_on\<^sub>L (R\<^sub>1 OO R\<^sub>2) L"
    by (auto simp: eq_on\<^sub>L_def)

  lemma eq_on_ltrans_indepI: "L \<bowtie> L' \<Longrightarrow> eq_on\<^sub>L (ltrans L') L"
    by (auto simp: eq_on\<^sub>L_def ltrans_push_indep)


  subsection \<open>Lens Instances\<close>

  subsubsection \<open>Function\<close>

  definition fun\<^sub>L :: "'a \<Rightarrow> 'b \<Longrightarrow> ('a\<Rightarrow>'b)" where
    "fun\<^sub>L x \<equiv> LENS (\<lambda>f. Some (f x)) (\<lambda>y f. Some (f(x:=y)))"

  lemma fun_lens[simp, intro!]: "hlens (fun\<^sub>L x)"
    by (unfold_locales) (auto simp: fun\<^sub>L_def)

  lemma funL_pre[simp]:
    "pre_get (fun\<^sub>L x) s"
    "pre_put (fun\<^sub>L x) s"
    by (auto simp: fun\<^sub>L_def)

  lemma funL_getput'[simp]:
    "get' (fun\<^sub>L x) f = f x"
    "put' (fun\<^sub>L x) a f = f(x:=a)"
    by (auto simp: fun\<^sub>L_def)

  lemma fun\<^sub>L_indepI[simp]: "x\<noteq>y \<Longrightarrow> fun\<^sub>L x \<bowtie> fun\<^sub>L y"
    by standard (auto simp: fun\<^sub>L_def)


  subsubsection \<open>Products\<close>
  definition fst\<^sub>L :: "'a \<Longrightarrow> 'a \<times> 'b" where "fst\<^sub>L \<equiv> LENS (\<lambda>(a,_). Some a) (\<lambda>a (_,b). Some (a,b))"
  definition snd\<^sub>L :: "'b \<Longrightarrow> 'a \<times> 'b" where "snd\<^sub>L \<equiv> LENS (\<lambda>(_,b). Some b) (\<lambda>b (a,_). Some (a,b))"

  lemma fst_lens[simp,intro!]: "hlens fst\<^sub>L"
    by (unfold_locales) (auto simp: fst\<^sub>L_def)

  lemma snd_lens[simp,intro!]: "hlens snd\<^sub>L"
    by (unfold_locales) (auto simp: snd\<^sub>L_def)

  lemma fstL_getput'[simp]:
    "get' fst\<^sub>L x = fst x"
    "put' fst\<^sub>L a x = (a,snd x)"
    by (auto simp: fst\<^sub>L_def split: prod.splits)

  lemma sndL_getput'[simp]:
    "get' snd\<^sub>L x = snd x"
    "put' snd\<^sub>L b x = (fst x,b)"
    by (auto simp: snd\<^sub>L_def split: prod.splits)

  lemma fstL_pre[simp, intro!]: "pre_get fst\<^sub>L s" "pre_put fst\<^sub>L s" by (auto simp: fst\<^sub>L_def split: prod.splits)
  lemma sndL_pre[simp, intro!]: "pre_get snd\<^sub>L s" "pre_put snd\<^sub>L s" by (auto simp: snd\<^sub>L_def split: prod.splits)

  lemma prod_indep[simp]: "fst\<^sub>L \<bowtie> snd\<^sub>L"
    by unfold_locales auto


  subsubsection \<open>Lists\<close>

  definition idx\<^sub>L :: "nat \<Rightarrow> ('a \<Longrightarrow> 'a list)" where
    "idx\<^sub>L i \<equiv> LENS
      (\<lambda>s. if i<length s then Some (s!i) else None)
      (\<lambda>x s. if i<length s then Some (s[i:=x]) else None)"

  definition hd\<^sub>L :: "'a \<Longrightarrow> 'a list" where
    "hd\<^sub>L \<equiv> LENS (\<lambda>x#_\<Rightarrow> Some x | _ \<Rightarrow> None) (\<lambda>x. \<lambda>_#xs \<Rightarrow> Some (x#xs) | _ \<Rightarrow> None )"

  definition tl\<^sub>L :: "'a list \<Longrightarrow> 'a list" where
    "tl\<^sub>L \<equiv> LENS (\<lambda>_#xs\<Rightarrow> Some xs | _ \<Rightarrow> None) (\<lambda>xs. \<lambda>x#_ \<Rightarrow> Some (x#xs) | _ \<Rightarrow> None )"

  definition last\<^sub>L :: "'a \<Longrightarrow> 'a list" where
    "last\<^sub>L \<equiv> LENS
      (\<lambda>xs. if xs\<noteq>[] then Some (last xs) else None)
      (\<lambda>x xs. if xs\<noteq>[] then Some (butlast xs @ [x]) else None)"

  lemma idx_lens[simp, intro!]: "hlens (idx\<^sub>L i)"
    by (unfold_locales) (auto simp: idx\<^sub>L_def split: if_splits prod.splits Option.bind_splits)

  lemma idxL_pre[simp]:
    "pre_get (idx\<^sub>L i) s \<longleftrightarrow> i < length s"
    "pre_put (idx\<^sub>L i) s \<longleftrightarrow> i < length s"
    by (auto simp: idx\<^sub>L_def split: if_splits Option.bind_splits)

  lemma idxL_getput'[simp]:
    "pre_get (idx\<^sub>L i) l \<Longrightarrow> get' (idx\<^sub>L i) l = l!i"
    "pre_put (idx\<^sub>L i) l \<Longrightarrow> put' (idx\<^sub>L i) a l = l[i:=a]"
    by (auto simp: idx\<^sub>L_def split: prod.splits Option.bind_splits)

  lemma hd_lens[simp, intro!]: "hlens (hd\<^sub>L)"
    by (unfold_locales) (auto simp: hd\<^sub>L_def split: list.splits)

  lemma hd_lens_pre[simp]:
    "pre_get hd\<^sub>L l \<longleftrightarrow> l\<noteq>[]"
    "pre_put hd\<^sub>L l \<longleftrightarrow> l\<noteq>[]"
    by (auto simp: hd\<^sub>L_def split: list.splits)

  lemma hd_lens_getput'[simp]:
    "pre_get hd\<^sub>L l \<Longrightarrow> get' hd\<^sub>L l = hd l"
    "pre_put hd\<^sub>L l \<Longrightarrow> put' hd\<^sub>L x l = x # tl l"
    by (auto simp: hd\<^sub>L_def split: list.splits)

  lemma tl_lens[simp, intro!]: "hlens (tl\<^sub>L)"
    by (unfold_locales) (auto simp: tl\<^sub>L_def split: list.splits)

  lemma tlL_pre[simp]:
    "pre_get tl\<^sub>L l \<longleftrightarrow> l\<noteq>[]"
    "pre_put tl\<^sub>L l \<longleftrightarrow> l\<noteq>[]"
    by (auto simp: tl\<^sub>L_def split: list.splits)

  lemma tlL_getput'[simp]:
    "pre_get tl\<^sub>L l \<Longrightarrow> get' tl\<^sub>L l = tl l"
    "pre_put tl\<^sub>L l \<Longrightarrow> put' tl\<^sub>L xs l = hd l # xs"
    by (auto simp: tl\<^sub>L_def split: list.splits)

  lemma last_lens[simp, intro!]: "hlens (last\<^sub>L)"
    by (unfold_locales) (auto simp: last\<^sub>L_def split: prod.splits Option.bind_splits)

  lemma lastL_pre[simp]:
    "pre_get last\<^sub>L l \<longleftrightarrow> l\<noteq>[]"
    "pre_put last\<^sub>L l \<longleftrightarrow> l\<noteq>[]"
    by (auto simp: last\<^sub>L_def)

  lemma lastL_getput'[simp]:
    "pre_get last\<^sub>L l \<Longrightarrow> get' last\<^sub>L l = last l"
    "pre_put last\<^sub>L l \<Longrightarrow> put' last\<^sub>L x l = butlast l@[x]"
    by (auto simp: last\<^sub>L_def split: prod.splits Option.bind_splits)


  lemma hdL_is_idx0: "hd\<^sub>L = idx\<^sub>L 0"
    unfolding hd\<^sub>L_def idx\<^sub>L_def
    by (auto split: list.splits if_splits intro!: ext)

  lemma hd_tl_indep[simp]: "hd\<^sub>L \<bowtie> tl\<^sub>L"
    by unfold_locales auto

  lemma idx\<^sub>L_indep[simp]: "i\<noteq>j \<Longrightarrow> idx\<^sub>L i \<bowtie> idx\<^sub>L j"
    apply unfold_locales
    by (auto simp: list_update_swap)




  subsubsection \<open>Option\<close>
  definition "the\<^sub>L \<equiv>
    LENS (\<lambda>x. x) (\<lambda>x. \<lambda>Some _ \<Rightarrow> Some (Some x) | _ \<Rightarrow> None)"

  lemma the_lens[simp, intro!]: "hlens (the\<^sub>L)"
    by (unfold_locales) (auto simp: the\<^sub>L_def split: option.splits)

  lemma theL_pre[simp]:
    "pre_get the\<^sub>L l \<longleftrightarrow> l\<noteq>None"
    "pre_put the\<^sub>L l \<longleftrightarrow> l\<noteq>None"
    by (auto simp: the\<^sub>L_def split: option.split)

  lemma theL_getput'[simp]:
    "pre_get the\<^sub>L l \<Longrightarrow> get' the\<^sub>L l = the l"
    "pre_put the\<^sub>L l \<Longrightarrow> put' the\<^sub>L x l = Some x"
    by (auto simp: the\<^sub>L_def split: option.split)


  definition "crov\<^sub>L \<equiv>
    LENS (\<lambda>x. x) (\<lambda>x _. Some (Some x))"

  lemma crov_lens[simp, intro!]: "lens (crov\<^sub>L)"
    by (unfold_locales) (auto simp: crov\<^sub>L_def split: option.splits)

  lemma crovL_pre[simp]:
    "pre_get crov\<^sub>L l \<longleftrightarrow> l\<noteq>None"
    "pre_put crov\<^sub>L l"
    by (auto simp: crov\<^sub>L_def split: option.split)

  lemma crovL_getput'[simp]:
    "pre_get crov\<^sub>L l \<Longrightarrow> get' crov\<^sub>L l = the l"
    "pre_put crov\<^sub>L l \<Longrightarrow> put' crov\<^sub>L x l = Some x"
    by (auto simp: crov\<^sub>L_def split: option.split)

  subsection \<open>Datatype Lens Generation\<close>

  context begin
    private lemma theMO_return: "the (Some x) = x" by simp
    private lemma domMO_return: "Some x \<noteq> None" by simp
    private lemma domMO_None: "\<not>(None \<noteq> None)" by simp

    private lemma the_None_undefined: "the None = undefined"
      unfolding option.the_def by auto


    ML \<open>
      structure Datatype_Lens = struct

        type lens_info = {
          lens_t : term,
          def_thm : thm

        }

        fun morph_lens_info phi {lens_t, def_thm} =
          {lens_t = Morphism.term phi lens_t,
           def_thm = Morphism.thm phi def_thm}

        val dummify_atomic_types = Term.map_types (Term.map_atyps (K Term.dummyT));


        fun define_lens (cs : Ctr_Sugar.ctr_sugar) qualified i j lthy = let
          val ctors = #ctrs cs
          val namess = #selss cs |> map (map (dest_Const #> fst))

          fun mk_optionMT T = Type (@{type_name option}, [T])

          fun mk_return t = let
            val T = fastype_of t
            val rT = T --> mk_optionMT T
          in
            Const (@{const_name Some},rT) $ t
          end

          fun mk_abort T = let
            val rT = mk_optionMT T
          in
            Const (@{const_name None},rT)
          end

          fun mk_get ctxt ctor i = let
            val (Ts,_) = strip_type (fastype_of ctor)
            val (vs,_) = Variable.variant_fixes (map (K "x") Ts) ctxt
            val vs = map Free (vs ~~ Ts)
            val t = mk_return (nth vs i) |> fold lambda (rev vs)
          in
            t
          end

          fun mk_invcase ctxt T ctor = let
            val (Ts,_) = strip_type (fastype_of ctor)
            val (vs,_) = Variable.variant_fixes (map (K "x") Ts) ctxt
            val vs = map Free (vs ~~ Ts)
            val t = mk_abort T |> fold lambda (rev vs)
          in
            t
          end

          fun mk_put ctxt ctor pvn i = let
            val (Ts,_) = strip_type (fastype_of ctor)
            val (vs,_) = Variable.variant_fixes (map (K "x") Ts) ctxt
            val vsa = nth_map i (K pvn) vs
            val vs = map Free (vs ~~ Ts)
            val vsa = map Free (vsa ~~ Ts)
            val t = mk_return (list_comb (ctor,vsa)) |> fold lambda (rev vs)
          in
            t
          end

          fun mk_case ts = let
            val rT = body_type (fastype_of (hd ts))
            val cT = (map fastype_of ts) ---> #T cs --> rT

            val (cn,_) = dest_Const (#casex cs)
            val cc = Const (cn,cT)
            val r = list_comb (cc,ts)
          in
            r
          end

          fun mk_lens ctxt i j = let
            val ctor = nth ctors i
            val lname = nth (nth namess i) j
            val T = nth (binder_types (fastype_of ctor)) j

            (* Get *)
            val get =
                 map (mk_invcase ctxt T) ctors
              |> nth_map i (K (mk_get ctxt ctor j))
              |> mk_case

            (* Put *)
            val (pvn,ctxt) = yield_singleton Variable.variant_fixes "v" ctxt
            val pvT = nth (binder_types (fastype_of ctor)) j
            val pv = Free (pvn,pvT)

            val put =
                 map (mk_invcase ctxt (#T cs)) ctors
              |> nth_map i (K (mk_put ctxt ctor pvn j))
              |> mk_case
              |> lambda pv

            val lensT = Type (@{type_name lens},[T,#T cs])
            val lens = Const (@{const_name LENS}, fastype_of get --> fastype_of put --> lensT)
            val rhs_term = lens $ get $ put

            val lname = String.tokens (fn x => x = #".") lname |> rev
            val (qname,lname) = (hd (tl lname),hd lname)
            val lname = lname ^ "\<^sub>L"
            val lhs_term = Free (lname, fastype_of rhs_term)
            val def_term = Logic.mk_equals (lhs_term,rhs_term)
          in
            ((qname,lname),def_term)
          end

          val ((qname,lname),def_term) = mk_lens lthy i j

          val lname = Binding.name lname
          val lname = Binding.qualify qualified qname lname

          val (def_term,_) = yield_singleton (Variable.importT_terms) def_term lthy

          val ((lens_t,(_,def_thm)),lthy) = Specification.definition
            (SOME (lname,NONE,Mixfix.NoSyn)) [] [] ((Binding.empty,[]),def_term) lthy;


          val lens_prop =
              Const (@{const_name hlens}, fastype_of lens_t --> HOLogic.boolT) $ lens_t
            |> HOLogic.mk_Trueprop

          fun prove ctxt = let
            val ctxt = put_simpset HOL_ss ctxt
            val ctxt = ctxt
              addsimps @{thms hlens.is_lens LENS_downstage theMO_return domMO_return domMO_None}
              addsimps #injects cs
              addsimps #distincts cs
            val ctxt = Splitter.add_split (#split cs) ctxt
            val ctxt = Splitter.add_split (#split_asm cs) ctxt
          in
            Locale.intro_locales_tac true ctxt []
            THEN unfold_tac ctxt [def_thm]
            THEN ALLGOALS (asm_full_simp_tac ctxt)
          end

          val lens_thm = Goal.prove lthy [] [] lens_prop (fn {context, ...} => prove context)
          val lt_name = Binding.suffix_name "_lens" lname
          val (_,lthy) = Local_Theory.note ((lt_name,@{attributes [simp, intro!]}),[lens_thm]) lthy

          (* pre_get field\<^sub>L x = is_CTOR x *)

          val (vn,lthy) = yield_singleton Variable.variant_fixes "x" lthy
          val v = Free (vn,Term.dummyT)

          val has_proper_disc = case nth (#discs cs) i of
            Const _ => true | _ => false

          fun p_simp_tac ctxt = let
            val disc_thms = if has_proper_disc then nth (#disc_thmss cs) i else []
          in
            asm_simp_tac (put_simpset HOL_ss ctxt addsimps @{thms
                LENS_downstage option.sel option.simps the_None_undefined             
              } @ [def_thm] @ #case_thms cs @ disc_thms @ #sel_defs cs
            )
          end

          fun p_discsel_tac ctxt = Induct_Tacs.case_tac ctxt vn [] NONE 
                THEN_ALL_NEW p_simp_tac ctxt

          fun prove_define tac term suffix lthy = let
            val _ = Pretty.block [Pretty.str "Proving ", Binding.pretty lname, Pretty.str "_", Pretty.str suffix, Pretty.str ": ", Syntax.pretty_term lthy term]
              |> Pretty.string_of |> writeln

            val thm = Goal.prove lthy [] [] term (fn {context=ctxt,...} => ALLGOALS (tac ctxt))
  
            val name = Binding.suffix_name ("_"^suffix) lname
            val (_,lthy) = Local_Theory.note ((name,@{attributes [simp]}),[thm]) lthy
          in
            lthy
          end

          val lthy =
            if has_proper_disc then let
              val pgdisc_term = 
                HOLogic.mk_eq (
                  (@{const pre_get (_,_)} $ lens_t ) $ v,
                  nth (#discs cs) i $ v
                )
              |> HOLogic.mk_Trueprop
              |> dummify_atomic_types |> Syntax.check_term lthy
    
              val lthy = prove_define p_discsel_tac pgdisc_term "pre_disc" lthy
            in lthy end
            else if length (#ctrs cs) = 1 then let
              val pgdisc_term =                 
                HOLogic.mk_eq (
                    (@{const pre_get (_,_)} $ lens_t ) $ v,
                    @{const True}
                  )
                |> HOLogic.mk_Trueprop
                |> dummify_atomic_types |> Syntax.check_term lthy

              val lthy = prove_define p_discsel_tac pgdisc_term "pre_disc" lthy
            in lthy end
            else lthy

          val selget_term = 
            HOLogic.mk_eq (
              nth (nth (#selss cs) i) j $ v,
              (@{const get' (_,_)} $ lens_t ) $ v
            )
          |> HOLogic.mk_Trueprop
          |> dummify_atomic_types |> Syntax.check_term lthy

          val lthy = prove_define p_discsel_tac selget_term "sel_get'" lthy


          val ctor = nth (#ctrs cs) i
          val ctarity = fastype_of ctor |> binder_types |> length
          val (ctargs,lthy) = Variable.variant_fixes (replicate ctarity "x" ) lthy
            |>> map (fn x => Free (x, dummyT))

          val get_ctor_term = HOLogic.mk_eq (
            (@{const get' (_,_)} $ lens_t ) $ (list_comb (ctor,ctargs)),
            nth ctargs j)
          |> HOLogic.mk_Trueprop
          |> dummify_atomic_types |> Syntax.check_term lthy

          val lthy = prove_define p_simp_tac get_ctor_term "get_ctor" lthy

          val put_ctor_term = HOLogic.mk_eq (
            (@{const put' (_,_)} $ lens_t ) $ v $ (list_comb (ctor,ctargs)),
            list_comb (ctor,nth_map j (K v) ctargs))
          |> HOLogic.mk_Trueprop
          |> dummify_atomic_types |> Syntax.check_term lthy

          val lthy = prove_define p_simp_tac put_ctor_term "put_ctor" lthy

          val linfo : lens_info = {lens_t = lens_t, def_thm = def_thm}

        in
          (linfo,lthy)
        end

        fun define_lens' cs qual i j (def_thms,lthy) = let
          val (dt,lthy) = define_lens cs qual i j lthy
        in
          (dt :: def_thms,lthy)
        end

        fun define_all_lenses_aux cs qual lthy = let
          fun def_lens i (dtss,lthy) = let
            val ub = nth (#ctrs cs) i |> fastype_of |> binder_types |> length
            val (dts,lthy) = fold (fn j => define_lens' cs qual i j) (0 upto ub - 1) ([],lthy)
          in
            (dts::dtss,lthy)
          end
        in
          fold (fn i => def_lens i) (0 upto length (#ctrs cs) - 1) ([],lthy)
        end


        fun define_all_lenses tyname cs qual lthy = let
          val (lis,(lthy,lthy_old)) =
            Local_Theory.open_target lthy |> snd
            |> define_all_lenses_aux cs qual
            ||> `Local_Theory.close_target
          val phi = Proof_Context.export_morphism lthy_old lthy
          val lis = map (map (morph_lens_info phi)) lis

          (* Indep-lemmas *)
          fun prove_indep (li1 : lens_info, li2 : lens_info) ctxt = let
            val iterm = @{const "lens_indep" (_,_,_)} $ #lens_t li1 $ #lens_t li2
              |> HOLogic.mk_Trueprop
              |> dummify_atomic_types |> @{print}
              |> Syntax.check_term ctxt
              
            
            fun p_simp_tac ctxt = auto_tac (put_simpset HOL_ss ctxt 
              addsimps #def_thm li1 :: #def_thm li2 :: #distincts cs @ #injects cs 
                      @ @{thms LENS_downstage option.sel option.simps }
              |> Splitter.add_split (#split cs)
              |> Splitter.add_split (#split_asm cs))

            fun tac ctxt = 
              Locale.intro_locales_tac true ctxt [] THEN p_simp_tac ctxt

            val thm = Goal.prove ctxt [] [] iterm (fn {context=ctxt, ...} => tac ctxt)

          in
            thm
          end

          fun comp_indep_thms [] = []
            | comp_indep_thms (li::lis) = map (fn li2 => prove_indep (li,li2) lthy) lis @ comp_indep_thms lis

          val indep_thms = map comp_indep_thms lis |> flat

          val tyname' = String.tokens (fn x => x = #".") tyname |> rev |> hd

          val indeps_name = Binding.name "indeps" |> Binding.qualify true tyname' 

          val (_,lthy) = Local_Theory.note ((indeps_name,@{attributes [simp]}),indep_thms) lthy
        in
          lthy
        end

      end
    \<close>
    ML \<open>
      let
        val parse_qualified =
          Scan.optional (@{keyword "("} |-- (@{keyword open} >> K true) --| @{keyword ")"}) false
      in
        Outer_Syntax.local_theory
          @{command_keyword define_lenses}
          "Define lenses for datatype"
          (parse_qualified -- Parse.type_const
            >> (fn (qual, tyname) => fn lthy => let
              val tyname =
                  Proof_Context.read_type_name {proper=true, strict=false} lthy tyname
               |> dest_Type |> fst
              val cs = Ctr_Sugar.ctr_sugar_of lthy tyname
              val _ = is_none cs andalso error ("Not a datatype " ^ tyname)
              val cs = the cs
            in
              Datatype_Lens.define_all_lenses tyname cs qual lthy
            end)
          )
      end
    \<close>


  end


  (*abbreviation comp\<^sub>L_aux where "comp\<^sub>L_aux a b \<equiv> comp\<^sub>L b a"
  bundle forward_composition_syntax begin
    no_notation comp\<^sub>L (infixr ";\<^sub>L" 80)
    notation comp\<^sub>L_aux (infixl "\<bullet>\<^sub>L" 80)
  end
  *)


  (* Can be used to generate simp-lemma to unfold generated lenses. TODO: Generate clean simp-theorems! *)
  (*lemma lens_eq_unfolds:
    assumes "L \<equiv> LENS g p"
    shows "get L s = g s" "put L x s = p x s"
    using assms by auto
  *)

(*
xxx, ctd here:
lemmas "get (CTOR \<dots>) =" and "put x (CTOR \<dots>) = "
*)

  section \<open>Tests and Examples\<close>


(*
  pre_get the_mem\<^sub>L x = (x = x)
*)

  context begin

    private datatype 'a test =
      A (xcord: nat) (ycord: 'a)
    | B (name: string)
    | C bool bool int

    declare [[ML_print_depth = 100]]
    private define_lenses test
    print_theorems

    value [code] "put ycord\<^sub>L ''bar'' (A 3 ''foo'')"
    value [code] "put' ycord\<^sub>L ''bar'' (A 3 ''foo'')"
    value [code] "put ycord\<^sub>L ''bar'' (B ''foo'')"

  end


  (*
    Lemmas:

      sel_get': sel x = get' sel\<^sub>L x
      pre_disc: pre_sel\<^sub>L = is_C 
      indeps: Cx\<^sub>L \<bowtie> Cy\<^sub>L

  *)


end
