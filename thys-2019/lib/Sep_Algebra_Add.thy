section \<open>Additions to Separation Algebra Library\<close>
theory Sep_Algebra_Add
imports "Separation_Algebra.Sep_Tactics"
begin

no_notation pred_K ("\<langle>_\<rangle>")
hide_const (open) Separation_Algebra.pure

subsection \<open>Simp-Lemmas for Separation Algebra\<close>

named_theorems sep_algebra_simps \<open>Advanced simplification lemmas for separation algebra\<close>

lemmas [sep_algebra_simps] = sep_conj_exists sep_add_ac
lemmas [simp] = sep_conj_assoc

lemmas sep_conj_c = sep_conj_commute sep_conj_left_commute

lemmas sep_conj_aci = sep_conj_ac sep_conj_empty sep_conj_empty'

subsection \<open>Separation Algebra with a Unique Zero\<close>

class unique_zero_sep_algebra = stronger_sep_algebra +
  assumes unique_zero: "x##x \<Longrightarrow> x=0"
begin
  lemma unique_zero_simps[simp]: 
    "a##a \<longleftrightarrow> a=0"
    "a##b \<Longrightarrow> a+b = a \<longleftrightarrow> b=0"
    "a##b \<Longrightarrow> a+b = b \<longleftrightarrow> a=0"
    "a##b \<Longrightarrow> a + b = 0 \<longleftrightarrow> a=0 \<and> b=0"
    apply -
    using local.sep_disj_zero local.unique_zero apply blast
    apply (metis local.sep_add_disjD local.sep_add_zero local.unique_zero)
    apply (metis local.sep_add_disjD local.sep_add_zero_sym local.sep_disj_commute local.unique_zero)
    by (metis local.sep_add_disjD local.sep_add_zero local.sep_disj_zero local.unique_zero)

end

subsection \<open>Standard Instantiations\<close>

instantiation "fun" :: (type,stronger_sep_algebra) stronger_sep_algebra
begin
  definition "f1 ## f2 \<longleftrightarrow> (\<forall>x. f1 x ## f2 x)"
  definition [simp]: "(f1 + f2) x = (f1 x + f2 x)"
  definition [simp]: "0 x \<equiv> 0"

  instance
    apply standard
    unfolding sep_disj_fun_def plus_fun_def zero_fun_def
    apply (auto)
    subgoal
      by (simp add: sep_disj_commute)
    subgoal
      using sep_add_commute by auto
    subgoal 
      by (simp add: sep_add_assoc) 
    (*subgoal 
      using sep_disj_addD1 by blast 
    subgoal 
      by (simp add: sep_disj_addI1) 
    *)
    done  
  
end

instance "fun" :: (type,unique_zero_sep_algebra) unique_zero_sep_algebra
  apply standard
  unfolding sep_disj_fun_def plus_fun_def zero_fun_def
  by (metis unique_zero)
  
lemma disj_fun_upd_iff[simp]: 
  "\<lbrakk>f a = 0; g a = 0\<rbrakk> \<Longrightarrow> (f(a:=x) ## g(a:=y)) \<longleftrightarrow> (f ## g \<and> x ## y)"
  unfolding sep_disj_fun_def by force

lemma fun_upd_Z_Z[simp]: "fun_upd 0 i 0 = 0" by auto

lemma sep_disj_fun_updI[sep_algebra_simps, intro]: "\<lbrakk>f##g; a##b\<rbrakk> \<Longrightarrow> f(x:=a) ## g(x:=b)"
  by (simp add: sep_disj_fun_def)
    
lemma sep_disj_fun_Zupd_eq[sep_algebra_simps]: 
  "f##0(x:=y) \<longleftrightarrow> f x ## y" 
  "0(x:=y) ## f \<longleftrightarrow> y ## f x" 
  by (auto simp add: sep_disj_fun_def)
  
  
lemma sep_disj_funD: "f##g \<Longrightarrow> f x ## g x" by (auto simp: sep_disj_fun_def) 

lemma merge_fun_singleton: "fun_upd 0 i a + fun_upd 0 i b = fun_upd 0 i (a+b)" by auto

lemma split_fun_upd_0: "fun_upd (a+b) i 0 = fun_upd a i 0 + fun_upd b i 0" by auto
  

instantiation option :: (stronger_sep_algebra) stronger_sep_algebra begin

  fun sep_disj_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
    "sep_disj None None \<longleftrightarrow> True"
  | "sep_disj None (Some _) \<longleftrightarrow> True"  
  | "sep_disj (Some _) None \<longleftrightarrow> True"
  | "sep_disj (Some x) (Some y) \<longleftrightarrow> x##y"

  lemma sep_disj_option_add_simps[simp]: 
    "sep_disj None x" 
    "sep_disj x None" 
    by (cases x; simp)+
        
  fun plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where 
    "plus None None = None"
  | "plus None (Some x) = Some x"
  | "plus (Some x) None = Some x" 
  | "plus (Some x) (Some y) = Some (x+y)"

  lemma plus_option_add_simps[simp]: "plus None x = x" "plus x None = x"
    by (cases x; simp)+
  
  definition "0 = None"
    
  instance 
    apply standard
    apply (simp_all add: zero_option_def)
    apply (case_tac x; case_tac y; simp add: sep_disj_commute)
    apply (case_tac x; case_tac y; auto simp add: sep_disj_commute sep_add_commute)
    apply (case_tac x; case_tac y; case_tac z; simp add: sep_add_assoc)
    apply (case_tac x; case_tac y; case_tac z; auto dest: sep_disj_addD1)
    (*apply (case_tac x; case_tac y; case_tac z; auto dest: sep_disj_addI1)*)
    done    
  
end


instantiation prod :: (stronger_sep_algebra, stronger_sep_algebra) stronger_sep_algebra
begin
  definition "a##b \<longleftrightarrow> fst a ## fst b \<and> snd a ## snd b"
  definition "a+b = (fst a + fst b, snd a + snd b)"  
  definition "0 = (0,0)"
  
  instance
    apply standard
    unfolding sep_disj_prod_def plus_prod_def zero_prod_def
    by (auto 
      simp: sep_add_ac 
      intro: sep_disj_commuteI sep_disj_addD1 sep_disj_addI1)
end

lemma sep_disj_prod_lower[sep_algebra_simps]: "(a,b) ## (c,d) \<longleftrightarrow> a##c \<and> b##d"
  by (simp add: sep_disj_prod_def)
  
lemma plus_prod_lower[sep_algebra_simps]: "(a,b) + (c,d) = (a+c,b+d)"
  by (simp add: plus_prod_def)

instance prod :: (unique_zero_sep_algebra,unique_zero_sep_algebra) unique_zero_sep_algebra
  by standard (auto simp: zero_prod_def sep_algebra_simps)

lemma prod_Z_lower[sep_algebra_simps]: 
  "(a,b) = 0 \<longleftrightarrow> a=0 \<and> b=0"
  "0 = (a,b) \<longleftrightarrow> a=0 \<and> b=0"
  by (auto simp: zero_prod_def)

lemma plus_prod_eqI: "(a+b,c+d) = (a,c) + (b,d)" by (simp add: sep_algebra_simps)
      
lemma fst_Z[simp]: "fst 0 = 0" by (simp add: zero_prod_def)
lemma snd_Z[simp]: "snd 0 = 0" by (simp add: zero_prod_def)

lemma fst_plus[sep_algebra_simps]: "fst (a+b) = fst a + fst b" by (auto simp: plus_prod_def)
lemma snd_plus[sep_algebra_simps]: "snd (a+b) = snd a + snd b" by (auto simp: plus_prod_def)
lemma disj_fstI[sep_algebra_simps]: "a##b \<Longrightarrow> fst a ## fst b" by (auto simp: sep_disj_prod_def)
lemma disj_sndI[sep_algebra_simps]: "a##b \<Longrightarrow> snd a ## snd b" by (auto simp: sep_disj_prod_def)


datatype 'a tsa_opt = ZERO | TRIV (the_tsa: 'a)

instantiation tsa_opt :: (type) unique_zero_sep_algebra begin
  definition sep_disj_tsa_opt :: "'a tsa_opt \<Rightarrow> 'a tsa_opt \<Rightarrow> bool" 
    where "a##b \<longleftrightarrow> a=ZERO \<or> b=ZERO"

  definition "a+b \<equiv> (case (a,b) of (ZERO,x) \<Rightarrow> x | (x,ZERO) \<Rightarrow> x)"
  definition "0 = ZERO"

  instance
    apply standard
    by (auto simp: zero_tsa_opt_def sep_disj_tsa_opt_def plus_tsa_opt_def split: tsa_opt.splits)
  
end
  
instance tsa_opt :: (type) cancellative_sep_algebra
  apply standard
  by (auto simp: zero_tsa_opt_def sep_disj_tsa_opt_def plus_tsa_opt_def split: tsa_opt.splits)
  

(* Lowering lemmas. If one side of operation breaks abstraction level, 
  the other side is also lowered
*)  
lemma TRIV_not_zero[simp]: "TRIV x \<noteq> 0" "0\<noteq>TRIV x" by (auto simp: zero_tsa_opt_def)
lemma TRIV_Z_lower[intro!]: 
  "ZERO = 0" 
  "0 = ZERO" 
  by (auto simp: zero_tsa_opt_def)  
  
lemma triv_Z_lower2[sep_algebra_simps]:  
  "x + ZERO = x"
  "ZERO + x = x"
  by (auto simp: zero_tsa_opt_def plus_tsa_opt_def split: tsa_opt.splits)  
  
lemma TRIV_disj_simps[sep_algebra_simps]:
  "TRIV a ## b \<longleftrightarrow> b=ZERO"
  "b ## TRIV a \<longleftrightarrow> b=ZERO"
  by (auto simp: sep_disj_tsa_opt_def)
  
subsection \<open>Additional Simplifier Setup\<close>

(* 
  This may cause trouble on non-eta-normalized terms.
    (\<lambda>s. \<box> s) \<rightarrow> \<lambda>s. s=0
  The next lemma hopefully fixes that.
*)    

lemma sep_empty_app[sep_algebra_simps]: "\<box> h \<longleftrightarrow> h=0"
  by (simp add: sep_empty_def)

lemma sep_empty_I[sep_algebra_simps]: "(\<lambda>h. h=0) = \<box>"
  by (simp add: sep_empty_def)
  
lemma sep_triv_ineqs[simp]: 
  "\<box> \<noteq> sep_false"  
  "sep_true \<noteq> sep_false"  
  "sep_false \<noteq> \<box>"  
  "sep_false \<noteq> sep_true"  
  by (auto dest: fun_cong)
  
lemma sep_true_not_empty:
  assumes "(a::'a::sep_algebra) \<noteq> (b::'a)"  
  shows "(\<box>::'a\<Rightarrow>bool) \<noteq> sep_true"  
  by (metis (mono_tags, lifting) assms sep_empty_I)
  
  
subsection \<open>Pure Assertions\<close>

text \<open>The Separation Algebra entry only defines @{term "pred_K \<Phi>"}, which
  makes no constraint on the heap. We define \<open>\<up>\<Phi>\<close>, which requires an empty heap, 
  and is more natural when using separation logic with deallocation.
\<close>      

definition pred_lift :: "bool \<Rightarrow> 'a::sep_algebra \<Rightarrow> bool" ("\<up>_" [100] 100)
  where "(\<up>\<Phi>) s \<equiv> \<Phi> \<and> \<box> s"

text \<open>Relation between \<open>pred_lift\<close> and \<open>pred_K\<close>. Warning, do not use 
  as simp-lemma, as \<open>sep_true\<close> is an abbreviation for \<open>\<langle>True\<rangle>\<close>\<close>  
lemma "pred_K \<Phi> = (\<up>\<Phi> ** sep_true)" by (auto simp: pred_lift_def sep_conj_def sep_algebra_simps) 
  
lemma pred_lift_move_front_simps[sep_algebra_simps]:
  "(\<up>\<Phi> ** \<up>\<Psi>) = (\<up>(\<Phi>\<and>\<Psi>))"
  "(\<up>\<Phi> ** \<up>\<Psi> ** B) = (\<up>(\<Phi>\<and>\<Psi>) ** B)"
  "NO_MATCH (\<up>X) A \<Longrightarrow> (A ** \<up>\<Phi> ** B) = (\<up>\<Phi> ** A ** B)"
  "NO_MATCH (\<up>X) A \<Longrightarrow> (A ** \<up>\<Phi>) = (\<up>\<Phi> ** A)"
  by (auto simp: pred_lift_def sep_conj_def sep_algebra_simps)
  
lemma pred_lift_extract_simps:
  "(\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> h=0"
  "(\<up>\<Phi> ** A) h \<longleftrightarrow> \<Phi> \<and> A h"
  by (auto simp: pred_lift_def sep_conj_def sep_algebra_simps)
  
lemma pure_true_conv[sep_algebra_simps]: "\<up>True = \<box>" by (auto simp: sep_algebra_simps pred_lift_extract_simps)

lemma pred_lift_false_conv[simp]: "\<up>False = sep_false" by (auto simp: sep_algebra_simps pred_lift_extract_simps)

lemma pure_assn_eq_conv[simp]: "(\<up>\<Phi>) = (\<up>\<Psi>) \<longleftrightarrow> \<Phi>=\<Psi>"
  by (smt pred_lift_extract_simps(1))

lemmas sep_conj_false_simps =
  pred_lift_false_conv
  sep_conj_false_left sep_conj_false_right

definition sep_is_pure_assn :: "('a::sep_algebra \<Rightarrow> bool) \<Rightarrow> bool" where
  "sep_is_pure_assn A \<equiv> \<forall>s. A s \<longrightarrow> s=0"

definition pure_part :: "('a::sep_algebra \<Rightarrow> bool) \<Rightarrow> bool" where
  "pure_part A \<equiv> Ex A"

lemma pure_partI: "A s \<Longrightarrow> pure_part A" by (auto simp: pure_part_def)
  
lemma pure_part_pure_eq[simp]: "sep_is_pure_assn A \<Longrightarrow> \<up>pure_part A = A"
  apply (rule ext)
  by (auto simp: sep_is_pure_assn_def pure_part_def pred_lift_def sep_algebra_simps)

  
lemma pure_part_triv_simps[simp]: 
  "\<not>pure_part sep_false"
  "pure_part \<box>"
  by (auto simp: pure_part_def)

    
lemma pure_part_pure[simp]: "pure_part (\<up>\<Phi>) = \<Phi>"  
  by (auto simp: pure_part_def sep_algebra_simps pred_lift_def)
  
lemma pure_part_split_conj: "pure_part (A**B) \<Longrightarrow> pure_part A \<and> pure_part B"  
  by (auto simp: pure_part_def sep_conj_def)
  
lemma sep_is_pure_lift_pred[simp]: "sep_is_pure_assn (\<up>\<Phi>)"  
  by (auto simp: sep_is_pure_assn_def pred_lift_def sep_algebra_simps)
  
lemma sep_is_pure_assn_false[simp]: "sep_is_pure_assn sep_false" by (auto simp: sep_is_pure_assn_def)
lemma sep_is_pure_assn_empty[simp]: "sep_is_pure_assn \<box>" by (auto simp: sep_is_pure_assn_def sep_algebra_simps)

lemma sep_is_pure_assn_conjI: "sep_is_pure_assn A \<Longrightarrow> sep_is_pure_assn B \<Longrightarrow> sep_is_pure_assn (A**B)"
  by (auto simp: sep_is_pure_assn_def sep_conj_def)

lemma pure_part_pure_conj_eq: "pure_part (\<up>P ** Q) \<longleftrightarrow> P \<and> pure_part Q"    
  unfolding pure_part_def by (auto simp: sep_algebra_simps pred_lift_extract_simps)

  
  
subsection \<open>Exact Assertion\<close>
  
definition EXACT :: "'a::sep_algebra \<Rightarrow> 'a \<Rightarrow> bool" where [simp]: "EXACT h h' \<equiv> h'=h"
lemma strictly_exact_EXACT[simp]: "strictly_exact (EXACT h)"
  unfolding EXACT_def by (auto intro: strictly_exactI)

lemma EXACT_split: "a##b \<Longrightarrow> EXACT (a+b) = (EXACT a ** EXACT b)"
  unfolding EXACT_def sep_conj_def by auto

lemma EXACT_zero[simp]: "EXACT 0 = \<box>" by (auto simp: sep_algebra_simps)

lemma EXACT_eq_iff[simp]: "EXACT a = EXACT b \<longleftrightarrow> a=b"
  unfolding EXACT_def by metis
  
subsection \<open>List-Sum over Separation Algebra\<close>  
  
(* TODO: Move. Clean up *)

definition "sepsum_list l \<equiv> foldr (+) l (0::_::stronger_sep_algebra)"

lemma sepsum_list_simps[simp]:
  "sepsum_list [] = 0"
  "sepsum_list (x#xs) = x + sepsum_list xs"
  by (auto simp: sepsum_list_def)

context begin
  
private named_theorems ss

private definition "sep_ldisj1 x ys \<equiv> \<forall>y\<in>List.set ys. x##y"

private lemma sep_ldisj1_simps[ss]:
  "sep_ldisj1 x []"
  "sep_ldisj1 x (y#ys) \<longleftrightarrow> x##y \<and> sep_ldisj1 x ys"
  by (auto simp: sep_ldisj1_def)

private lemma sep_ldisj1_append[ss]: "sep_ldisj1 x (ys\<^sub>1@ys\<^sub>2) \<longleftrightarrow> sep_ldisj1 x ys\<^sub>1 \<and> sep_ldisj1 x ys\<^sub>2"
  by (induction ys\<^sub>1) (auto simp: ss)
    
private definition "sep_ldisj xs ys \<equiv> \<forall>x\<in>List.set xs. sep_ldisj1 x ys"

private lemma sep_ldisj_simps[ss]:
  "sep_ldisj [] ys"
  "sep_ldisj xs []"
  "sep_ldisj (x#xs) ys \<longleftrightarrow> sep_ldisj1 x ys \<and> sep_ldisj xs ys"
  "sep_ldisj xs (y#ys) \<longleftrightarrow> sep_ldisj1 y xs \<and> sep_ldisj xs ys"
  by (auto simp: sep_ldisj_def sep_ldisj1_def sep_algebra_simps)

private lemma sep_ldisj_append1[ss]: "sep_ldisj (xs\<^sub>1@xs\<^sub>2) ys \<longleftrightarrow> sep_ldisj xs\<^sub>1 ys \<and> sep_ldisj xs\<^sub>2 ys"
  by (induction xs\<^sub>1) (auto simp: ss)
  
private lemma sep_ldisj_append2[ss]: "sep_ldisj xs (ys\<^sub>1@ys\<^sub>2) \<longleftrightarrow> sep_ldisj xs ys\<^sub>1 \<and> sep_ldisj xs ys\<^sub>2"
  by (induction ys\<^sub>1) (auto simp: ss)

private lemma sep_ldisj_commute[sep_algebra_simps]: "sep_ldisj xs ys \<longleftrightarrow> sep_ldisj ys xs"
  by (force simp: sep_ldisj_def sep_ldisj1_def sep_algebra_simps)
    
fun sep_distinct :: "_::stronger_sep_algebra list \<Rightarrow> bool" where
  "sep_distinct [] \<longleftrightarrow> True"  
| "sep_distinct (x#xs) \<longleftrightarrow> sep_ldisj1 x xs \<and> sep_distinct xs"  

declare sep_distinct.simps[simp del, ss add]

private lemma sep_distinct_append_aux[ss]: 
  "sep_distinct (xs@ys) \<longleftrightarrow> sep_distinct xs \<and> sep_distinct ys \<and> sep_ldisj xs ys"
  by (induction xs) (auto simp: ss)

private lemma norm_ldisj1[ss]: "sep_distinct ys \<Longrightarrow> sep_ldisj1 x ys \<longleftrightarrow> x ## sepsum_list ys"  
  by (induction ys arbitrary: x) (auto simp: ss)
  
private lemma norm_ldisj[ss]: "sep_distinct xs \<Longrightarrow> sep_distinct ys \<Longrightarrow> sep_ldisj xs ys \<longleftrightarrow> sepsum_list xs ## sepsum_list ys"  
  by (induction xs) (auto simp: ss)
  
lemma sep_distinct_append[simp]: 
  "sep_distinct (xs@ys) \<longleftrightarrow> sep_distinct xs \<and> sep_distinct ys \<and> sepsum_list xs ## sepsum_list ys"  
  by (auto simp: ss)
  
lemma sepsum_append[simp]: "sep_distinct (xs@ys) \<Longrightarrow> sepsum_list (xs@ys) = sepsum_list xs + sepsum_list ys"
  by (induction xs) (auto simp: sep_algebra_simps ss)

lemma sep_distinct_simps[simp]:  
  "sep_distinct []"
  "sep_distinct (x#xs) \<longleftrightarrow> x ## sepsum_list xs \<and> sep_distinct xs"
  by (auto simp: ss)
  
  
end  
  
subsection \<open>Finite Assertion Families\<close>
interpretation sep_folding: folding "\<lambda>i Q. P i ** Q" \<box> for P
  apply unfold_locales
  apply (intro ext) 
  apply (simp add: sep.add_ac)
  done
  
definition "sep_set_img S P \<equiv> \<up>(finite S) ** sep_folding.F P S"
  
syntax
  "_SEP_SET_IMG"      :: "pttrn => 'a set => ('b \<Rightarrow> bool) => ('b \<Rightarrow> bool)"  ("(3\<Union>*_\<in>_./ _)" [0, 0, 10] 10)

translations 
  "\<Union>*x\<in>A. B"   \<rightleftharpoons> "CONST sep_set_img A (\<lambda>x. B)"
  
print_translation \<open>
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax sep_set_img} @{syntax_const "_SEP_SET_IMG"}]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>
  
lemma sep_set_img_infinite[simp]: "infinite I \<Longrightarrow> sep_set_img I P = sep_false"
  unfolding sep_set_img_def by auto




lemma sep_set_img_empty[simp]: "sep_set_img {} P = \<box>"
  and sep_set_img_insert_remove: "sep_set_img (insert x S) P = (P x ** sep_set_img (S-{x}) P)"
  and sep_set_img_insert[simp]: "x\<notin>S \<Longrightarrow> sep_set_img (insert x S) P = (P x ** sep_set_img S P)"
  and sep_set_img_remove: "x\<in>S \<Longrightarrow> sep_set_img S P = (P x ** sep_set_img (S-{x}) P)"
  by (auto 
    simp: sep_set_img_def sep_algebra_simps pred_lift_extract_simps sep_folding.insert_remove sep_folding.remove 
    del: ext intro!: ext)
    
lemma sep_set_img_cong:
  assumes [simp]: "I=I'"
  assumes P: "\<And>x. finite I' \<Longrightarrow> x\<in>I' \<Longrightarrow> P x = P' x"
  shows "sep_set_img I P = sep_set_img I' P'"
proof -
  {
    assume "finite I'"
    then have "sep_set_img I' P = sep_set_img I' P'" using P
      by induction auto
  }
  then show ?thesis by (cases "finite I'") auto
qed  
    
lemma sep_set_img_cong_strong[cong]:
  assumes [simp]: "I=I'"
  assumes P: "\<And>x. finite I' =simp=> x\<in>I' =simp=> P x = P' x"
  shows "sep_set_img I P = sep_set_img I' P'"
  using assms
  unfolding simp_implies_def
  by (rule sep_set_img_cong)
    
lemma sep_set_img_union[simp]:
  assumes "S\<^sub>1\<inter>S\<^sub>2={}"
  shows "sep_set_img (S\<^sub>1\<union>S\<^sub>2) P = (sep_set_img S\<^sub>1 P ** sep_set_img S\<^sub>2 P)"
proof -
  {
    assume "finite S\<^sub>1" 
    then have ?thesis using assms
      by (induction S\<^sub>1) auto
  }
  then show ?thesis by (cases "finite S\<^sub>1") auto
    
qed  

lemmas sep_set_img_ins[simp] = sep_set_img_union[where S\<^sub>1="{i}", simplified] for i


lemma sep_set_img_unionI':
  assumes NDUP: "\<And>x. \<lbrakk>x\<in>S\<^sub>2 \<rbrakk> \<Longrightarrow> (P x ** P x) = sep_false"
  assumes P: "(sep_set_img S\<^sub>1 P ** sep_set_img S\<^sub>2 P) s"
  shows "sep_set_img (S\<^sub>1\<union>S\<^sub>2) P s"
proof -

  have A: "(P x ** P x ** F) = sep_false" if "x\<in>S\<^sub>2" for x F
    using assms
    by (simp add: sep.mult_commute sep_conj_left_commute that)

  {
    assume "finite S\<^sub>1" 
    then have "?thesis" using P
    proof (induction S\<^sub>1 arbitrary: s)
      case empty
      then show ?case by simp
    next
      case (insert x S\<^sub>1)
      then show ?case 
        apply (cases "x\<notin>S\<^sub>2")
        apply (auto simp: sep_set_img_remove sep_set_img_insert_remove sep_algebra_simps sep_conj_impl)
        by (simp add: A sep_conj_left_commute) 
    qed
  }
  then show ?thesis using P by (cases "finite S\<^sub>1") auto
qed

lemma sep_set_img_pull_EXS: "(\<Union>*x\<in>I. EXS y. f x y) = (EXS Y. \<Union>*x\<in>I. f x (Y x))"
proof -
  {
    assume "finite I"
    then have ?thesis
      apply (induction I)
      apply simp
      apply (rule ext)
      apply (clarsimp simp: sep_algebra_simps; safe)
      subgoal for x F s xa xb
        apply (rule exI[where x="xb(x:=xa)"])
        apply auto
        by (smt sep_set_img_cong)
      subgoal by auto  
      done
  }
  then show ?thesis by (cases "finite I") auto
qed  

lemma list_conj_eq_sep_set_img: "distinct xs \<Longrightarrow> (\<And>*map P xs) = sep_set_img (List.set xs) P"  
  by (induction xs) auto


lemma sep_is_pure_assn_imgI:
  assumes "\<And>i. i\<in>I \<Longrightarrow> sep_is_pure_assn (f i)" 
  shows "sep_is_pure_assn (\<Union>*i\<in>I. f i)"
proof (cases "finite I")
  assume "finite I"
  then show ?thesis using assms
    by (induction I) (auto simp: sep_is_pure_assn_conjI)
qed simp
  
  
end
