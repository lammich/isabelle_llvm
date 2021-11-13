theory Similar
imports LLVM_Shallow
begin

  definition sim_addr :: "(llvm_addr \<Rightarrow> llvm_addr) \<Rightarrow> _"
    where "sim_addr f a b \<longleftrightarrow> b = f a"

  fun sim_ptr where
    "sim_ptr f PTR_NULL PTR_NULL \<longleftrightarrow> True"
  | "sim_ptr f (PTR_ADDR a) (PTR_ADDR b) \<longleftrightarrow> sim_addr f a b"  
  | "sim_ptr f _ _ \<longleftrightarrow> False"  

  fun sim_val where
    "sim_val f (LL_STRUCT fs) (LL_STRUCT fs') \<longleftrightarrow> list_all2 (sim_val f) fs fs'"
  | "sim_val f (LL_INT a) (LL_INT b) \<longleftrightarrow> a=b"  
  | "sim_val f (LL_PTR a) (LL_PTR b) \<longleftrightarrow> sim_ptr f a b"
  | "sim_val _ _ _ = False"
  
  definition "sim_val' f a b \<equiv> sim_val f (to_val a) (to_val b)"
  
  definition sim_memory where
    "sim_memory f m\<^sub>1 m\<^sub>2 \<longleftrightarrow> (\<forall>a\<^sub>1. 
      f_valid_addr a\<^sub>1 m\<^sub>1 = f_valid_addr (f a\<^sub>1) m\<^sub>2      
    \<and> (f_valid_addr a\<^sub>1 m\<^sub>1 \<longrightarrow> f_load a\<^sub>1 m\<^sub>1 = f_load (f a\<^sub>1) m\<^sub>2)
      )"
  
  definition "sim_macc f a\<^sub>1 a\<^sub>2 \<equiv> 
    llvm_macc.reads a\<^sub>2 = f`llvm_macc.reads a\<^sub>1
  \<and> llvm_macc.writes a\<^sub>2 = f`llvm_macc.writes a\<^sub>1 
    "
  
  fun sim_result where
    "sim_result f (FAIL _) (FAIL _) = True"
  | "sim_result f (FAIL _) (NTERM) = True"
  | "sim_result f (NTERM) (FAIL _) = True"
  | "sim_result f (NTERM) (NTERM) = True"
  | "sim_result f (EXC e i s) (EXC e' i' s') = (sim_val' f e e' \<and> sim_macc f i i' \<and> sim_memory f s s')"
  | "sim_result f (SUCC x i s) (SUCC x' i' s') = (sim_val' f x x' \<and> sim_macc f i i' \<and> sim_memory f s s')"
  | "sim_result _ _ _ = False"
  
  definition "sim_m f m\<^sub>1 m\<^sub>2 \<equiv> \<forall>s\<^sub>1 s\<^sub>2. sim_memory f s\<^sub>1 s\<^sub>2 \<longrightarrow> sim_result f (run m\<^sub>1 s\<^sub>1) (run m\<^sub>2 s\<^sub>2)"
  
  definition "similar m\<^sub>1 m\<^sub>2 \<equiv> \<forall>f s\<^sub>1 s\<^sub>2. bij f \<and> sim_memory f s\<^sub>1 s\<^sub>2 
    \<longrightarrow> (\<exists>f'. bij f' \<and> sim_result f' (run m\<^sub>1 s\<^sub>1) (run m\<^sub>2 s\<^sub>2))"
  
  lemma "similar m m"
    oops

    
  lemma [simp]: "sim_macc f 0 0"  
    unfolding sim_macc_def zero_llvm_macc_def by simp
    
  lemma "sim_val' f x x' \<Longrightarrow> sim_m f (return x) (return x')"  
    unfolding sim_m_def by (simp add: run_simps)
    
  lemma sim_macc_add: "sim_macc f a a' \<Longrightarrow> sim_macc f b b' \<Longrightarrow> sim_macc f (a+b) (a'+b')"  
    by (auto simp: sim_macc_def plus_llvm_macc_def)
    
  lemma sim_result_add_intf: "sim_macc f i i' \<Longrightarrow> sim_result f r r' \<Longrightarrow> sim_result f (add_intf i r) (add_intf i' r')"  
    by (cases r; cases r'; simp add: sim_macc_add)
    
    
  lemma 
    fixes m m' :: "'a::llvm_rep llM"
    assumes "sim_m \<phi> m m'"
    assumes "\<And>x x' s s'. sim_val' \<phi> x x' \<Longrightarrow> sim_memory \<phi> s s' \<Longrightarrow> sim_m \<phi> (f x) (f' x')"
    shows "sim_m \<phi> (bind m f) (bind m' f')"
    oops: we need a rep for bind!
    
    
    using assms
    unfolding sim_m_def 
    apply (auto simp add: run_simps mwp_def split: mres.splits)
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply fastforce
    apply (rule sim_result_add_intf)
    apply fastforce
  proof goal_cases
    case (1 s\<^sub>1 x41 x42 x43 s\<^sub>2 x41a x42a x43a)
    from "1"(2)[OF _ "1"(5)]
    
    
    then show ?case sorry
  qed
    
    
  lemma "similar m m' \<Longrightarrow> similar (par E m m') (par E m' m)"  
    xxx, ctd here: proof also needs definition of well-formed
    
    

end
