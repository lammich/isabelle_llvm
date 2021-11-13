theory LLVM_Simple_Memory_RS
imports "../basic/kernel/Simple_Memory" "Sep_Generic_Wp"
begin

  (* TODO: Move *)  
  lemma pure_part_exact[simp, intro!]: "pure_part (EXACT x)"  
    unfolding pure_part_def EXACT_def by blast
    
  
  subsection \<open>Abstract Memory Separation Algebra\<close>

  typedef 'a amemory = "UNIV :: ((llvm_addr \<Rightarrow> 'a tsa_opt) \<times> (nat \<Rightarrow> nat tsa_opt)) set" by simp

  setup_lifting type_definition_amemory
  
  instantiation amemory :: (type) unique_zero_sep_algebra
  begin

    lift_definition sep_disj_amemory :: "'a amemory \<Rightarrow> 'a amemory \<Rightarrow> bool" is
      "\<lambda>a b. a ## b" .
      
    lift_definition plus_amemory :: "'a amemory \<Rightarrow> 'a amemory \<Rightarrow> 'a amemory" is
      "\<lambda>a b. a + b" .

    lift_definition zero_amemory :: "'a amemory" is "0" .  
  
    instance
      apply (standard; transfer)
      apply (simp_all add: sep_algebra_simps)
      done
  
  end

  type_synonym llvm_amemory = "llvm_val amemory"
  translations (type) "llvm_amemory" \<leftharpoondown> (type) "llvm_val amemory"
  
  subsubsection \<open>Instantiation of generic-sep-logic locale\<close>
  
  definition "llvm_\<alpha>m m a \<equiv> if f_valid_addr a m then TRIV (f_load a m) else 0"
  definition "llvm_\<alpha>b m b \<equiv> if f_valid_block b m then TRIV (f_block_size b m) else 0"
  
  lift_definition llvm_\<alpha> :: "'a memory \<Rightarrow> 'a amemory" is "\<lambda>m. (llvm_\<alpha>m m, llvm_\<alpha>b m)" .
  
  lift_definition amemory_addrs :: "'a amemory \<Rightarrow> llvm_addr set" is "\<lambda>(m,b). {a. m a \<noteq> 0}" .
  
  definition "llvm_macc_touches i \<equiv> llvm_macc.reads i \<union> llvm_macc.writes i"
  lemma llvm_macc_touches_simp[simp]: "llvm_macc_touches (MACC r w) = r\<union>w"
    by (simp add: llvm_macc_touches_def)

  definition "f_valid_addrs m \<equiv> {a. f_valid_addr a m}"
  definition "f_freed_addrs m \<equiv> {ADDR b i | b i. f_freed_block b m}"
  
  interpretation generic_sep_logic 
    f_valid_addrs 
    f_freed_addrs
    llvm_\<alpha>
    amemory_addrs
    llvm_macc_touches
    apply unfold_locales
    subgoal unfolding f_valid_addrs_def f_freed_addrs_def by auto 
    subgoal unfolding f_valid_addrs_def apply transfer apply (auto simp: llvm_\<alpha>m_def) done
    subgoal apply transfer apply (auto simp: sep_algebra_simps sep_disj_fun_def sep_disj_tsa_opt_def simp flip: zero_tsa_opt_def) done
    subgoal 
      apply transfer 
      apply (auto simp: sep_algebra_simps sep_disj_fun_def simp flip: zero_tsa_opt_def)
      done
    subgoal
      by (simp add: llvm_macc_touches_def zero_llvm_macc_def)
    subgoal
      by (auto simp add: llvm_macc_touches_def plus_llvm_macc_def)
    subgoal
      by (auto simp add: llvm_macc_touches_def nointer_llvm_macc_def)
    done

  (* For presentation in paper *)  
  
  lemma new_mem_dj_freed: "new_mem s s' \<inter> f_freed_addrs s = {}"
    unfolding new_mem_def used_mem_def by blast
  
  lemma wpa_alt_for_paper: "wpa A c Q s = wp c (\<lambda>r i s'.
          Q r s' \<comment> \<open>Postcondition satisfied\<close>
        \<and> llvm_macc_touches i \<subseteq> f_valid_addrs s \<union> new_mem s s' \<and> valid_trans s s' \<comment> \<open>well-formed\<close>
        \<and> llvm_macc_touches i \<inter> A = {} \<comment> \<open>access no addresses in \<open>A\<close>\<close>
     ) s"
    unfolding wpa_def
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    apply (intro ext)
    using alloc_free_dj[of s] new_mem_dj_freed[of s]
    apply auto
    done
  
    
    
  subsection \<open>Basic Hoare Rules\<close>    

  subsubsection \<open>Points-to and block assertions\<close>
      
  lift_definition llvm_ato :: "'a \<Rightarrow> llvm_addr \<Rightarrow> 'a amemory" is "\<lambda>v a. (0(a:=TRIV v),0)" .
  
  lemma amemory_addrs_pto[simp]: "amemory_addrs (llvm_ato x a) = {a}"
    by transfer simp
    
  lemma f_valid_addr_\<alpha>m: "f_valid_addr a m \<longleftrightarrow> llvm_\<alpha>m m a \<noteq> ZERO"  
    by (auto simp: llvm_\<alpha>m_def)
    
  lemma f_load_\<alpha>m: "llvm_\<alpha>m m a = TRIV x \<Longrightarrow> f_load a m = x"  
    by (auto simp: llvm_\<alpha>m_def split: if_splits)
    

  lemma f_valid_addr_\<alpha>: "\<lbrakk>llvm_ato x a ## asf; llvm_\<alpha> s = llvm_ato x a + asf\<rbrakk> 
    \<Longrightarrow> f_valid_addr a s \<and> f_load a s = x"
    apply transfer
    apply (clarsimp simp: sep_algebra_simps f_valid_addr_\<alpha>m f_load_\<alpha>m)
    done

  lemma f_valid_djD: "\<lbrakk> as ## asf; llvm_\<alpha> s = as + asf \<rbrakk> 
    \<Longrightarrow> amemory_addrs as \<inter> amemory_addrs asf = {} \<and> amemory_addrs as \<inter> f_freed_addrs s = {}"  
    apply rule
    apply (meson addr_dj)
    by (metis Int_assoc Int_empty_right Un_Int_eq(3) addr_add addr_cover alloc_free_dj)
    
    
  subsubsection \<open>Load\<close>    

  (* TODO: Move *)
  lemma STATE_exact_iff: 
    "STATE asf (EXACT as) s \<longleftrightarrow> as ## asf \<and> llvm_\<alpha> s = as + asf"
    by (simp add: STATE_def sep_algebra_simps)
  
        
  lemma llvmt_load_rule[vcg_rules]: "htriple (EXACT (llvm_ato x a)) (llvmt_load a) (\<lambda>r. \<up>(r=x) ** EXACT (llvm_ato x a))"  
    unfolding llvmt_load_def llvmt_check_addr_def
    apply rule
    apply vcg defer
    apply vcg
    apply (auto 0 3 simp: STATE_exact_iff f_valid_addrs_def f_valid_addr_\<alpha> dest: f_valid_djD)
    done
    
  subsubsection \<open>Store\<close>    
    
    
  lemma f_store_valid_trans: "f_valid_addr a s \<Longrightarrow> valid_trans s (f_store a x' s)"  
    unfolding valid_trans_def f_valid_addrs_def f_freed_addrs_def
    by auto
    
  lemma f_store_\<alpha>b: "f_valid_addr a s \<Longrightarrow> llvm_\<alpha>b (f_store a x' s) = llvm_\<alpha>b s"
    unfolding llvm_\<alpha>b_def
    by (auto simp: fun_eq_iff)
    
  lemma f_store_\<alpha>m: "\<lbrakk>asf a = 0; llvm_\<alpha>m s = 0(a := TRIV x) + asf\<rbrakk> \<Longrightarrow> llvm_\<alpha>m (f_store a x' s) = 0(a := TRIV x') + asf"  
    apply (rule ext)
    subgoal for a'
      apply (frule fun_cong[where x=a'])
      apply (drule fun_cong[where x=a])
      unfolding llvm_\<alpha>m_def
      by (auto split: if_splits) 
    done      
    
    
  lemma f_store_\<alpha>: "\<lbrakk>llvm_ato x a ## asf; llvm_\<alpha> s = llvm_ato x a + asf\<rbrakk>
       \<Longrightarrow> llvm_ato x' a ## asf \<and> llvm_\<alpha> (f_store a x' s) = llvm_ato x' a + asf"
    apply transfer
    apply (clarsimp simp: sep_algebra_simps f_valid_addr_\<alpha>m f_store_\<alpha>b f_store_\<alpha>m simp flip: zero_tsa_opt_def)
    done

  (* TODO: Move *)  
  method vcg_all = (vcg, defer_tac)+
        
  lemma store_freed_addrs[simp]: "f_valid_addr a s \<Longrightarrow> f_freed_addrs (f_store a x' s) = f_freed_addrs s"
    by (simp add: f_freed_addrs_def)
  
  find_theorems "llvm_ato _ _ ## _"  
    
  
  lemma llvmt_store_rule[vcg_rules]: "llvm_struct_of_val x' = llvm_struct_of_val x 
    \<Longrightarrow> htriple (EXACT (llvm_ato x a)) (llvmt_store x' a) (\<lambda>_. EXACT (llvm_ato x' a))"  
    unfolding llvmt_store_def llvmt_load_def llvmt_check_addr_def
    
    apply (vcg_all)
    apply (auto 0 3
      simp: STATE_exact_iff POSTCOND_def f_valid_addr_\<alpha> 
            sep_algebra_simps f_store_valid_trans f_store_\<alpha>
      dest: f_valid_djD) 
      
    subgoal by (metis f_store_\<alpha> sep_add_commute sep_disj_commute)
    subgoal by (metis (no_types, lifting) IntI Un_iff addr_add addr_cover alloc_free_dj amemory_addrs_pto empty_iff insertCI)
    subgoal by (metis UnCI addr_add addr_cover amemory_addrs_pto insertCI)
    subgoal by (metis (no_types, lifting) IntI Un_iff addr_add addr_cover alloc_free_dj amemory_addrs_pto empty_iff insertCI)
    subgoal by (simp add: f_valid_addr_\<alpha> f_valid_addrs_def sep_add_commute sep_disj_commute)
    done
    
  subsubsection \<open>Alloc\<close>    
    
  lift_definition llvm_block :: "nat \<Rightarrow> nat \<Rightarrow> 'a amemory" is "\<lambda>b n. (0,0(b:=TRIV n))" .
  
  definition "llvm_blockv xs b \<equiv> sepsum_list (map (\<lambda>i. llvm_ato (xs!i) (ADDR b (int i))) [0..<length xs])"

  definition "llvm_ptr_is_block_base p \<equiv> llvm_ptr.is_addr p \<and> llvm_addr.idx (llvm_ptr.the_addr p) = 0"
  definition "llvm_ptr_the_block p \<equiv> llvm_addr.block (llvm_ptr.the_addr p)"
    
  definition "llvm_blockp p n \<equiv> \<up>(llvm_ptr_is_block_base p) ** EXACT (llvm_block (llvm_ptr_the_block p) n)"
  definition "llvm_blockvp xs p \<equiv> \<up>(llvm_ptr_is_block_base p) ** EXACT (llvm_blockv xs (llvm_ptr_the_block p))"
  
      
  lemma block_pto_disj[simp]:
    "llvm_block b n ## llvm_ato x a"
    "llvm_ato x a ## llvm_block b n"
    by (transfer;simp add: sep_algebra_simps zero_tsa_opt_def)+
    
  lemma llvm_pto_disj[simp]: "llvm_ato x a ## llvm_ato y b \<longleftrightarrow> a\<noteq>b"  
    apply transfer
    apply (auto simp: sep_algebra_simps)
    done
    

  lemma block_init_aux:  "distinct is \<Longrightarrow> 
    sep_distinct (map (\<lambda>i. llvm_ato (zi i) (ADDR b' (int i))) is)
  \<and> (\<forall>i. i\<notin>set is \<longrightarrow> llvm_ato (zi i) (ADDR b' (int i)) ## sepsum_list (map (\<lambda>i. llvm_ato (zi i) (ADDR b' (int i))) is))  
    "
    apply (induction "is")
    apply auto
    done
    
        
  lemma disj_block_init: "a ## llvm_blockv xs b' \<longleftrightarrow> (\<forall>i\<in>{0..<length xs}. a ## llvm_ato (xs!i) (ADDR b' (int i)))"  
    unfolding llvm_blockv_def
    apply (simp_all add: block_init_aux sep_algebra_simps)
    done
    
    
  lemma llvm_blockv_split_disj[simp]: "llvm_blockv xs b ## llvm_ato x (ADDR b (int (length xs)))"
    unfolding llvm_blockv_def
    by (simp_all add: block_init_aux sep_algebra_simps)
    
  lemma llvm_blockv_split_aux: "(map (\<lambda>i. llvm_ato ((xs @ xs') ! i) (ADDR b (int i))) [0..<length xs])
    = (map (\<lambda>i. llvm_ato (xs ! i) (ADDR b (int i))) [0..<length xs])"  
    by (simp)
    
  lemma llvm_blockv_split[simp]: "llvm_blockv (xs@[x]) b = llvm_blockv xs b + llvm_ato x (ADDR b (int (length xs)))"
    unfolding llvm_blockv_def
    by (auto simp add: block_init_aux sep_algebra_simps llvm_blockv_split_aux)
    
    
  definition "llvm_block_init_raw \<equiv> \<lambda>xs b. (\<lambda>ADDR b' i' \<Rightarrow> if b=b' \<and> 0\<le>i' \<and> i'<int (length xs) then TRIV (xs!nat i') else 0)"
    
  lift_definition llvm_block_init_alt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a amemory" is
    "\<lambda>xs b. (llvm_block_init_raw xs b,0)" .
    
  lemma llvm_block_init_alt_Nil[simp]: "llvm_block_init_alt [] b = 0" 
    apply transfer 
    apply (auto split: llvm_addr.split if_splits simp: sep_algebra_simps llvm_block_init_raw_def fun_eq_iff)
    done
    
  lemma llvm_block_init_alt_append[simp]: 
    "llvm_block_init_alt (xs@[x]) b = llvm_block_init_alt xs b + llvm_ato x (ADDR b (int (length xs)))
    \<and> llvm_block_init_alt xs b ## llvm_ato x (ADDR b (int (length xs)))"
    apply transfer 
    apply (auto split: llvm_addr.split simp: sep_algebra_simps llvm_block_init_raw_def fun_eq_iff)
    done
    
    
  lemma llvm_block_init_alt_aux: "map (\<lambda>xa. llvm_ato ((xs @ [x]) ! xa) (ADDR b (int xa))) [0..<length xs] 
    = map (\<lambda>xa. llvm_ato (xs ! xa) (ADDR b (int xa))) [0..<length xs]"  
    by auto
    
  lemma llvm_block_init_alt: "llvm_blockv xs b = llvm_block_init_alt xs b"  
    unfolding llvm_blockv_def
    apply (induction xs rule: rev_induct)
    apply (simp_all add: sep_algebra_simps block_init_aux llvm_block_init_alt_aux cong: map_cong)
    done
    
  lemma block_block_init_dj[simp]: "llvm_block b n ## llvm_block_init_alt xs b'"  
    apply (induction xs rule: rev_induct)
    apply simp_all
    done
    
  lemma block_block_init_dj'[simp]: 
    "llvm_block b n ## llvm_blockv xs b'"  
    "llvm_blockv xs b' ## llvm_block b n"  
    unfolding llvm_blockv_def
    by (simp_all add: block_init_aux sep_algebra_simps)
        
  lemma f_alloc_valid_trans[simp]: "f_alloc x n m = (b, m') \<Longrightarrow> valid_trans m m'"  
    unfolding valid_trans_def f_valid_addrs_def f_freed_addrs_def
    apply auto
    subgoal by (meson f_valid_addr_alloc)
    subgoal by (meson f_alloc_freed_block)
    done
    

  lemma llvmt_alloc_rule[vcg_rules]: "htriple \<box> (llvmt_alloc s n) (\<lambda>b. 
    EXACT (llvm_block b n) ** EXACT (llvm_blockv (replicate n (llvm_zero_initializer s)) b)
  )"
    unfolding llvmt_alloc_def
    apply rule
    supply [split] = prod.splits
    
    apply vcg_all
    apply vcg_normalize
    apply (simp add: sep_algebra_simps STATE_def flip: EXACT_split)
    apply (intro conjI)
    subgoal
      apply transfer
      apply (auto simp: sep_algebra_simps llvm_\<alpha>b_def)
      by (meson f_alloc_fresh_block)
    subgoal
      apply (clarsimp simp add: sep_algebra_simps disj_block_init)
      apply transfer
      apply (auto simp add: sep_algebra_simps llvm_\<alpha>m_def)
      by (meson f_alloc_fresh_block valid_addr_valid_block)
    subgoal
      unfolding llvm_block_init_alt
      apply transfer
      apply (auto simp add: sep_algebra_simps llvm_\<alpha>m_def llvm_block_init_raw_def)
      subgoal
        apply (clarsimp 
          simp: fun_eq_iff llvm_\<alpha>m_def sep_algebra_simps
          split: llvm_addr.splits)
        by (metis (no_types, lifting) f_alloc_fresh_block f_load_alloc f_load_alloc_indep f_valid_addr_alloc llvm_addr.inject nat_less_iff nth_replicate valid_addr_valid_block)  
      subgoal for sa s n x1 x2
        by (auto 
          simp: fun_eq_iff llvm_\<alpha>b_def 
          dest: f_alloc_fresh_block f_alloc_valid_block f_alloc_block_size_this f_alloc_block_size_other)
      done
      
    done
    
    
    
  lemma llvmt_allocp_rule[vcg_rules]: "htriple \<box> (llvmt_allocp s n) (\<lambda>p. 
    llvm_blockp p n ** llvm_blockvp (replicate n (llvm_zero_initializer s)) p
  )"
    unfolding llvm_blockp_def llvm_blockvp_def llvm_ptr_is_block_base_def llvm_ptr_the_block_def llvmt_allocp_def
    apply vcg
    done
    
    
  subsubsection \<open>Free\<close>  
    
  lemma llvm_block_valid: "llvm_block b n ## asf \<Longrightarrow> llvm_\<alpha> s = llvm_block b n + asf \<Longrightarrow> f_valid_block b s"
    apply transfer
    apply (auto simp: llvm_\<alpha>b_def fun_eq_iff sep_algebra_simps split: if_splits)
    done
    
  lemma llvm_block_init_raw_other: "llvm_addr.block a' \<noteq> ba \<Longrightarrow> llvm_block_init_raw xs ba a' = 0"  
    unfolding llvm_block_init_raw_def
    apply (cases a'; auto)
    done
    
  lemma llvmt_free_aux: "\<lbrakk>
    f_block_size (llvm_addr.block a') sa = length xs; 
    as a' ## llvm_block_init_raw xs (llvm_addr.block a') a';
    f_valid_addr a' sa
  \<rbrakk>
    \<Longrightarrow> as a' = 0"  
    unfolding llvm_block_init_raw_def
    apply (cases a'; auto simp: sep_algebra_simps split: if_splits)
    apply (simp add: f_block_size.rep_eq f_valid_addr.rep_eq)
    apply (simp add: f_block_size.rep_eq f_valid_addr.rep_eq nat_less_iff)
    done
    
    
  lemma f_free_valid_trans: "f_valid_block b sa \<Longrightarrow> valid_trans sa (f_free b sa)"
    unfolding valid_trans_def f_valid_addrs_def f_freed_addrs_def
    apply auto
    by (metis llvm_addr.collapse)
    
  lemma llvmt_free_rule[vcg_rules]: "htriple 
    (EXACT (llvm_block b (length xs)) ** EXACT (llvm_blockv xs b)) 
    (llvmt_free b) 
    (\<lambda>_. \<box>) 
  "
    unfolding llvmt_free_def
    apply rule
    apply vcg_all
    apply (clarsimp simp: sep_algebra_simps STATE_def simp flip: EXACT_split)
    subgoal for sa asf
      apply (subgoal_tac "f_valid_block b sa")
      subgoal
        unfolding llvm_block_init_alt
        apply transfer
        apply (clarsimp simp: sep_algebra_simps fun_eq_iff)
        apply (intro conjI allI)
        subgoal for as b xs ba sa a'
          (* TODO: Clean up this mess! *)
          apply (auto simp: llvm_\<alpha>m_def split: if_splits) []
          apply (clarsimp simp: llvm_block_init_raw_other )
          apply (auto simp: sep_algebra_simps sep_disj_fun_def) []
          apply (auto simp: sep_algebra_simps sep_disj_fun_def llvm_\<alpha>b_def split: if_splits) []
          apply (subgoal_tac "f_block_size (llvm_addr.block a') sa = length xs")
          apply (subgoal_tac "as a' ## llvm_block_init_raw xs (llvm_addr.block a') a'")
          apply (cases "\<not>f_valid_addr a' sa"; simp) 
          apply blast
          apply (blast intro: llvmt_free_aux)
          apply simp_all 
          done
        subgoal
          apply (auto simp: llvm_\<alpha>b_def fun_eq_iff split: if_splits)
          done
        done
      subgoal
        by (smt (verit, best) block_block_init_dj'(2) llvm_block_valid sep_add_ac(4) sep_add_commute sep_add_left_commute sep_disj_add_eq)

    done
    subgoal by (metis STATE_exact_iff STATE_frame1 llvm_block_valid)
    subgoal by (metis STATE_exact_iff STATE_frame1 f_free_valid_trans llvm_block_valid)
    done
    
    
  lemma llvmt_freep_rule[vcg_rules]: "htriple 
    (llvm_blockp p (length xs) ** llvm_blockvp xs p) 
    (llvmt_freep p) 
    (\<lambda>_. \<box>) 
  "
    unfolding llvm_blockp_def llvm_blockvp_def llvm_ptr_is_block_base_def llvm_ptr_the_block_def llvmt_freep_def
    apply (cases p; simp)
    subgoal for a
      apply (cases a; simp add: sep_algebra_simps)
      apply vcg
      done
    done
  
  definition "llvm_pto x p \<equiv> case p of PTR_NULL \<Rightarrow> sep_false | PTR_ADDR a \<Rightarrow> if llvm_addr.idx a \<ge> 0 then EXACT (llvm_ato x a) else sep_false"
  
  
  subsection \<open>Pointer Reasoning\<close>
  
  class addr_algebra =
    fixes abase :: "'a \<Rightarrow> bool"
      and acompat :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "~\<^sub>a" 50)
      and adiff :: "'a \<Rightarrow> 'a \<Rightarrow> int" (infix "-\<^sub>a" 65)
      and aidx :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infixl "+\<^sub>a" 65)
    assumes 
        \<comment> \<open>Compatibility is equivalence relation over base pointers\<close>
            acompat_equiv: "part_equivp acompat"  
        and acompat_dom: "a\<^sub>1 ~\<^sub>a a\<^sub>2 \<Longrightarrow> abase a\<^sub>1 \<and> abase a\<^sub>2"
        
        \<comment> \<open>Indexing properties\<close>
        and aidx_Z[simp]: "a +\<^sub>a 0 = a" \<comment> \<open>Indexing by zero extended to non-base pointers\<close>
        and aidx_plus[simp]: "abase a \<Longrightarrow> a +\<^sub>a i\<^sub>1 +\<^sub>a i\<^sub>2 = a +\<^sub>a (i\<^sub>1 + i\<^sub>2)"
        and aidx_inj[simp]: "abase a \<Longrightarrow> a +\<^sub>a i = a +\<^sub>a j \<longleftrightarrow> i=j"
        (*and abase_idx[simp, intro!]: "abase a \<Longrightarrow> abase (a +\<^sub>a i)"*)
        and abase_idx[simp]: "abase (a +\<^sub>a i) \<longleftrightarrow> abase a"
        
        \<comment> \<open>Difference\<close>
        and adiff_same[simp]: "a -\<^sub>a a = 0" \<comment> \<open>Reflexive difference extended to non-base pointers\<close>
        and aidx_compat[simp]: "abase a \<Longrightarrow> a ~\<^sub>a a+\<^sub>ai"
        and adiff_idx[simp]: "a ~\<^sub>a b \<Longrightarrow> a +\<^sub>a (b -\<^sub>a a) = b"
        
  begin
    lemma acompat_trans[trans]: "a ~\<^sub>a b \<Longrightarrow> b ~\<^sub>a c \<Longrightarrow> a ~\<^sub>a c"
      using acompat_equiv by (meson part_equivp_transp)
  
    lemma acompat_sym[sym, intro]: "a ~\<^sub>a b \<Longrightarrow> b ~\<^sub>a a"
      using acompat_equiv by (meson part_equivp_symp)

    (*lemma acompat_sym_iff[simp]: "p~\<^sub>ap' \<longleftrightarrow> p'~\<^sub>ap"
      using acompat_sym by auto
    *)
      
        
    lemma acompat_refl[simp]: "a ~\<^sub>a a \<longleftrightarrow> abase a"  
      using acompat_sym acompat_trans local.acompat_dom local.aidx_compat by blast
      
    lemma aidx_compat'[simp]: 
      "abase b \<Longrightarrow> a ~\<^sub>a b +\<^sub>a i  \<longleftrightarrow> a ~\<^sub>a b"  
      "abase a \<Longrightarrow> a +\<^sub>a i ~\<^sub>a b \<longleftrightarrow> a ~\<^sub>a b"  
      using acompat_sym acompat_trans local.aidx_compat by blast+
      
    lemma diff_Z_iff_eq[simp]: "a\<^sub>1 ~\<^sub>a a\<^sub>2 \<Longrightarrow> a\<^sub>1 -\<^sub>a a\<^sub>2 = 0 \<longleftrightarrow> a\<^sub>1=a\<^sub>2"  
      by (metis acompat_sym acompat_trans local.adiff_idx local.adiff_same)
      
    lemma diff_Z_iff_eq'[simp]: "a\<^sub>2 ~\<^sub>a a\<^sub>1 \<Longrightarrow> a\<^sub>1 -\<^sub>a a\<^sub>2 = 0 \<longleftrightarrow> a\<^sub>1=a\<^sub>2"  
      by (metis acompat_sym acompat_trans local.adiff_idx local.adiff_same)
      
    lemma adiff_idx'[simp]: "b ~\<^sub>a a \<Longrightarrow> a +\<^sub>a (b -\<^sub>a a) = b"
      using acompat_sym local.adiff_idx by blast
      

    lemma idx_diff_distrib[simp]: "p~\<^sub>ap' \<Longrightarrow> (p+\<^sub>ai)-\<^sub>ap' = (p-\<^sub>ap')+i"
      by (metis acompat_dom adiff_idx' aidx_compat aidx_inj aidx_plus)
    lemma idx_diff_distrib'[simp]: "p'~\<^sub>ap \<Longrightarrow> (p+\<^sub>ai)-\<^sub>ap' = (p-\<^sub>ap')+i"
      by (metis acompat_dom adiff_idx' aidx_compat aidx_inj aidx_plus)
    
    lemma adiff_idx_idx[simp]:
      "p~\<^sub>ap' \<Longrightarrow> p +\<^sub>a (p' -\<^sub>a p + i) = p' +\<^sub>a i"
      "p'~\<^sub>ap \<Longrightarrow> p +\<^sub>a (p' -\<^sub>a p + i) = p' +\<^sub>a i"
      apply (metis acompat_dom adiff_idx aidx_plus)
      by (metis acompat_dom adiff_idx' aidx_plus)
      
    lemma acompat_dom'[simp, intro]:
      "p~\<^sub>ap' \<Longrightarrow> abase p"
      "p~\<^sub>ap' \<Longrightarrow> abase p'"
      apply (simp_all add: acompat_dom)
      done
            
  end        

  
  instantiation llvm_addr :: addr_algebra begin
    definition abase_llvm_addr where [simp]: "abase_llvm_addr (_::llvm_addr) = True"
    fun acompat_llvm_addr where "ADDR bi\<^sub>1 ba\<^sub>1 ~\<^sub>a ADDR bi\<^sub>2 ba\<^sub>2 \<longleftrightarrow> bi\<^sub>1=bi\<^sub>2"
    fun aidx_llvm_addr where "ADDR bi ba +\<^sub>a i = ADDR bi (ba + i)"
    fun adiff_llvm_addr where "ADDR bi\<^sub>1 ba\<^sub>1 -\<^sub>a ADDR bi\<^sub>2 ba\<^sub>2 = ba\<^sub>1 - ba\<^sub>2"
    
    lemma acomp_llvm_addr_alt: "(~\<^sub>a) = (\<lambda>ADDR bi\<^sub>1 ba\<^sub>1 \<Rightarrow> \<lambda>ADDR bi\<^sub>2 ba\<^sub>2 \<Rightarrow> bi\<^sub>1=bi\<^sub>2)" by (intro ext) (auto split: llvm_addr.splits)
    lemma aidx_llvm_addr_alt: "(+\<^sub>a) = (\<lambda>ADDR bi ba \<Rightarrow> \<lambda>i. ADDR bi (ba + i))" by (intro ext) (auto split: llvm_addr.splits)
    lemma adiff_llvm_addr_alt: "(-\<^sub>a) = (\<lambda>ADDR bi\<^sub>1 ba\<^sub>1 \<Rightarrow> \<lambda>ADDR bi\<^sub>2 ba\<^sub>2 \<Rightarrow> ba\<^sub>1 - ba\<^sub>2)" by (intro ext) (auto split: llvm_addr.splits)

    instance
      apply standard
      apply (intro part_equivpI sympI transpI)
      apply (meson acompat_equiv acompat_llvm_addr.simps(1) part_equivp_def)
      apply (auto 
        simp: acomp_llvm_addr_alt aidx_llvm_addr_alt adiff_llvm_addr_alt
        split: llvm_addr.splits 
        intro: acompat_trans) 
        
      done
  
  end
    
  instantiation llvm_ptr :: addr_algebra begin
    fun abase_llvm_ptr where "abase (PTR_ADDR _) = True" | "abase PTR_NULL = False"
  
    fun acompat_llvm_ptr where 
      "PTR_ADDR a ~\<^sub>a PTR_ADDR b \<longleftrightarrow> a~\<^sub>ab"
    | "(_::llvm_ptr) ~\<^sub>a _ \<longleftrightarrow> False"
      
    fun aidx_llvm_ptr where 
      "PTR_ADDR a +\<^sub>a i = PTR_ADDR (a +\<^sub>a i)"
    | "PTR_NULL +\<^sub>a i = PTR_NULL"  
      
    fun adiff_llvm_ptr where 
      "PTR_ADDR a -\<^sub>a PTR_ADDR b = a -\<^sub>a b"
    | "PTR_NULL -\<^sub>a PTR_NULL = 0"
    | "(_::llvm_ptr) -\<^sub>a _ = undefined"

    instance
      apply standard
      apply (intro part_equivpI sympI transpI)
      subgoal by (meson acompat_llvm_addr.simps acompat_llvm_ptr.simps(1))
      subgoal for a b by (cases a; cases b; auto)
      subgoal for x y z by (cases x; cases y; cases z; auto intro: acompat_trans)
      subgoal for a\<^sub>1 a\<^sub>2 by (cases a\<^sub>1; cases a\<^sub>2; auto)
      subgoal for a by (cases a; auto)
      subgoal for a by (cases a; auto)
      subgoal for a by (cases a; auto)
      subgoal for a by (cases a; auto)
      subgoal for a by (cases a; auto)
      subgoal for a by (cases a; auto)
      subgoal for a b by (cases a; cases b; auto)
      done
  
  end
  
  lemma llvmt_check_ptr_rule[vcg_rules]: "htriple (llvm_pto x p) (llvmt_check_ptr p) (\<lambda>_. llvm_pto x p)"
    unfolding llvmt_check_ptr_def
    apply rule
    apply vcg
    apply vcg_normalize
    apply (auto 
      simp: llvm_pto_def f_valid_ptr_def sep_algebra_simps f_valid_addr_\<alpha> f_valid_addr_is_ptr_valid STATE_def
      split: llvm_ptr.splits if_splits)
    done
  
  (* TODO: Move *)  
  lemma llvm_pto_null[simp]: "llvm_pto x PTR_NULL = sep_false"  
    by (simp add: llvm_pto_def)
    
  lemma pure_part_llvm_pto[simp]: "pure_part (llvm_pto x p) \<longleftrightarrow> llvm_ptr.is_addr p \<and> llvm_addr.idx (llvm_ptr.the_addr p)\<ge>0"  
    unfolding llvm_pto_def
    apply (cases p; simp)
    done
        
  lemma llvm_addr_idx_add[simp]: "llvm_addr.idx (a +\<^sub>a i) = llvm_addr.idx a + i"  
    by (metis aidx_llvm_addr.elims llvm_addr.sel(2))
    
  lemma fold_addr_add: "ADDR (llvm_addr.block a) (llvm_addr.idx a + i) = a+\<^sub>ai"
    by (cases a; simp)
    
  (* TODO: Also include one-past-end pointers! *)
  lemma llvmt_ofs_ptr_weak_rule[vcg_rules]: "htriple (llvm_pto x (p +\<^sub>a i)) (llvmt_ofs_ptr p i) (\<lambda>r. \<up>(r=p +\<^sub>a i) ** llvm_pto x (p +\<^sub>a i))"
    apply (cases p; simp)
    unfolding llvmt_ofs_ptr_def Let_def
    supply [simp] = fold_addr_add
    apply vcg_all
    apply (auto simp: STATE_def llvm_pto_def split: if_splits)
    done
    
  lemma llvmt_check_ptrcmp_null[vcg_normalize_simps]:
    "llvmt_check_ptrcmp PTR_NULL p\<^sub>2 = return ()"  
    "llvmt_check_ptrcmp p\<^sub>1 PTR_NULL = return ()"  
    unfolding llvmt_check_ptrcmp_def by auto
    
  lemma llvmt_ptr_eq_weak_rule[vcg_rules]: "htriple (llvm_pto x p\<^sub>1 ** llvm_pto y p\<^sub>2) (llvmt_ptr_eq p\<^sub>1 p\<^sub>2) 
    (\<lambda>r. \<up>(r \<longleftrightarrow> p\<^sub>1=p\<^sub>2) ** llvm_pto x p\<^sub>1 ** llvm_pto y p\<^sub>2)"
    apply (cases p\<^sub>1; cases p\<^sub>2; simp)
    unfolding llvmt_ptr_eq_def Let_def llvmt_check_ptrcmp_def
    apply vcg
    done
    
  lemma llvmt_ptr_neq_weak_rule[vcg_rules]: "htriple (llvm_pto x p\<^sub>1 ** llvm_pto y p\<^sub>2) (llvmt_ptr_neq p\<^sub>1 p\<^sub>2) 
    (\<lambda>r. \<up>(r \<longleftrightarrow> p\<^sub>1\<noteq>p\<^sub>2) ** llvm_pto x p\<^sub>1 ** llvm_pto y p\<^sub>2)"
    apply (cases p\<^sub>1; cases p\<^sub>2; simp)
    unfolding llvmt_ptr_neq_def Let_def llvmt_check_ptrcmp_def
    apply vcg
    done
    
  lemma check_ptr_null[vcg_normalize_simps]: "llvmt_check_ptr PTR_NULL = return ()"
    unfolding llvmt_check_ptr_def by (simp add: f_valid_ptr_def)
    
  lemma llvmt_ptr_cmp_null[vcg_normalize_simps]:
    "llvmt_ptr_eq PTR_NULL b = return (PTR_NULL = b)"  
    "llvmt_ptr_eq a PTR_NULL = return (a = PTR_NULL)"  
    "llvmt_ptr_neq PTR_NULL b = return (PTR_NULL \<noteq> b)"  
    "llvmt_ptr_neq a PTR_NULL = return (a \<noteq> PTR_NULL)"  
    unfolding llvmt_ptr_eq_def llvmt_ptr_neq_def 
    by (auto simp: vcg_normalize_simps)
    
    
    
    
end
