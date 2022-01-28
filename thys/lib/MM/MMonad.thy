theory MMonad
imports NEMonad Generic_Memory
begin

  subsection \<open>Base Type Monad Combinators\<close>
  text \<open>State monad combinators, built on ne-monad\<close>

  context
    includes monad_syntax_ne
  begin
  
    definition "malloc vs s = do {
      b \<leftarrow> spec b. mapp s b = FRESH;
      return (b, 0::interference, mmap s b (\<lambda>_. VALID vs))
    }"
    
    definition "mfree b s = do {
      assert cell.is_valid (mapp s b);
      return ((), 0::interference, mmap s b (\<lambda>_. FREED))
    }"  

    definition "mload a s = do {
      let b = addr.block a;
      let idx = addr.index a;
      assert cell.is_valid (mapp s b);
      return (cell.vals (mapp s b) idx, intf_r {a}, s)
    }"
    
    definition "mstore a v s = do {
      let b = addr.block a;
      let idx = addr.index a;
      assert cell.is_valid (mapp s b);
      return ((), intf_w {a}, mmap s b (\<lambda>VALID vs \<Rightarrow> VALID (vs(idx:=v))))
    }"
  
    definition "preturn x s = (return (x,0::interference,s))"
    
    definition "pbind m f s \<equiv> do {
      (x,i\<^sub>1,s) \<leftarrow> m s;
      (r,i\<^sub>2,s) \<leftarrow> f x s;
      return (r,i\<^sub>1+i\<^sub>2 ::interference,s)
    }"  
  
    definition "ppar m\<^sub>1 m\<^sub>2 s \<equiv> do {
      ((r\<^sub>1,i\<^sub>1,s\<^sub>1),(r\<^sub>2,i\<^sub>2,s\<^sub>2)) \<leftarrow> m\<^sub>1 s \<parallel> m\<^sub>2 s;
      assert intf_consistent s i\<^sub>1 s\<^sub>1 \<and> intf_consistent s i\<^sub>2 s\<^sub>2; \<comment> \<open>Ensure reported interference is 
        consistent with observable modifications on state. This will later be enforced by subtyping.\<close>
      assume spar_feasible s s\<^sub>1 s\<^sub>2; \<comment> \<open>Filter out impossible combinations (where malloc did not sync)\<close>
      assert intf_norace i\<^sub>1 i\<^sub>2; \<comment> \<open>Fail on data races\<close>
      let s = combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2; \<comment> \<open>Combine states\<close>
      return ((r\<^sub>1,r\<^sub>2),i\<^sub>1+i\<^sub>2,s) 
    }"
      

  end    

  subsection \<open>Invariant\<close>  
  text \<open>
    We prove the following invariants
  
    \<^enum> the reported interference is consistent with the observable changes on the state. 
      This is a sanity check property, which also enables us to show commutativity of par.
    \<^enum> each program returns at least one possible result.
      This is a sanity check property, which ensures that we don't accidentally verify a 
      'magic' program.
    \<^enum> the memory manager can choose any available addresses.
      This is required to give it enough flexibility to always leave non-conflicting choices
      for parallel composition.
  
  \<close>
  
  definition "consistentM m \<equiv> \<forall>s. wlp (m s) (\<lambda>(_,i,s'). intf_consistent s i s')"
  definition "consistentM_pw s m \<equiv> wlp m (\<lambda>(_,i,s'). intf_consistent s i s')"
  
  definition "non_emptyM_pw s m \<equiv> \<not>is_fail m \<longrightarrow> 
    (\<forall>A. finite A \<longrightarrow> (\<exists>x i s'. is_res m (x,i,s') \<and> alloc_blocks s s' \<inter> A = {} ))"
  definition "non_emptyM m \<equiv> \<forall>s. \<not>is_fail (m s) \<longrightarrow> 
    (\<forall>A. finite A \<longrightarrow> (\<exists>x i s'. is_res (m s) (x,i,s') \<and> alloc_blocks s s' \<inter> A = {} ))"
  
  lemma non_emptyM_pw: "non_emptyM m = (\<forall>s. non_emptyM_pw s (m s))"
    unfolding non_emptyM_def non_emptyM_pw_def by simp
  
  lemma consistentM_pw: "consistentM m \<longleftrightarrow> (\<forall>s. consistentM_pw s (m s))"
    unfolding consistentM_def consistentM_pw_def by auto
      
  definition "invarM m \<equiv> consistentM m \<and> non_emptyM m"  

  definition "invarM_pw s m \<equiv> consistentM_pw s m \<and> non_emptyM_pw s m"
  
  lemma invarM_pw: "invarM m = (\<forall>s. invarM_pw s (m s))"
    unfolding invarM_def invarM_pw_def
    by (auto simp add: consistentM_pw non_emptyM_pw)
  
  
  
  
  
      
  lemma consistentMI[intro?]:
    assumes "\<And>s. wlp (m s) (\<lambda>(_,i,s'). intf_consistent s i s')"
    shows "consistentM m"
    using assms unfolding consistentM_def ..
    
  lemma consistentMD:
    assumes "consistentM m"
    shows "wlp (m s) (\<lambda>(_,i,s'). intf_consistent s i s')"
    using assms unfolding consistentM_def ..

  lemma consistent_wlp: "consistentM m \<Longrightarrow> (\<And>x i s'. intf_consistent s i s' \<Longrightarrow> Q (x,i,s')) \<Longrightarrow> (wlp (m s) Q)"  
    unfolding consistentM_def by pw

  lemma invarM_pw_FAIL[simp]: "invarM_pw s FAIL" 
    unfolding invarM_pw_def consistentM_pw_def non_emptyM_pw_def
    by pw
          
    
    
            
  subsubsection \<open>Invariant Preservation\<close>
    
  context begin \<comment> \<open>This context will be closed after lifting is completed\<close>
  
    qualified named_theorems invarM_lemmas 
  
    
    lemma [invarM_lemmas]: "consistentM (malloc v)"
      unfolding consistentM_def malloc_def
      apply rule
      apply wp
      apply (auto simp: intf_consistent_def)
      done
      
    lemma [invarM_lemmas]: "consistentM (mfree a)"
      unfolding consistentM_def mfree_def
      apply rule
      apply wp
      apply auto
      unfolding intf_consistent_def
      by (auto)
  
    lemma [invarM_lemmas]: "consistentM (mload a)"
      unfolding consistentM_def mload_def
      apply rule
      apply wp
      apply auto
      unfolding intf_consistent_def
      by (auto simp: )
      
    lemma [invarM_lemmas]: "consistentM (mstore a v)"
      unfolding consistentM_def mstore_def
      apply rule
      apply wp
      apply auto
      unfolding intf_consistent_def
      by (auto split: cell.split)
  
  
    lemma [invarM_lemmas]: "consistentM (preturn x)"
      unfolding consistentM_def preturn_def
      apply rule
      apply wp
      apply auto
      unfolding intf_consistent_def
      by (auto simp: zero_interference_def)
      
    lemma [invarM_lemmas]: "consistentM m \<Longrightarrow> (\<And>x. consistentM (f x)) \<Longrightarrow> consistentM (pbind m f)"  
      supply [wp_recursion_rule] = consistent_wlp
      unfolding pbind_def
      apply rule
      apply wp
      unfolding intf_consistent_def is_valid_def plus_interference_def
      apply (clarsimp split: interference.splits)
      apply (intro conjI; clarsimp)
      subgoal
        by (metis Un_iff cell_state_trans_simps(4) cell_state_trans_trans)
      subgoal
        by (meson cell_state_trans_trans)
      subgoal
        by (metis cell.sel cell_state_trans_def is_valid_def)
      done
      
      
    lemma cell_combine_eq_iffs:
      "cell_combine c A c' = FRESH \<longleftrightarrow> c=FRESH \<and> c'=FRESH"  
      "cell_combine c A c' = FREED \<longleftrightarrow> c=FREED \<or> c'=FREED"
      by (cases c; cases c'; simp)+

    (*lemma "cell_combine c\<^sub>1 I c\<^sub>2 = VALID vs \<longleftrightarrow> (\<exists>vs\<^sub>1 vs\<^sub>2. c\<^sub>1=VALID vs\<^sub>1 \<and> c\<^sub>2=VALID vs\<^sub>2 \<and> vs = (\<lambda>i. if i\<in>I then vs\<^sub>2 i else vs\<^sub>1 i))"  
      by (cases c\<^sub>1; cases c\<^sub>2; simp)
    *)
                  
    lemma [invarM_lemmas]: "consistentM m\<^sub>1 \<Longrightarrow> consistentM m\<^sub>2 \<Longrightarrow> consistentM (ppar m\<^sub>1 m\<^sub>2)"    
      supply [wp_recursion_rule] = consistent_wlp
      supply [wp_rule] = wlp_PAR[OF consistentMD consistentMD]
      unfolding ppar_def
      apply rule
      apply wp
      apply clarsimp
      apply wp
      apply simp_all
      unfolding intf_consistent_def is_valid_def plus_interference_def combine_states_def
      apply (clarsimp split: interference.splits simp: cell_combine_eq_iffs)
      apply (intro conjI; clarsimp)
      subgoal 
        unfolding spar_feasible_def intf_norace_def Let_def
        by auto
        
      apply (metis cell.exhaust_disc cell_combine_eq_iffs(1) cell_combine_eq_iffs(2) cell_state_trans_def; fail)  
        
      by (smt (verit) cell.collapse cell.exhaust_disc cell.simps(1) cell_combine.simps(7) cell_combine_eq_iffs(2) cell_state_trans_simps(4) is_valid_def)
      
      
    lemma [invarM_lemmas]: "non_emptyM (malloc v)"  
      unfolding non_emptyM_def malloc_def alloc_blocks_def
      apply pw
      using ex_fresh by fastforce
  
    lemma [invarM_lemmas]: "non_emptyM (mfree a)"  
      unfolding non_emptyM_def mfree_def alloc_blocks_def
      by pw
      
    lemma [invarM_lemmas]: "non_emptyM (mload a)"  
      unfolding non_emptyM_def mload_def
      by pw
      
    lemma [invarM_lemmas]: "non_emptyM (mstore a v)"  
      unfolding non_emptyM_def mstore_def alloc_blocks_def
      by pw
  
    lemma [invarM_lemmas]: "non_emptyM (preturn x)"  
      unfolding non_emptyM_def preturn_def
      by pw
      
              
    lemma [invarM_lemmas]: "non_emptyM m \<Longrightarrow> (\<And>x. non_emptyM (f x)) \<Longrightarrow> non_emptyM (pbind m f)"  
      unfolding non_emptyM_def pbind_def alloc_blocks_def
      apply pw
      by (smt (verit, ccfv_SIG) disjoint_iff mem_Collect_eq)
      
      
    lemma finite_alloc_blocks[simp, intro]: "finite (alloc_blocks s s')"  
      unfolding alloc_blocks_def
      by (simp add: finite_non_fresh)
      
    lemma alloc_blocks_combine_eq: "alloc_blocks s (combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2) = alloc_blocks s s\<^sub>1 \<union> alloc_blocks s s\<^sub>2"  
      unfolding alloc_blocks_def combine_states_def
      by (auto simp: cell_combine_eq_iffs)
    
      
    lemma [invarM_lemmas]: "\<lbrakk>non_emptyM m\<^sub>1; consistentM m\<^sub>1; non_emptyM m\<^sub>2; consistentM m\<^sub>2 \<rbrakk> \<Longrightarrow> non_emptyM (ppar m\<^sub>1 m\<^sub>2)"
      unfolding non_emptyM_def ppar_def
      apply pw
    proof goal_cases
      case (1 s A)
      
      obtain x\<^sub>1 i\<^sub>1 s\<^sub>1 where R1: "is_res (m\<^sub>1 s) (x\<^sub>1, i\<^sub>1, s\<^sub>1)" and I1: "alloc_blocks s s\<^sub>1 \<inter> A = {}" using 1 by meson
      
      hence "intf_consistent s i\<^sub>1 s\<^sub>1" using \<open>consistentM m\<^sub>1\<close> \<open>m\<^sub>1 s \<noteq> FAIL\<close>
        unfolding consistentM_def wlp_def by pw 
      have "finite (alloc_blocks s s\<^sub>1 \<union> A)" using 1 by auto
      then obtain x\<^sub>2 i\<^sub>2 s\<^sub>2 where R2: "is_res (m\<^sub>2 s) (x\<^sub>2, i\<^sub>2, s\<^sub>2)" and I2: "alloc_blocks s s\<^sub>2 \<inter> (alloc_blocks s s\<^sub>1 \<union> A) = {}"  
        using 1 by metis
      hence NF2: "m\<^sub>2 s \<noteq> FAIL" using 1 by metis
      with R2 have "intf_consistent s i\<^sub>2 s\<^sub>2" using \<open>consistentM m\<^sub>2\<close>
        unfolding consistentM_def wlp_def by pw 
  
      from I2 have "spar_feasible s s\<^sub>1 s\<^sub>2"
        unfolding spar_feasible_def by blast
      
      with I1 I2 R1 R2 NF2 have NI: "intf_norace i\<^sub>1 i\<^sub>2" using 1
        by metis
        
        
      show ?case
        apply (rule exI[where x=x\<^sub>1])
        apply (rule exI[where x=x\<^sub>2])
        apply (rule exI[where x="i\<^sub>1+i\<^sub>2"])
        apply (rule exI[where x="combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2"])
        
        apply (rule conjI)
        subgoal
          apply (intro exI conjI impI)
          apply fact
          apply fact
          apply (rule NI)
          apply fact
          apply fact
          apply (rule NI)
          apply fact
          apply fact
          apply simp
          apply simp
          apply simp
          done
        subgoal using I1 I2 by (auto simp: alloc_blocks_combine_eq)
        done
        
    qed

      
    declare invarM_def[invarM_lemmas]      

subsection \<open>Subtyping to Invariant\<close>    
  text \<open>We create a subtype that satisfies the invariant, and 
    lift the monad combinators
  \<close>

    typedef ('r,'v) M = "{m::'v memory \<Rightarrow> ('r\<times>interference\<times>'v memory) neM. invarM m}" 
      morphisms run Abs_M
      unfolding invarM_def consistentM_def non_emptyM_def
      by pw
      
    setup_lifting type_definition_M

    lemma invarM_run: "invarM (run m)"
      using run by force
        
    lift_definition Mreturn :: "'r \<Rightarrow> ('r,'v) M" is preturn by (simp add: invarM_lemmas)
    lift_definition Mbind :: "('x,'v) M \<Rightarrow> ('x \<Rightarrow> ('r,'v) M) \<Rightarrow> ('r,'v) M"
      is pbind by (auto simp add: invarM_lemmas intro!: invarM_pw[THEN iffD1])
    
    lift_definition Mpar :: "('x,'v) M \<Rightarrow> (('y,'v) M) \<Rightarrow> ('x\<times>'y,'v) M"
      is ppar by (simp add: invarM_lemmas)
    
    lift_definition Mmalloc :: "(nat \<Rightarrow> 'v) \<Rightarrow> (block,'v) M" is malloc by (simp add: invarM_lemmas)
    lift_definition Mfree :: "block \<Rightarrow> (unit,'v) M" is mfree by (simp add: invarM_lemmas)
    lift_definition Mload :: "addr \<Rightarrow> ('v,'v) M" is mload by (simp add: invarM_lemmas)
    lift_definition Mstore :: "addr \<Rightarrow> 'v \<Rightarrow> (unit,'v) M" is mstore by (simp add: invarM_lemmas)
  end    

subsubsection \<open>Pointwise Reasoning Setup\<close>    

  lemma M_eq_iff[pw_init]: "m=m' \<longleftrightarrow> (\<forall>s. run m s = run m' s)"
    apply transfer
    by auto
    
  lemma pw_Mreturn[pw_simp]:
    "run (Mreturn x) s \<noteq> FAIL"  
    "is_res (run (Mreturn x) s) r \<longleftrightarrow> r=(x,0,s)"  
    by (transfer'; unfold preturn_def; pw)+


  lemma pw_Mbind1[pw_simp]:
    "run (Mbind m f) s = FAIL \<longleftrightarrow> is_fail (run m s) \<or> (\<exists>x i s'. is_res (run m s) (x,i,s') \<and> is_fail (run (f x) s'))"
    apply transfer
    unfolding pbind_def
    by pw
    
  lemma pw_Mbind2[pw_simp]:
    "is_res (run (Mbind m f) s) ris \<longleftrightarrow> (case ris of (r,i'',s'') 
      \<Rightarrow>  (\<forall>x i s'. is_res (run m s) (x,i,s') \<longrightarrow> \<not>is_fail (run (f x) s'))
        \<and> (\<exists>x i i' s'. is_res (run m s) (x,i,s') \<and> is_res (run (f x) s') (r,i',s'') \<and> i''=i+i')
      )"
    apply transfer
    unfolding pbind_def
    apply pw 
    by blast
  
  lemma invarM_pw_iff: "invarM m \<longleftrightarrow> (\<forall>s. 
      (\<forall>r i s'. is_res (m s) (r,i,s') \<longrightarrow> intf_consistent s i s')
    \<and> non_emptyM_pw s (m s)
  )"  
    unfolding invarM_def consistentM_def non_emptyM_pw
    apply pw  
    by (metis is_res_def)
  

  lemma pw_Mpar1[pw_simp]:
    "run (Mpar m\<^sub>1 m\<^sub>2) s = FAIL \<longleftrightarrow> (is_fail (run m\<^sub>1 s) \<or> is_fail (run m\<^sub>2 s) 
      \<or> (\<exists>r\<^sub>1 i\<^sub>1 s\<^sub>1 r\<^sub>2 i\<^sub>2 s\<^sub>2. is_res (run m\<^sub>1 s) (r\<^sub>1,i\<^sub>1,s\<^sub>1) \<and> is_res (run m\<^sub>2 s) (r\<^sub>2,i\<^sub>2,s\<^sub>2) 
          \<and> spar_feasible s s\<^sub>1 s\<^sub>2 \<and> \<not>intf_norace i\<^sub>1 i\<^sub>2  ))"
    apply transfer
    unfolding ppar_def invarM_pw_iff
    apply pw
    done

  lemma pw_Mpar2[pw_simp]:
    "is_res (run (Mpar m\<^sub>1 m\<^sub>2) s) ris \<longleftrightarrow> (case ris of (r,i,s') \<Rightarrow> 
        (\<forall>r\<^sub>1 i\<^sub>1 s\<^sub>1 r\<^sub>2 i\<^sub>2 s\<^sub>2. is_res (run m\<^sub>1 s) (r\<^sub>1,i\<^sub>1,s\<^sub>1) \<and> is_res (run m\<^sub>2 s) (r\<^sub>2,i\<^sub>2,s\<^sub>2) \<and> spar_feasible s s\<^sub>1 s\<^sub>2 
          \<longrightarrow> intf_norace i\<^sub>1 i\<^sub>2)
      \<and> (\<exists>r\<^sub>1 i\<^sub>1 s\<^sub>1 r\<^sub>2 i\<^sub>2 s\<^sub>2. is_res (run m\<^sub>1 s) (r\<^sub>1,i\<^sub>1,s\<^sub>1) \<and> is_res (run m\<^sub>2 s) (r\<^sub>2,i\<^sub>2,s\<^sub>2) 
          \<and> spar_feasible s s\<^sub>1 s\<^sub>2 \<and> r=(r\<^sub>1,r\<^sub>2) \<and> i=i\<^sub>1+i\<^sub>2 \<and> s' = combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2  ))"
    apply transfer
    unfolding ppar_def invarM_pw_iff
    apply pw
    apply blast
    apply blast
    apply blast
    done
    
  lemma pw_Mmalloc1[pw_simp]: "run (Mmalloc vs) s \<noteq> FAIL"  
    apply transfer
    unfolding malloc_def
    by pw
    
  lemma pw_Mmalloc2[pw_simp]: "is_res (run (Mmalloc vs) s) r = (case r of (b,i,s') \<Rightarrow> 
    mapp s b = FRESH \<and> i=0 \<and> s' = mmap s b (\<lambda>_. VALID vs)
  )"  
    apply transfer'
    unfolding malloc_def
    by pw
    
  lemma pw_Mfree1[pw_simp]: "run (Mfree b) s = FAIL \<longleftrightarrow> \<not>cell.is_valid (mapp s b)"  
    apply transfer'
    unfolding mfree_def
    by pw
    
  lemma pw_Mfree2[pw_simp]: "is_res (run (Mfree b) s) r = (case r of (_,i,s') \<Rightarrow> 
    cell.is_valid (mapp s b) \<and> i=0 \<and> s' = mmap s b (\<lambda>_. FREED)
  )"  
    apply transfer'
    unfolding mfree_def
    by pw
    
  lemma pw_Mload1[pw_simp]: "run (Mload a) s = FAIL \<longleftrightarrow> \<not>cell.is_valid (mapp s (addr.block a))"  
    apply transfer'
    unfolding mload_def
    by pw
    
  lemma pw_Mload2[pw_simp]: "is_res (run (Mload a) s) r  \<longleftrightarrow> (case r of (v,i,s') \<Rightarrow> 
    cell.is_valid (mapp s (addr.block a)) 
    \<and> v = cell.vals (mapp s (addr.block a)) (addr.index a)
    \<and> i = intf_r {a}
    \<and> s'=s)
    "
    apply transfer'
    unfolding mload_def
    by pw

  lemma pw_Mstore1[pw_simp]: "run (Mstore a v) s = FAIL \<longleftrightarrow> \<not>cell.is_valid (mapp s (addr.block a))"  
    apply transfer'
    unfolding mstore_def
    by pw
    
  lemma pw_Mstore2[pw_simp]: "is_res (run (Mstore a v) s) r  \<longleftrightarrow> (case r of (_,i,s') \<Rightarrow> 
    cell.is_valid (mapp s (addr.block a)) 
    \<and> i = intf_w {a}
    \<and> s' = mmap s (addr.block a) (\<lambda>VALID vs \<Rightarrow> VALID (vs((addr.index a):=v))))
    "
    apply transfer'
    unfolding mstore_def
    by pw
    
      
subsection \<open>Recursion Setup\<close>    
      
  lift_definition Mbot :: "('r,'v) M" is "\<lambda>_. FAIL"
    by (auto simp: invarM_pw)

  context
  begin
    interpretation FR: flat_rec FAIL .
    
    
    lift_definition Mle :: "('r,'v) M \<Rightarrow> ('r,'v) M \<Rightarrow> bool" 
      is "fun_ord FR.le" .
      
      
    definition "fun_chain \<equiv> Complete_Partial_Order.chain (fun_ord FR.le)"  
    definition "fun_chain' \<equiv> Complete_Partial_Order.chain Mle"  
      
    lemma [transfer_rule]: "(rel_fun (rel_set cr_M) (=)) fun_chain fun_chain'"
      unfolding fun_chain_def fun_chain'_def Complete_Partial_Order.chain_def
      (* TODP: clean up this proof *)
      apply (auto simp: rel_fun_def fun_ord_def rel_set_def)
      apply (metis (full_types) Mle.rep_eq cr_M_def fun_ord_def)
      by (metis (no_types, lifting) Mle.rep_eq cr_M_def fun_ord_def)
      
    
    
    lift_definition Mlub :: "('r,'v) M set \<Rightarrow> ('r,'v) M"
      is "\<lambda>C. if fun_chain C then fun_lub FR.lub C else (\<lambda>_. FAIL)"
      unfolding invarM_pw
      apply rule
      subgoal for C s
        apply (auto simp: FR.fun_lub_apply fun_chain_def)
        apply (drule FR.chain_apply[where x=s])
        apply (erule FR.chain_cases)
        apply auto
        by force
      done
      
    lemma M_ccpo: "class.ccpo Mlub Mle (mk_lt Mle)"
      apply intro_locales
      apply (rule preorder_mk_ltI)
      apply unfold_locales
      
      apply transfer apply (auto simp: fun_ord_def FR.le_def) []
      apply transfer apply (fastforce simp: fun_ord_def FR.le_def) []
      apply transfer apply (auto simp: fun_ord_def FR.le_def fun_eq_iff; metis) [] 
      
      apply (fold fun_chain'_def)
      
      apply transfer
      apply (clarsimp simp: fun_ord_def FR.fun_lub_apply fun_chain_def)
      subgoal for C f s
        apply (drule FR.chain_apply[where x=s])
        apply (erule FR.chain_cases)
        apply (auto simp: FR.le_def)
        done
        
      apply transfer
      apply (clarsimp simp: fun_ord_def FR.fun_lub_apply fun_chain_def)
      subgoal for C f s
        apply (drule FR.chain_apply[where x=s])
        apply (erule FR.chain_cases)
        apply (auto simp: FR.le_def)
        apply force
        apply force
        done
      done
  

    interpretation RS: ccpo Mlub Mle "mk_lt Mle"
      by (rule M_ccpo) 
    interpretation RS: rec_setup Mlub Mle "mk_lt Mle"
      by unfold_locales
      
      
    
    definition "REC \<equiv> RS.REC"
    definition "M_mono \<equiv> RS.fmono"

    definition M_mono' where "M_mono' F \<equiv> \<forall>D D'. fun_ord Mle D D' \<longrightarrow> Mle (F D) (F D')"
    
    lemma M_monoI[mono]: 
      assumes "\<And>x. M_mono' (\<lambda>D. F D x)"
      shows "M_mono F"
      using assms unfolding M_mono'_def M_mono_def Complete_Partial_Order.monotone_def fun_ord_def
      by blast
    
          
    text \<open>Pointwise properties of recursive functions can be proved by well-founded induction 
      on the arguments.\<close>
    lemma REC_wf_induct: 
      assumes WF: "wf V"
      assumes MONO: "M_mono F"
      assumes STEP: "\<And>x D. \<lbrakk>\<And>y. \<lbrakk>(y,x)\<in>V\<rbrakk> \<Longrightarrow> P y (D y) \<rbrakk> \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      using assms unfolding M_mono_def REC_def 
      using RS.REC_wf_induct by metis

    text \<open>For pointwise properties, which hold at non-terminating arguments, we
      can use the following induction scheme, which does not require a well-founded ordering.\<close>
    lemma REC_pointwise_induct: 
      fixes P
      assumes BOT: "\<And>x s. P x s FAIL" 
      assumes STEP: "\<And>D x s. (\<And>y s. P y s (run (D y) s)) \<Longrightarrow> P x s (run (F D x) s)"
      shows "P x s (run (REC F x) s)"
    proof -
      have "\<forall>s. P x s (run (REC F x) s)"
        unfolding REC_def
        supply R = RS.REC_pointwise_induct[where P="\<lambda>x m. \<forall>s. P x s (run m s)"]
        apply (rule R)
        subgoal for x
          apply (transfer fixing: P)
          apply (auto simp: fun_chain_def chain_empty fun_lub_def BOT)
          done
        subgoal for x
          unfolding ccpo.admissible_def fun_chain'_def[symmetric]
          apply (transfer fixing: P)
          apply (clarsimp simp: FR.fun_lub_apply)
          subgoal for x C s
            unfolding fun_chain_def
            apply (drule FR.chain_apply[where x=s])
            apply (erule FR.chain_cases)
            apply (auto simp: FR.le_def BOT) 
            by force
          done
        subgoal using STEP by blast 
        done
      thus ?thesis ..
    qed
      
subsubsection \<open>Monotonicity Prover Setup\<close>      

    qualified lemma Mle_alt: "Mle a b \<longleftrightarrow> (\<forall>s. FR.le (run a s) (run b s))"  
      apply transfer
      by (auto simp: fun_ord_def)
      
    qualified lemma pw_FR_le: "FR.le a b \<longleftrightarrow> a=b \<or> is_fail a"  
      unfolding FR.le_def is_fail_def by auto

    context
      notes [pw_init] = Mle_alt pw_FR_le
    begin  
    
      lemma mono_const[mono]: 
        "M_mono' (\<lambda>_. c)"  
        "M_mono' (\<lambda>D. D y)"
        unfolding M_mono'_def fun_ord_def
        by auto 
        
      lemma mono_If[mono]: "
        M_mono' (\<lambda>D. F D) \<Longrightarrow> M_mono' (\<lambda>D. G D) \<Longrightarrow>
        M_mono' (\<lambda>D. if b then F D else G D)"  
        unfolding M_mono'_def
        by auto
        
      lemma mono_Mbind1: "
        M_mono' (\<lambda>D. F D) \<Longrightarrow> 
        M_mono' (\<lambda>D. Mbind (F D) (G))"  
        unfolding M_mono'_def fun_ord_def Mle_alt
        apply pw' 
        apply (safe; simp; blast)
        done

      lemma mono_Mbind2: "
        (\<And>y. M_mono' (\<lambda>D. G D y)) \<Longrightarrow> 
        M_mono' (\<lambda>D. Mbind F (G D))"  
        unfolding M_mono'_def fun_ord_def Mle_alt
        apply pw
        apply blast
        apply metis
        apply blast
        apply blast
        done
                
      lemma mono_Mbind[mono]: 
        assumes "M_mono' (\<lambda>D. F D)" 
        assumes "\<And>y. M_mono' (\<lambda>D. G D y)"
        shows "M_mono' (\<lambda>D. Mbind (F D) (G D))"  
        using mono_Mbind1[OF assms(1)] mono_Mbind2[of G, OF assms(2)]
        unfolding M_mono'_def
        apply auto
        using RS.order.trans by blast

      lemma mono_Mpar1: "
        M_mono' (\<lambda>D. F D) \<Longrightarrow> 
        M_mono' (\<lambda>D. Mpar (F D) G)"  
        unfolding M_mono'_def fun_ord_def Mle_alt
        apply pw' 
        apply (safe; simp; blast)
        done
        
      lemma mono_Mpar2: "
        M_mono' (\<lambda>D. G D) \<Longrightarrow> 
        M_mono' (\<lambda>D. Mpar F (G D))"  
        unfolding M_mono'_def fun_ord_def Mle_alt
        apply pw' 
        apply (safe; simp; blast)
        done
        
      lemma mono_Mpar[mono]: "
        M_mono' (\<lambda>D. F D) \<Longrightarrow> 
        M_mono' (\<lambda>D. G D) \<Longrightarrow> 
        M_mono' (\<lambda>D. Mpar (F D) (G D))"  
        using mono_Mpar1 mono_Mpar2
        unfolding M_mono'_def
        apply auto
        using RS.order.trans by blast

      lemma mono_REC[mono]: 
        assumes "\<And>D. M_mono (F D)"
        assumes "\<And>DD x. M_mono' (\<lambda>D. F D DD x)"
        shows "M_mono' (\<lambda>D. REC (F D) x)"  
        using assms
        unfolding M_mono'_def REC_def
        apply clarsimp
        subgoal for D D'
          apply (rule RS.REC_mono[of F D D', unfolded fun_ord_def, rule_format])
          subgoal by (simp add: fun_ord_def M_mono_def monotone_def)
          subgoal by blast
          done
        done
        
      lemma mono_case_prod[mono]:
        assumes "\<And>a b. nres_mono' (\<lambda>D. F D a b)"
        shows "nres_mono' (\<lambda>D. case p of (a,b) \<Rightarrow> F D a b)"
        using assms
        unfolding nres_mono'_def fun_ord_def
        apply (cases p) by simp
      
      lemma mono_Let[mono]:
        assumes "\<And>x. nres_mono' (\<lambda>D. F D x)"
        shows "nres_mono' (\<lambda>D. let x=v in F D x)"
        using assms
        unfolding nres_mono'_def fun_ord_def
        by simp
    end          
  end          

  
  subsection \<open>Symmetry of parallel\<close>    
      
  definition "mswap m \<equiv> do\<^sub>n\<^sub>e { ((r\<^sub>1,r\<^sub>2),i,s)\<leftarrow>m; return\<^sub>n\<^sub>e ((r\<^sub>2,r\<^sub>1),i,s) }"  
  
  lemma pw_mswap[pw_simp]:
    "mswap m = FAIL \<longleftrightarrow> is_fail m"
    "is_res (mswap m) ab \<longleftrightarrow> (case ab of ((r\<^sub>1,r\<^sub>2),i,s) \<Rightarrow> is_res m ((r\<^sub>2,r\<^sub>1),i,s))"
    unfolding mswap_def 
    apply pw
    by (cases ab; pw)
    
  lemma ppar_sym: "invarM m\<^sub>1 \<Longrightarrow> invarM m\<^sub>2 \<Longrightarrow> ppar m\<^sub>1 m\<^sub>2 s = mswap (ppar m\<^sub>2 m\<^sub>1 s)"  
    unfolding ppar_def
    apply (cases "m\<^sub>1 s"; cases "m\<^sub>2 s"; simp)
    defer
    apply pw
    apply pw
    apply pw
    subgoal for P\<^sub>1 P\<^sub>2
      apply (subgoal_tac "invarM_pw s (SPEC P\<^sub>1)")
      apply (subgoal_tac "invarM_pw s (SPEC P\<^sub>2)")
      
      apply (thin_tac "invarM _")+
      apply (thin_tac "_=_")+
      subgoal
        apply pw
        using spar_feasible_sym intf_norace_sym
        apply -
        apply (fastforce simp: add.commute intro: combine_states_sym)+
        done
      apply (metis invarM_pw)
      apply (metis invarM_pw)
      done
    done
    
  lemma res_run_consistentI: "is_res (run m s) (x,i,s') \<Longrightarrow> intf_consistent s i s'"  
    using invarM_pw_iff invarM_run by fastforce
        
    
  lemma Mpar_sym: "Mpar m\<^sub>1 m\<^sub>2 = Mbind (Mpar m\<^sub>2 m\<^sub>1) (\<lambda>(r\<^sub>1,r\<^sub>2). Mreturn (r\<^sub>2,r\<^sub>1))"  
    apply pw
    using spar_feasible_sym intf_norace_sym apply blast
    using spar_feasible_sym intf_norace_sym apply blast
    using spar_feasible_sym intf_norace_sym apply blast
    apply (metis (no_types, opaque_lifting) add.commute combine_states_sym spar_feasible_sym res_run_consistentI)
    using spar_feasible_sym intf_norace_sym apply blast
    apply (metis (no_types, opaque_lifting) add.commute combine_states_sym spar_feasible_sym res_run_consistentI)
    done
   
  lifting_update M.lifting  
  lifting_forget M.lifting  
     
end        
            
        
(* TODO:
    can we integrate independence of values not read into consistency?
    \<rightarrow> will change admissibility proof, but should be OK!
    \<rightarrow> will need a simulation relation spanning results, too. As results
      can contain pointers to changed memory layout.
    
        
    use this infrastructure to build LL-monad!
    
*)    
    
