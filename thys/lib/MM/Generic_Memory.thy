theory Generic_Memory
imports NEMonad
begin

  datatype 'v cell = FRESH | FREED | is_valid: VALID (vals: "nat \<Rightarrow> 'v")
  hide_const (open) is_valid vals

  datatype addr = ADDR (block: nat) (index: nat) 
  hide_const (open) block index
  
  class infinite =
    assumes infinite_UNIV[simp,intro!]: "\<not> finite (UNIV :: 'a set)"

  instance nat :: infinite  
    apply standard
    by simp
      
  type_synonym block = nat  
    
  typedef 'v memory = "{ f :: block \<Rightarrow> 'v cell . finite {a. f a \<noteq> FRESH} }" 
    by (auto intro: exI[where x="\<lambda>_. FRESH"])

  setup_lifting type_definition_memory  

  lift_definition mapp :: "'v memory \<Rightarrow> block \<Rightarrow> 'v cell" is "\<lambda>m a. m a" .
  lift_definition mmap :: "'v memory \<Rightarrow> block \<Rightarrow> ('v cell \<Rightarrow> 'v cell) \<Rightarrow> 'v memory" is "\<lambda>m a f. m(a := f (m a))"
  proof goal_cases
    case (1 f a fx)
    thm 1
    have "{aa. (f(a := cell)) aa \<noteq> FRESH} \<subseteq> insert a {a. f a \<noteq> FRESH}" for cell
      by auto
    moreover from 1 have "finite \<dots>" by auto
    ultimately show ?case by (meson finite_subset)
  qed
    
  lemma mapp_mmap[simp]: "mapp (mmap f a g) = (mapp f)(a:=g (mapp f a))"
    apply transfer
    by auto

  lemma mext: "f=f' \<longleftrightarrow> (\<forall>a. mapp f a = mapp f' a)"
    apply transfer
    by auto

  fun cell_combine where
    "cell_combine FRESH I c = c"
  | "cell_combine c I FRESH = c"
  | "cell_combine FREED I c = FREED"
  | "cell_combine c I FREED = FREED"
  | "cell_combine (VALID c\<^sub>1) I (VALID c\<^sub>2) = VALID (\<lambda>i. if i\<in>I then c\<^sub>2 i else c\<^sub>1 i)"
    
  lemma cell_combine_add_simps[simp]:
    "cell_combine c I FRESH = c"
    "cell_combine FREED I c = FREED"
    "cell_combine c I FREED = FREED"
    by (cases c; simp)+
  
  lift_definition mcombine :: "('v) memory \<Rightarrow> (addr set) \<Rightarrow> ('v) memory \<Rightarrow> ('v) memory" is
    "\<lambda>m\<^sub>1 A m\<^sub>2 b. cell_combine (m\<^sub>1 b) {i. ADDR b i \<in> A} (m\<^sub>2 b)"
    subgoal for f\<^sub>1 A f\<^sub>2
    proof goal_cases
      case 1
      
      have "{a. cell_combine (f\<^sub>1 a) {i. ADDR a i \<in> A} (f\<^sub>2 a) \<noteq> FRESH} \<subseteq> {a. f\<^sub>1 a \<noteq> FRESH} \<union> {a. f\<^sub>2 a \<noteq> FRESH}"
        by auto
        
      from finite_subset[OF this] 1 show ?case by simp 
    qed
  done
    
  
  lemma mapp_combine[simp]: "mapp (mcombine m\<^sub>1 A m\<^sub>2) b = cell_combine (mapp m\<^sub>1 b) {i. ADDR b i \<in> A} (mapp m\<^sub>2 b)"
    apply transfer
    by auto  

  lemma finite_non_fresh: "finite {a. mapp f a \<noteq> FRESH}"  
    apply transfer
    .
    
  lemma ex_fresh: "finite A \<Longrightarrow> \<exists>a\<in>-A. mapp m a = FRESH"
    apply transfer
    by (metis (mono_tags, lifting) finite_compl infinite_UNIV rev_finite_subset subset_Collect_conv)
      
    
  definition "cell_state_trans c c' \<equiv> 
    (cell.is_valid c \<longrightarrow> cell.is_valid c' \<or> c'=FREED)
  \<and> (c=FREED \<longrightarrow> c'=FREED)"
    
  lemma cell_state_trans_simps[simp]:
    "cell_state_trans c c"
    "cell_state_trans FRESH c"
    "cell_state_trans c FREED"
    "cell_state_trans (VALID v) c' \<longleftrightarrow> c'\<noteq>FRESH"
    "cell_state_trans FREED c' \<longleftrightarrow> c'=FREED"
    apply (auto simp: cell_state_trans_def)
    by (cases c'; simp)
    
  lemma cell_state_trans_trans[trans]: "cell_state_trans c c' \<Longrightarrow> cell_state_trans c' c'' \<Longrightarrow> cell_state_trans c c''"  
    by (auto simp: cell_state_trans_def)
  
  
  
  definition "alloc_blocks m m' \<equiv> {b . mapp m b = FRESH \<and> mapp m' b \<noteq> FRESH}"
  
  lemma alloc_blocks_same[simp]: "alloc_blocks m m = {}"
    by (auto simp: alloc_blocks_def)
  
  
  datatype interference = interference (r: "addr set") (w: "addr set")
  hide_const (open) r w  
    
  abbreviation "intf_r r \<equiv> interference r {}"
  abbreviation "intf_w w \<equiv> interference {} w"
  
  
  instantiation interference :: comm_monoid_add
  begin
    definition "0 = interference {} {}"
    definition "a+b \<equiv> case (a,b) of (interference ra wa, interference rb wb) \<Rightarrow>
      interference (ra\<union>rb) (wa\<union>wb)"

     instance
       apply standard     
       unfolding zero_interference_def plus_interference_def
       by (auto split: interference.split)
      
  end
  
    
  lemma interference_zero_simps[simp]:  
    "interference.r 0 = {}"  
    "interference.w 0 = {}"  
    by (auto split: interference.split simp: zero_interference_def)
    
  lemma interference_plus_simps[simp]:
    "interference.r (a+b) = interference.r a \<union> interference.r b"  
    "interference.w (a+b) = interference.w a \<union> interference.w b"  
    by (auto split: interference.split simp: plus_interference_def)
  
  
  definition "intf_consistent s i s' \<equiv> 
    let r = interference.r i in
    let w = interference.w i in
      (\<forall>b \<in> addr.block ` (r\<union>w). mapp s' b \<noteq> FRESH)
    \<and> (\<forall>b. cell_state_trans (mapp s b) (mapp s' b))
    \<and> (\<forall>b i. cell.is_valid (mapp s b) \<and> cell.is_valid (mapp s' b) \<and> ADDR b i \<notin> w 
        \<longrightarrow> cell.vals (mapp s' b) i = cell.vals (mapp s b) i)
  "
    
  definition "spar_feasible s s\<^sub>1 s\<^sub>2 \<equiv> alloc_blocks s s\<^sub>1 \<inter> alloc_blocks s s\<^sub>2 = {}"
      
  definition "intf_norace i\<^sub>1 i\<^sub>2 \<equiv> 
    case i\<^sub>1 of (interference r\<^sub>1 w\<^sub>1) \<Rightarrow> 
    case i\<^sub>2 of (interference r\<^sub>2 w\<^sub>2) \<Rightarrow> 
      (r\<^sub>1\<union>w\<^sub>1) \<inter> w\<^sub>2 = {}
    \<and> w\<^sub>1 \<inter> (r\<^sub>2\<union>w\<^sub>2) = {}"
  
  definition "combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2 \<equiv> mcombine s\<^sub>1 (interference.w i\<^sub>2) s\<^sub>2"

  lemma spar_feasible_sym: "spar_feasible s s\<^sub>1 s\<^sub>2 = spar_feasible s s\<^sub>2 s\<^sub>1"  
    by (auto simp: spar_feasible_def)

  lemma intf_norace_sym: "intf_norace i\<^sub>1 i\<^sub>2 = intf_norace i\<^sub>2 i\<^sub>1"  
    by (auto simp: intf_norace_def Let_def split: interference.split)
    
  lemma combine_states_sym: "\<lbrakk>spar_feasible s s\<^sub>1 s\<^sub>2; intf_norace i\<^sub>1 i\<^sub>2; intf_consistent s i\<^sub>1 s\<^sub>1; intf_consistent s i\<^sub>2 s\<^sub>2 \<rbrakk> \<Longrightarrow>
    combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2 = combine_states s\<^sub>2 i\<^sub>1 s\<^sub>1"
    unfolding mext
    apply (rule)
    subgoal for a
      unfolding intf_norace_def intf_consistent_def combine_states_def
      apply (auto split!: interference.splits simp: Let_def)
      apply (cases "mapp s\<^sub>1 a"; cases "mapp s\<^sub>2 a"; simp)
      apply (auto simp: fun_eq_iff)
      unfolding spar_feasible_def alloc_blocks_def disjoint_iff_not_equal
      apply auto 
      by (metis cell.exhaust_disc cell.sel cell.simps(5) cell.simps(7) cell_state_trans_def)
    done  
      
    
  
    
  (*  
      
      
    
  definition "valid_addr m a \<longleftrightarrow> cell.is_valid (mapp m a)"
  
  definition "m_fresh m \<equiv> {a. mapp m a = FRESH }"
  definition "m_freed m \<equiv> {a. mapp m a = FREED }"
  definition "m_valid m \<equiv> {a. cell.is_valid (mapp m a) }"
    
  lemma m_fresh_infinite[simp, intro!]: "infinite (m_fresh m)"
    unfolding m_fresh_def
    apply transfer
    using finite_Collect_not infinite_UNIV by blast
    
    
  datatype ('a,'idx) interference = interference (r: "('a\<times>'idx) set") (w: "('a\<times>'idx) set") (a: "'a set") (f: "'a set")
  hide_const (open) r w a f  
    
  abbreviation "intf_r r \<equiv> interference r {} {} {}"
  abbreviation "intf_w w \<equiv> interference {} w {} {}"
  abbreviation "intf_a a \<equiv> interference {} {} a {}"
  abbreviation "intf_f f \<equiv> interference {} {} {} f"

  instantiation interference :: (type,type) comm_monoid_add
  begin
    definition "0 = interference {} {} {} {}"
    definition "a+b \<equiv> case (a,b) of (interference ra wa aa fa, interference rb wb ab fb) \<Rightarrow>
      interference (ra\<union>rb) (wa\<union>wb) (aa\<union>ab) (fa\<union>fb)"

     instance
       apply standard     
       unfolding zero_interference_def plus_interference_def
       by (auto split: interference.split)
      
  end
  
    
  lemma interference_zero_simps[simp]:  
    "interference.a 0 = {}"  
    "interference.f 0 = {}"  
    "interference.r 0 = {}"  
    "interference.w 0 = {}"  
    by (auto split: interference.split simp: zero_interference_def)
    
  lemma interference_plus_simps[simp]:
    "interference.a (a+b) = interference.a a \<union> interference.a b"  
    "interference.f (a+b) = interference.f a \<union> interference.f b"  
    "interference.r (a+b) = interference.r a \<union> interference.r b"  
    "interference.w (a+b) = interference.w a \<union> interference.w b"  
    by (auto split: interference.split simp: plus_interference_def)
    
  
  text \<open>Over-approximation of everything that was modified: precise written addresses, and everything of allocated or freed blocks\<close>
  definition "intf_modified i \<equiv> case i of (interference rd wr al fr) \<Rightarrow> wr \<union> (al\<union>fr)\<times>UNIV"
    
  definition "intf_compatible i\<^sub>1 i\<^sub>2 \<equiv> interference.a i\<^sub>1 \<inter> interference.a i\<^sub>2 = {}"
  
  definition "intf_nointer i\<^sub>1 i\<^sub>2 \<equiv> 
    let m\<^sub>1 = intf_modified i\<^sub>1 in
    let m\<^sub>2 = intf_modified i\<^sub>2 in
    let r\<^sub>1 = interference.r i\<^sub>1 in
    let r\<^sub>2 = interference.r i\<^sub>2 in
      (r\<^sub>1 \<union> m\<^sub>1) \<inter> m\<^sub>2 = {}
    \<and> m\<^sub>1 \<inter> (r\<^sub>2\<union>m\<^sub>2) = {}
  "
  
  (*
  definition "intf_nointer i\<^sub>1 i\<^sub>2 \<equiv> case (i\<^sub>1,i\<^sub>2) of (interference r\<^sub>1 w\<^sub>1 a\<^sub>1 f\<^sub>1, interference r\<^sub>2 w\<^sub>2 a\<^sub>2 f\<^sub>2) \<Rightarrow>
    let ww\<^sub>1 = w\<^sub>1 \<union> a\<^sub>1 \<union> f\<^sub>1 in
    let ww\<^sub>2 = w\<^sub>2 \<union> a\<^sub>2 \<union> f\<^sub>2 in
      (r\<^sub>1 \<union> ww\<^sub>1) \<inter> ww\<^sub>2 = {}
    \<and> ww\<^sub>1 \<inter> (r\<^sub>2\<union>ww\<^sub>2) = {}
  "
  *)
   
  definition "intf_consistent s i s' \<equiv> case i of (interference rd wr al fr) \<Rightarrow>
    (finite (al\<union>fr))  
  \<and> (\<forall>a\<in>-(wr\<union>al\<union>fr). mapp s a = mapp s' a)
  \<and> (\<forall>a\<in>fr. mapp s a \<noteq> FREED \<and> mapp s' a = FREED)
  \<and> (\<forall>a\<in>al. mapp s a = FRESH)
  \<and> (\<forall>a\<in>(rd\<union>wr)-fr. cell.is_valid (mapp s' a))  
  \<and> (\<forall>a\<in>(rd\<union>wr)-al. cell.is_valid (mapp s a))
  "  

  definition "combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2 \<equiv> mcombine s\<^sub>1 (intf_modified i\<^sub>2) s\<^sub>2"

  lemma intf_compatible_sym: "intf_compatible i\<^sub>1 i\<^sub>2 = intf_compatible i\<^sub>2 i\<^sub>1"  
    by (auto simp: intf_compatible_def)

  lemma intf_nointer_sym: "intf_nointer i\<^sub>1 i\<^sub>2 = intf_nointer i\<^sub>2 i\<^sub>1"  
    by (auto simp: intf_nointer_def Let_def split: interference.split)
  
  lemma combine_states_sym: "intf_nointer i\<^sub>1 i\<^sub>2 \<Longrightarrow> intf_consistent s i\<^sub>1 s\<^sub>1 \<Longrightarrow> intf_consistent s i\<^sub>2 s\<^sub>2 \<Longrightarrow>
    combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2 = combine_states s\<^sub>2 i\<^sub>1 s\<^sub>1"
    unfolding intf_nointer_def intf_consistent_def combine_states_def mext intf_modified_def
    apply (auto split!: interference.splits simp: Let_def)
    by (metis Compl_iff Un_iff boolean_algebra.de_Morgan_disj inter_compl_diff_conv)
  
  *)
  

end
