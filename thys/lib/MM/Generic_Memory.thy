section \<open>Memory Model\<close>
theory Generic_Memory
imports NEMonad
begin
  subsection \<open>Miscellaneous\<close>
  definition "i_nth xs i \<equiv> if i\<in>{0..<int (length xs)} then xs!nat i else undefined"  
  definition "i_upd xs i x \<equiv> if i\<in>{0..<int (length xs)} then xs[nat i:=x] else xs"
        
  lemma i_nth_simp[simp]: 
    "0\<le>i \<Longrightarrow> nat i < length xs \<Longrightarrow> i_nth xs i = xs!nat i"
    "i<0 \<Longrightarrow> i_nth xs i = undefined"
    "length xs \<le> nat i \<Longrightarrow> i_nth xs i = undefined"
    by (auto simp: i_nth_def)
  
  lemma i_upd_simp[simp]: 
    "0\<le>i \<Longrightarrow> nat i < length xs \<Longrightarrow> i_upd xs i v = xs[nat i:=v]"
    "i<0 \<Longrightarrow> i_upd xs i v = xs"
    "length xs \<le> nat i \<Longrightarrow> i_upd xs i v = xs"
    "length (i_upd xs i v) = length xs"
    by (auto simp: i_upd_def)
    
  lemma i_get_upd_lens_laws[simp]:  
    "0\<le>i \<Longrightarrow> nat i<length xs \<Longrightarrow> i_nth (i_upd xs i x) i= x"
    "i_upd xs i (i_nth xs i) = xs"
    "i_upd (i_upd xs i y) i x = i_upd xs i x"
    "i\<noteq>j \<Longrightarrow> i_nth (i_upd xs i x) j = i_nth xs j"
    by (auto simp: i_upd_def i_nth_def)
    

  definition list_combine where
    "list_combine xs\<^sub>1 I xs\<^sub>2 \<equiv> map (\<lambda>i. if i\<in>I then xs\<^sub>2!i else xs\<^sub>1!i) [0..<length xs\<^sub>1 ]"
    
  lemma nth_undefined: "\<not>i<length xs \<Longrightarrow> xs!i = undefined (i-length xs)"
    apply (induction xs arbitrary: i)
    apply (simp add: nth_def)
    by auto
    
  lemma list_combine_nth: "length xs\<^sub>1 = length xs\<^sub>2 \<Longrightarrow> list_combine xs\<^sub>1 I xs\<^sub>2 ! i = (if i\<in>I then xs\<^sub>2!i else xs\<^sub>1!i)"  
    unfolding list_combine_def
    apply (cases "i<length xs\<^sub>2")
    subgoal by (auto simp: )
    subgoal by (simp add: nth_undefined)
    done

  lemma list_combine_length[simp]: "length (list_combine xs\<^sub>1 I xs\<^sub>2) = length xs\<^sub>1"  
    by (auto simp: list_combine_def)
    
  lemma list_combine_inth: "length xs\<^sub>1 = length xs\<^sub>2 \<Longrightarrow> i_nth (list_combine xs\<^sub>1 I xs\<^sub>2) i = (if nat i\<in>I then i_nth xs\<^sub>2 i else i_nth xs\<^sub>1 i)"  
    apply (cases "0\<le>i"; simp)
    apply (cases "nat i < length xs\<^sub>1"; auto simp: list_combine_nth)
    done
    

  subsection \<open>Memory Type Definition\<close>
  text \<open>We define the memory model abstracted over the value type first.
    Only later, we instantiate the value type with LLVM specific values
  \<close>
  
  datatype 'v block = FRESH | FREED | is_alloc: ALLOC (vals: "'v list")
  hide_const (open) is_alloc vals

  text \<open>For technical reasons, we use integers as indexes. These are, however, always positive.\<close>
  datatype addr = ADDR (block: nat) (index: int) 
  hide_const (open) block index
  
  class infinite =
    assumes infinite_UNIV[simp,intro!]: "\<not> finite (UNIV :: 'a set)"

  instance nat :: infinite  
    apply standard
    by simp
      
  type_synonym block_idx = nat  
    
  typedef 'v memory = "{ f :: block_idx \<Rightarrow> 'v block . finite {a. f a \<noteq> FRESH} }" 
    by (auto intro: exI[where x="\<lambda>_. FRESH"])

  setup_lifting type_definition_memory  

  text \<open>We define a get (mapp) and map (mmap) function for blocks of memory. 
    These will be used as the only interface to the memory type from now on.\<close>
  
  lift_definition mapp :: "'v memory \<Rightarrow> block_idx \<Rightarrow> 'v block" is "\<lambda>m a. m a" .
  lift_definition mmap :: "'v memory \<Rightarrow> block_idx \<Rightarrow> ('v block \<Rightarrow> 'v block) \<Rightarrow> 'v memory" is "\<lambda>m a f. m(a := f (m a))"
  proof goal_cases
    case (1 f a fx)
    thm 1
    have "{aa. (f(a := block)) aa \<noteq> FRESH} \<subseteq> insert a {a. f a \<noteq> FRESH}" for block
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

  subsection \<open>Block State\<close>  
    
  definition "block_size m b \<equiv> case mapp m b of 
    ALLOC vs \<Rightarrow> length vs
  | _ \<Rightarrow> 0"

  abbreviation "is_FRESH m b \<equiv> mapp m b = FRESH"  
  abbreviation "is_ALLOC m b \<equiv> block.is_alloc (mapp m b)"  
  abbreviation "is_FREED m b \<equiv> mapp m b = FREED"  

  lemma block_size_noblock[simp]:
    "is_FRESH m b \<Longrightarrow> block_size m b = 0"
    "is_FREED m b \<Longrightarrow> block_size m b = 0"
    "\<not>is_ALLOC m b \<Longrightarrow> block_size m b = 0"
    by (auto simp: block_size_def split: block.splits)
    
  lemma is_ALLOC_conv: "is_ALLOC s b \<longleftrightarrow> \<not>is_FREED s b \<and> \<not>is_FRESH s b"  
    apply auto
    using block.exhaust_disc by blast
    
  lemma is_block_state_simps: 
    "is_FREED s b \<Longrightarrow> \<not>is_ALLOC s b \<and> \<not>is_FRESH s b"
    "is_FRESH s b \<Longrightarrow> \<not>is_ALLOC s b \<and> \<not>is_FREED s b"
    by (auto)
      
  subsection \<open>Accessing Memory via Addresses\<close>  
    
  definition "get_addr m a \<equiv> 
    case a of ADDR b i \<Rightarrow> i_nth (block.vals (mapp m b)) i
  "  
    
  text \<open>The \<open>put\<close> function is closed to do nothing on invalid addresses. 
    This removes a lot of side-conditions from the lens laws below, 
    making them simpler to reason with.\<close>
  definition "put_addr m a x \<equiv> 
    case a of ADDR b i \<Rightarrow> mmap m b (\<lambda>ALLOC vs \<Rightarrow> ALLOC (i_upd vs i x) | c \<Rightarrow> c )
  "

  lemma block_size_put[simp]:
    "block_size (put_addr m a x) b = block_size m b"
    unfolding block_size_def put_addr_def 
    by (auto split: addr.splits block.splits simp: mext)
  
  lemma addr_put_get[simp]: "put_addr m a (get_addr m a) = m"
    and addr_put_put[simp]: "put_addr (put_addr m a y) a x = put_addr m a x"
    unfolding get_addr_def put_addr_def 
    by (auto split: addr.splits block.splits simp: mext)
    
    
  definition "is_valid_addr m a \<equiv> 
    case a of ADDR b i \<Rightarrow> 0\<le>i \<and> nat i < block_size m b"  
    
  lemma is_valid_addr_alt: "is_valid_addr m a = (case a of ADDR b i \<Rightarrow> is_ALLOC m b \<and> 0\<le>i \<and> nat i < block_size m b)"  
    by (auto simp: is_valid_addr_def block_size_def split: addr.splits block.split)

  definition "is_valid_ptr_addr m a \<equiv> 
    case a of ADDR b i \<Rightarrow> is_ALLOC m b \<and> 0\<le>i \<and> nat i \<le> block_size m b"  
    
          
  text \<open>Lens laws\<close>  
  lemma addr_get_put[simp]: "is_valid_addr m a \<Longrightarrow> get_addr (put_addr m a x) a = x"
    and addr_put_valid[simp]: "is_valid_addr (put_addr m a x) a' \<longleftrightarrow> is_valid_addr m a'"
    and addr_put_ptr_valid[simp]: "is_valid_ptr_addr (put_addr m a x) a' \<longleftrightarrow> is_valid_ptr_addr m a'"
    unfolding is_valid_addr_def is_valid_ptr_addr_def block_size_def get_addr_def put_addr_def
    by (auto split: addr.splits block.splits)
    
  lemma addr_indep[simp]: "\<lbrakk> is_valid_addr m a\<^sub>1; is_valid_addr m a\<^sub>2; a\<^sub>1\<noteq>a\<^sub>2\<rbrakk> \<Longrightarrow> get_addr (put_addr m a\<^sub>1 x) a\<^sub>2 = get_addr m a\<^sub>2"    
    unfolding is_valid_addr_def get_addr_def put_addr_def 
    by (auto split: addr.splits block.splits simp: mext nth_list_update')
  
  subsection \<open>Allocating and Freeing\<close>  
  definition "addr_alloc vs b m \<equiv> mmap m b (\<lambda>_. ALLOC vs)"  
  definition "addr_free b m \<equiv> mmap m b (\<lambda>_. FREED)"  

  lemma addr_alloc_state[simp]:
    "is_FRESH (addr_alloc vs b m) b' \<longleftrightarrow> b'\<noteq>b \<and> is_FRESH m b'"  
    "is_ALLOC (addr_alloc vs b m) b' \<longleftrightarrow> b'=b \<or> is_ALLOC m b'"  
    "is_FREED (addr_alloc vs b m) b' \<longleftrightarrow> b'\<noteq>b \<and> is_FREED m b'"
    by (auto simp: addr_alloc_def)
    
  lemma addr_free_state[simp]:
    "is_FRESH (addr_free b m) b' \<longleftrightarrow> b'\<noteq>b \<and> is_FRESH m b'"  
    "is_ALLOC (addr_free b m) b' \<longleftrightarrow> b'\<noteq>b \<and> is_ALLOC m b'"  
    "is_FREED (addr_free b m) b' \<longleftrightarrow> b'=b \<or> is_FREED m b'"
    by (auto simp: addr_free_def)
    
  lemma put_addr_state[simp]:
    "is_FRESH (put_addr m a x) b' \<longleftrightarrow> is_FRESH m b'"  
    "is_ALLOC (put_addr m a x) b' \<longleftrightarrow> is_ALLOC m b'"  
    "is_FREED (put_addr m a x) b' \<longleftrightarrow> is_FREED m b'"
    by (auto simp: put_addr_def split: addr.splits block.splits)
    
    
  
      
  lemma bs_alloc[simp]: "block_size (addr_alloc vs b m) b' = (if b=b' then length vs else block_size m b')"
    by (auto simp: block_size_def addr_alloc_def)
  
  lemma bs_free[simp]: "block_size (addr_free b m) b' = (if b=b' then 0 else block_size m b')"
    by (auto simp: block_size_def addr_free_def)
    
  lemma get_addr_alloc[simp]: "get_addr (addr_alloc vs b m) a = (if addr.block a = b then i_nth vs (addr.index a) else get_addr m a)"
    by (cases a; auto simp: get_addr_def addr_alloc_def)
    
  lemma valid_addr_alloc[simp]: "is_valid_addr (addr_alloc vs b m) a = (if addr.block a = b then 0\<le>addr.index a \<and> nat (addr.index a) < length vs else is_valid_addr m a)"
    by (cases a; auto simp: is_valid_addr_def)

  lemma valid_ptr_addr_alloc[simp]: "is_valid_ptr_addr (addr_alloc vs b m) a = (if addr.block a = b then 0\<le>addr.index a \<and> nat (addr.index a) \<le> length vs else is_valid_ptr_addr m a)"
    by (cases a; auto simp: is_valid_ptr_addr_def)
        
  lemma get_addr_free[simp]: "addr.block a \<noteq> b \<Longrightarrow> get_addr (addr_free b m) a = get_addr m a"
    by (cases a; auto simp: get_addr_def addr_free_def)
    
  lemma valid_addr_free[simp]: 
    "is_valid_addr (addr_free b m) a = (addr.block a \<noteq> b \<and> is_valid_addr m a)"
    "is_valid_ptr_addr (addr_free b m) a = (addr.block a \<noteq> b \<and> is_valid_ptr_addr m a)"
    by (cases a; auto simp: is_valid_addr_def is_valid_ptr_addr_def)+
    
  subsection \<open>Combining Memories\<close>  
  text \<open>The definition of the raw combine operator is asymmetric,
    using the first memory by default, except for some specified blocks and addresses.
    Symmetry is only proved later, when we know that the combined memories have actually evolved by
    consistent, race-free executions.
  \<close>
    
  fun block_combine where
    "block_combine FRESH I c = c"
  | "block_combine c I FRESH = c"
  | "block_combine FREED I c = FREED"
  | "block_combine c I FREED = FREED"
  | "block_combine (ALLOC vs\<^sub>1) I (ALLOC vs\<^sub>2) = ALLOC (list_combine vs\<^sub>1 I vs\<^sub>2)"
    
  lemma block_combine_add_simps[simp]:
    "block_combine c I FRESH = c"
    "block_combine FREED I c = FREED"
    "block_combine c I FREED = FREED"
    by (cases c; simp)+
  
  lift_definition mcombine :: "('v) memory \<Rightarrow> (addr set) \<Rightarrow> ('v) memory \<Rightarrow> ('v) memory" is
    "\<lambda>m\<^sub>1 A m\<^sub>2 b. block_combine (m\<^sub>1 b) { nat i | i. 0\<le>i \<and> ADDR b i \<in> A} (m\<^sub>2 b)"
    subgoal for f\<^sub>1 A f\<^sub>2
    proof goal_cases
      case 1
      
      have "{b. block_combine (f\<^sub>1 b) {nat i | i. 0\<le>i \<and> ADDR b i \<in> A} (f\<^sub>2 b) \<noteq> FRESH} \<subseteq> {a. f\<^sub>1 a \<noteq> FRESH} \<union> {a. f\<^sub>2 a \<noteq> FRESH}"
        by auto
        
      from finite_subset[OF this] 1 show ?case by auto
    qed
  done
    
  
  lemma mapp_combine[simp]: "mapp (mcombine m\<^sub>1 A m\<^sub>2) b = block_combine (mapp m\<^sub>1 b) { nat i | i. 0\<le>i \<and> ADDR b i \<in> A} (mapp m\<^sub>2 b)"
    apply transfer
    by auto  

  lemma finite_non_fresh: "finite {a. mapp f a \<noteq> FRESH}"  
    apply transfer
    .
    
  lemma ex_fresh: "finite A \<Longrightarrow> \<exists>a\<in>-A. mapp m a = FRESH"
    apply transfer
    by (metis (mono_tags, lifting) finite_compl infinite_UNIV rev_finite_subset subset_Collect_conv)
      

  subsection \<open>Valid State Transitions of Memory Blocks\<close>  
  text \<open>Blocks can only transition from fresh to allocated to freed, and 
    allocated blocks cannot change their size.
  \<close>
  
  definition "block_state_trans c c' \<equiv> 
    (block.is_alloc c \<longrightarrow> (block.is_alloc c' \<and> length (block.vals c') = length (block.vals c)) \<or> c'=FREED)
  \<and> (c=FREED \<longrightarrow> c'=FREED)"

      
  (* Alternative characterization: *)  
  inductive block_state_trans1 where
    "block_state_trans1 FRESH (ALLOC vs)" 
  | "length vs' = length vs \<Longrightarrow> block_state_trans1 (ALLOC vs) (ALLOC vs')" 
  | "block_state_trans1 (ALLOC vs) FREED"
    
  (* TODO: Move *)  
  lemma r2_into_rtranclp: "P a b \<Longrightarrow> P b c \<Longrightarrow> P\<^sup>*\<^sup>* a c" by auto
    
  lemma block_state_trans_alt: "block_state_trans c c' = block_state_trans1\<^sup>*\<^sup>* c c'"
  proof
    show "block_state_trans1\<^sup>*\<^sup>* c c' \<Longrightarrow> block_state_trans c c'"
      apply (induction rule: rtranclp.induct)
      unfolding block_state_trans_def
      by (auto elim: block_state_trans1.cases)
  
    show "block_state_trans c c' \<Longrightarrow> block_state_trans1\<^sup>*\<^sup>* c c'"  
      unfolding block_state_trans_def
      apply (cases c; cases c'; simp)
      apply (auto intro: r2_into_rtranclp block_state_trans1.intros)
      done
    
  qed    
  
  lemma block_state_trans_simps[simp]:
    "block_state_trans c c"
    "block_state_trans FRESH c"
    "block_state_trans c FREED"
    "block_state_trans (ALLOC vs) (ALLOC vs') \<longleftrightarrow> length vs' = length vs"
    "block_state_trans FREED c' \<longleftrightarrow> c'=FREED"
    by (auto simp: block_state_trans_def)
  
      
  lemma block_state_trans_trans[trans]: "block_state_trans c c' \<Longrightarrow> block_state_trans c' c'' \<Longrightarrow> block_state_trans c c''"  
    by (auto simp: block_state_trans_def)
  
  
  definition "valid_block_trans m m' b \<equiv> 
      (is_ALLOC m b \<longrightarrow> (is_ALLOC m' b \<and> block_size m' b = block_size m b) \<or> is_FREED m' b)
    \<and> (is_FREED m b \<longrightarrow> is_FREED m' b)"  
    
  lemma valid_block_trans_alt: "valid_block_trans m m' b \<longleftrightarrow> block_state_trans (mapp m b) (mapp m' b)"  
    unfolding valid_block_trans_def block_state_trans_def block_size_def
    by (auto split: block.split)
    

  lemma valid_block_trans_refl[simp]:
    "valid_block_trans m m b"
    by (auto simp: valid_block_trans_def)
  
      
  lemma valid_block_trans_trans[trans]: "valid_block_trans c c' b \<Longrightarrow> valid_block_trans c' c'' b \<Longrightarrow> valid_block_trans c c'' b"  
    unfolding valid_block_trans_def
    by (auto simp: valid_block_trans_def)
    
    
  lemma valid_block_trans_alloc[simp]: "is_FRESH m b \<Longrightarrow> valid_block_trans m (addr_alloc vs b m) b'"  
    by (auto simp: valid_block_trans_def)
    
  lemma valid_block_trans_free[simp]: "is_ALLOC m b \<Longrightarrow> valid_block_trans m (addr_free b m) b'"  
    by (auto simp: valid_block_trans_def)
    
  lemma valid_block_trans_put[simp]: "valid_block_trans m (put_addr m a x) b'"  
    by (auto simp: valid_block_trans_def)
    
          
  text \<open>Blocks allocated (and potentially freed again) in execution from \<open>m\<close> to \<open>m'\<close> \<close>
  definition "alloc_blocks m m' \<equiv> {b . is_FRESH m b \<and> \<not>is_FRESH m' b}"

  text \<open>Blocks freed in execution from \<open>m\<close> to \<open>m'\<close> \<close>
  definition "freed_blocks m m' \<equiv> {b . \<not>is_FREED m b \<and> is_FREED m' b}"
  
    
  lemma alloc_blocks_refl[simp]: "alloc_blocks m m = {}"
    by (auto simp: alloc_blocks_def)

  lemma freed_blocks_refl[simp]: "freed_blocks m m = {}"
    by (auto simp: freed_blocks_def)
      

  subsection \<open>Access Reports\<close>
      
  datatype acc = ACC_REPORT 
    (r: "addr set")   \<comment> \<open>Read addresses\<close>
    (w: "addr set")   \<comment> \<open>Written addresses\<close>
    (a: "block_idx set")  \<comment> \<open>Allocated blocks\<close>
    (f: "block_idx set")  \<comment> \<open>Freed blocks\<close>
    
  hide_const (open) r w a f
    
  abbreviation "acc_r r \<equiv> ACC_REPORT {r} {} {} {}" 
  abbreviation "acc_w w \<equiv> ACC_REPORT {} {w} {} {}" 
  abbreviation "acc_a a \<equiv> ACC_REPORT {} {}  {a} {}" 
  abbreviation "acc_f f \<equiv> ACC_REPORT {} {}  {} {f}" 
  
  
  instantiation acc :: comm_monoid_add
  begin
    definition "0 = ACC_REPORT {} {} {} {}"
    definition "a+b \<equiv> case (a,b) of (ACC_REPORT ra wa aa fa, ACC_REPORT rb wb ab fb) \<Rightarrow>
      ACC_REPORT (ra\<union>rb) (wa\<union>wb) (aa\<union>ab) (fa\<union>fb)"

     instance
       apply standard     
       unfolding zero_acc_def plus_acc_def
       by (auto split: acc.split)
      
  end
  
    
  lemma acc_zero_simps[simp]:  
    "acc.r 0 = {}"  
    "acc.w 0 = {}"  
    "acc.a 0 = {}"  
    "acc.f 0 = {}"  
    by (auto split: acc.split simp: zero_acc_def)
    
  lemma acc_plus_simps[simp]:
    "acc.r (a+b) = acc.r a \<union> acc.r b"  
    "acc.w (a+b) = acc.w a \<union> acc.w b"  
    "acc.a (a+b) = acc.a a \<union> acc.a b"  
    "acc.f (a+b) = acc.f a \<union> acc.f b"  
    by (auto split: acc.split simp: plus_acc_def)
  
  abbreviation "split_acc i \<equiv> (
    acc.r i, 
    acc.w i, 
    acc.a i, 
    acc.f i
  )"
  

  subsubsection \<open>Consistency with Memory Change\<close>
  text \<open>Reported ACC_REPORT is consistent with observable state change. 
    Also includes that state change itself is consistent.\<close>
  definition "acc_consistent s i s' \<equiv> 
    let (r,w,a,f) = split_acc i in
      \<comment> \<open>Referred to blocks must exist or have existed in final state, and cannot be freed in initial state\<close>
      (\<forall>b \<in> addr.block`(r\<union>w) \<union> a \<union> f. \<not>is_FRESH s' b \<and> \<not>is_FREED s b) 
      \<comment> \<open>Read and written addresses must be valid\<close>
    \<and> (\<forall>addr\<in>r\<union>w. is_ALLOC s (addr.block addr) \<longrightarrow> is_valid_addr s addr)  
    \<and> (\<forall>addr\<in>r\<union>w. is_ALLOC s' (addr.block addr) \<longrightarrow> is_valid_addr s' addr)  
      \<comment> \<open>Cell state makes valid transitions only\<close>
    \<and> (\<forall>b. valid_block_trans s s' b)
      \<comment> \<open>Allocated and freed blocks consistent with state transition\<close>
    \<and> a = alloc_blocks s s' 
    \<and> f = freed_blocks s s'
    
      \<comment> \<open>Addresses not freed nor written must be unchanged\<close>
    \<and> (\<forall>a. is_valid_addr s a \<and> is_valid_addr s' a \<and> a\<notin>w \<longrightarrow> get_addr s a = get_addr s' a)
  "

  text \<open>For convenience, we define locales for consistent executions\<close>
  locale acc_consistent_loc =
    fixes s i s'
    assumes consistent: "acc_consistent s i s'"
  begin
    abbreviation "r \<equiv> acc.r i"
    abbreviation "w \<equiv> acc.w i"
    abbreviation "a \<equiv> acc.a i"
    abbreviation "f \<equiv> acc.f i"
    abbreviation "m \<equiv> acc.w i \<union> {addr. addr.block addr \<in> f}"

    
    abbreviation "allocated_addrs_approx \<equiv> {addr. addr.block addr \<in> a}"
    abbreviation "freed_addrs_approx \<equiv> {addr. addr.block addr \<in> f}"
    
    
    lemma valid_block_trans: 
      "valid_block_trans s s' b"
      using consistent unfolding acc_consistent_def by auto
  
    lemma acc_a_alloc: 
      "a = alloc_blocks s s'"  
      using consistent unfolding acc_consistent_def by auto
      
    lemma acc_f_freed: 
      "f = freed_blocks s s'"  
      using consistent unfolding acc_consistent_def by auto
      
    lemma acc_ref_not_fresh:  
      "b\<in>addr.block ` (r \<union> w) \<union> a \<union> f \<Longrightarrow> mapp s' b \<noteq> FRESH"
      using consistent unfolding acc_consistent_def by auto

    lemma acc_ref_not_freed:  
      "b\<in>addr.block ` (r \<union> w) \<union> a \<union> f \<Longrightarrow> mapp s b \<noteq> FREED"
      using consistent unfolding acc_consistent_def by auto
          
    lemma acc_nw_untouched:  
      "is_valid_addr s addr \<Longrightarrow> is_valid_addr s' addr \<Longrightarrow> addr \<notin> w \<Longrightarrow> get_addr s' addr = get_addr s addr"
      using consistent unfolding acc_consistent_def by auto

    lemma valid_if_not_freed: "is_valid_addr s addr \<Longrightarrow> addr.block addr \<notin> f \<Longrightarrow> is_valid_addr s' addr"
      apply (cases addr; clarsimp)
      subgoal for b i
        using valid_block_trans[of b]
        unfolding is_valid_addr_def valid_block_trans_def
        by (auto simp: acc_f_freed freed_blocks_def)
      done

    lemma rw_valid_s:  
      "addr\<in>r\<union>w \<Longrightarrow> is_ALLOC s (addr.block addr) \<Longrightarrow> is_valid_addr s addr"
      using consistent unfolding acc_consistent_def by auto
    
    lemma rw_valid_s':  
      "addr\<in>r\<union>w \<Longrightarrow> is_ALLOC s' (addr.block addr) \<Longrightarrow> is_valid_addr s' addr"
      using consistent unfolding acc_consistent_def by auto
    
            
    lemma addr_orig_val: "is_valid_addr s addr \<Longrightarrow> addr.block addr \<notin> f \<Longrightarrow> addr\<notin>w 
      \<Longrightarrow> is_valid_addr s' addr \<and> get_addr s' addr = get_addr s addr"
      using acc_nw_untouched valid_if_not_freed by blast
      
    lemma valid_trans_imps:
      "is_FREED s b \<Longrightarrow> is_FREED s' b"  
      "is_ALLOC s b \<Longrightarrow> is_ALLOC s' b \<or> is_FREED s' b"  
      "is_FRESH s' b \<Longrightarrow> is_FRESH s b"  
      using valid_block_trans[of b]
      apply (auto simp: valid_block_trans_def)
      using block.exhaust_disc by blast
      

    lemma is_ALLOC'_eq: "is_ALLOC s' b \<longleftrightarrow> b\<notin>f \<and> (is_ALLOC s b \<or> b \<in> a)"  
      unfolding acc_a_alloc acc_f_freed alloc_blocks_def freed_blocks_def
      apply simp
      by (metis block.disc(2) block.exhaust_disc valid_trans_imps(1) valid_trans_imps(2))
      
    lemma is_FRESH'_eq: "is_FRESH s' b \<longleftrightarrow> b\<notin>a \<and> is_FRESH s b"  
      unfolding acc_a_alloc acc_f_freed alloc_blocks_def freed_blocks_def
      apply simp
      using valid_trans_imps(3) by blast
      
    lemma is_FREED'_eq: "is_FREED s' b \<longleftrightarrow> is_FREED s b \<or> b\<in>f"  
      unfolding acc_a_alloc acc_f_freed alloc_blocks_def freed_blocks_def
      apply simp
      using valid_trans_imps(1) by blast
      

    lemma rw_valid_or_alloc: "r\<union>w \<subseteq> Collect (is_valid_addr s) \<union> {addr. addr.block addr \<in> a}" 
      apply rule
      subgoal for addr
    proof (cases addr)
      case [simp]: (ADDR b i)
      
      assume A: "addr \<in> r \<union> w"
      
      with acc_ref_not_freed[of b] acc_ref_not_fresh[of b] 
      have "\<not>is_FREED s b" "\<not>is_FRESH s' b" by force+
      hence "b\<in>a \<or> is_ALLOC s b" 
        by (auto simp: is_FRESH'_eq is_ALLOC_conv)
      
      then show ?thesis using rw_valid_s[OF A] by auto
    qed done

    lemma f_valid_or_alloc: "f \<subseteq> Collect (is_ALLOC s) \<union> a"
      by (smt (verit, del_insts) Collect_mono_iff UnI2 freed_blocks_def acc_f_freed is_ALLOC_conv is_FRESH'_eq mem_Collect_eq sup_ge1 sup_set_def)
    
    lemma a_dj_alloc: "Collect (is_ALLOC s) \<inter> a = {}"  
      unfolding acc_a_alloc alloc_blocks_def
      by (auto)
          
    lemma a_dj_valid: "Collect (is_valid_addr s) \<inter> {addr. addr.block addr \<in> a} = {}"  
      using a_dj_alloc unfolding is_valid_addr_alt
      by (auto split: addr.splits)
      
    lemma valid_addrs'_subset: "Collect (is_valid_addr s') \<subseteq> Collect (is_valid_addr s) \<union> allocated_addrs_approx"
      apply (auto simp: acc_a_alloc)
      by (smt addr.case_eq_if block.disc(2) acc_a_alloc is_ALLOC'_eq 
              valid_block_trans  is_valid_addr_alt valid_block_trans_def)
      
    definition "allocated_addrs \<equiv> Collect (is_valid_addr s') - Collect (is_valid_addr s)"      
    definition "freed_addrs \<equiv> Collect (is_valid_addr s) - Collect (is_valid_addr s')"      
              
    lemma valid_s_not_alloc: "Collect (is_valid_addr s) \<inter> allocated_addrs = {}" 
      unfolding allocated_addrs_def by blast

    lemma valid_s'_not_freed: "Collect (is_valid_addr s') \<inter> freed_addrs = {}" 
      unfolding freed_addrs_def by blast
      
    lemma alloc_valid_s': "allocated_addrs \<subseteq> Collect (is_valid_addr s')" 
      unfolding allocated_addrs_def by blast

    lemma freed_valid_s: "freed_addrs \<subseteq> Collect (is_valid_addr s)" 
      unfolding freed_addrs_def by blast
      
    lemma alloc_dj_freed: "allocated_addrs \<inter> freed_addrs = {}"  
      unfolding freed_addrs_def allocated_addrs_def by blast
          
    lemma valid_s'_alt: "Collect (is_valid_addr s') = Collect (is_valid_addr s) - freed_addrs \<union> allocated_addrs"
      unfolding allocated_addrs_def freed_addrs_def by auto
              
    lemma valid_s'_alt': "Collect (is_valid_addr s') = (Collect (is_valid_addr s) \<union> allocated_addrs) - freed_addrs "
      unfolding allocated_addrs_def freed_addrs_def by auto
      
    (* Interference related to alloc/valid *)  
      
    lemma allocated_addrs_approx: "allocated_addrs \<subseteq> allocated_addrs_approx"
      by (simp add: Diff_subset_conv allocated_addrs_def valid_addrs'_subset)
    
    lemma freed_addrs_approx: "freed_addrs \<subseteq> freed_addrs_approx"
      using freed_addrs_def valid_if_not_freed by fastforce
      

    lemma f_dj_valid: "Collect (is_valid_addr s') \<inter> freed_addrs_approx = {}"  
      by (metis (no_types, lifting) addr.case_eq_if disjoint_iff is_ALLOC'_eq is_valid_addr_alt mem_Collect_eq)
      
            
  end  

  text \<open>Consistency is transitive\<close>    
  lemma acc_consistent_trans:  
    assumes "acc_consistent s i\<^sub>1 s\<^sub>1" 
    assumes "acc_consistent s\<^sub>1 i\<^sub>2 s\<^sub>2"  
    shows "acc_consistent s (i\<^sub>1 + i\<^sub>2) s\<^sub>2"
  proof -
    interpret c1: acc_consistent_loc s i\<^sub>1 s\<^sub>1 by unfold_locales fact
    interpret c2: acc_consistent_loc s\<^sub>1 i\<^sub>2 s\<^sub>2 by unfold_locales fact
  
    show ?thesis
      unfolding acc_consistent_def Let_def split
      apply (intro conjI allI ballI)
      subgoal for b
        using c1.acc_ref_not_fresh[of b] c2.acc_ref_not_fresh[of b]
        by (auto simp: c1.is_FRESH'_eq c2.is_FRESH'_eq)
      subgoal for b
        using c1.acc_ref_not_freed[of b] c2.acc_ref_not_freed[of b]
        by (auto simp: c1.is_FREED'_eq)
      subgoal for a
        using c1.rw_valid_s[of a] c1.rw_valid_s'[of a] c2.rw_valid_s[of a]
        apply clarsimp
        apply (smt (verit, ccfv_threshold) Un_iff addr.case_eq_if c1.valid_block_trans c2.acc_ref_not_freed image_eqI is_valid_addr_def valid_block_trans_def)
        done
      subgoal for a
        using c1.rw_valid_s'[of a] c2.rw_valid_s'[of a] c2.rw_valid_s[of a]
        apply clarsimp
        by (metis Un_iff c1.acc_ref_not_fresh c2.is_ALLOC'_eq c2.is_FREED'_eq c2.valid_if_not_freed block.exhaust_disc image_subset_iff sup_ge1)
      subgoal
        using c1.valid_block_trans c2.valid_block_trans valid_block_trans_trans by blast
      subgoal
        apply (simp add: c1.acc_a_alloc c2.acc_a_alloc alloc_blocks_def)
        by (auto simp: c1.is_FRESH'_eq c2.is_FRESH'_eq)
      subgoal
        apply (simp add: c1.acc_f_freed c2.acc_f_freed freed_blocks_def)
        by (auto simp: c1.is_FREED'_eq c2.is_FREED'_eq)
      subgoal
        by (smt (verit, del_insts) Un_iff addr.case_eq_if block_size_noblock(2) c1.acc_nw_untouched c1.is_FREED'_eq c1.valid_if_not_freed c2.acc_nw_untouched c2.is_FREED'_eq acc_plus_simps(2) is_valid_addr_def)
      done
  qed  

  
  
  
  subsection \<open>Parallel Execution\<close>
  
  subsubsection \<open>Feasibility and Data Race\<close>
  
  text \<open>Parallel state changes are feasible: the memory manager did not allocate the same blocks\<close>    
  definition "spar_feasible i\<^sub>1 i\<^sub>2 \<equiv> acc.a i\<^sub>1 \<inter> acc.a i\<^sub>2 = {}"
  
  text \<open>Parallel executions have no race.
    Note, that this assumes that the ACC_REPORT report is consistent.
    See lemma \<open>acc_norace_strong\<close> below for alternative definition 
    including allocated blocks.
  \<close>      
  definition "acc_norace i\<^sub>1 i\<^sub>2 \<equiv> 
    let (r\<^sub>1, w\<^sub>1, a\<^sub>1, f\<^sub>1) = split_acc i\<^sub>1 in
    let (r\<^sub>2, w\<^sub>2, a\<^sub>2, f\<^sub>2) = split_acc i\<^sub>2 in
    let m\<^sub>1 = w\<^sub>1 \<union> {a. addr.block a \<in> f\<^sub>1} in
    let m\<^sub>2 = w\<^sub>2 \<union> {a. addr.block a \<in> f\<^sub>2} in
      \<comment> \<open>Addresses read or modified by thread1 not modified by thread2\<close>
      (r\<^sub>1\<union>m\<^sub>1) \<inter> (m\<^sub>2) = {}
      \<comment> \<open>Addresses modified by thread1 not read or modified by thread2\<close>
    \<and> (m\<^sub>1) \<inter> (r\<^sub>2\<union>m\<^sub>2) = {}
    "
  
  
  
  lemma spar_feasible_sym: "spar_feasible i\<^sub>1 i\<^sub>2 = spar_feasible i\<^sub>2 i\<^sub>1"  
    by (auto simp: spar_feasible_def)

  lemma acc_norace_sym: "acc_norace i\<^sub>1 i\<^sub>2 = acc_norace i\<^sub>2 i\<^sub>1"  
    by (simp add: acc_norace_def Let_def; fast)
    
  
  definition "combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2 \<equiv> mcombine s\<^sub>1 (acc.w i\<^sub>2) s\<^sub>2"

  
  text \<open>Locale that assumes consistent, feasible parallel executions\<close>
  locale feasible_parallel_execution =
    fixes s s\<^sub>1 i\<^sub>1 s\<^sub>2 i\<^sub>2
    assumes c1[simp]: "acc_consistent s i\<^sub>1 s\<^sub>1"
    assumes c2[simp]: "acc_consistent s i\<^sub>2 s\<^sub>2"
    assumes feasible: "spar_feasible i\<^sub>1 i\<^sub>2"
  begin  
  
    sublocale c1: acc_consistent_loc s i\<^sub>1 s\<^sub>1
      by unfold_locales (rule c1)
    
    sublocale c2: acc_consistent_loc s i\<^sub>2 s\<^sub>2
      by unfold_locales (rule c2)

  
    abbreviation "r\<^sub>1 \<equiv> c1.r"
    abbreviation "w\<^sub>1 \<equiv> c1.w"
    abbreviation "a\<^sub>1 \<equiv> c1.a"
    abbreviation "f\<^sub>1 \<equiv> c1.f"
  
    abbreviation "r\<^sub>2 \<equiv> c2.r"
    abbreviation "w\<^sub>2 \<equiv> c2.w"
    abbreviation "a\<^sub>2 \<equiv> c2.a"
    abbreviation "f\<^sub>2 \<equiv> c2.f"

    abbreviation "valid_addrs_s \<equiv> Collect (is_valid_addr s)"
    abbreviation "valid_blocks_s \<equiv> Collect (is_ALLOC s)"
      
    lemma par_blocks_exist_before:
      assumes [simp]: "is_ALLOC s\<^sub>1 b" 
      assumes [simp]: "is_ALLOC s\<^sub>2 b"  
      shows "is_ALLOC s b"
    proof (cases "mapp s b")
      case [simp]: FRESH
      
      have "b \<in> alloc_blocks s s\<^sub>1 \<inter> alloc_blocks s s\<^sub>2"
        unfolding alloc_blocks_def by auto
      with feasible have False
        unfolding spar_feasible_def c1.acc_a_alloc c2.acc_a_alloc by auto
      then show ?thesis ..
    next
      case FREED
      with c1.valid_block_trans[of b] have False unfolding valid_block_trans_def by auto
      then show ?thesis ..
    next
      case (ALLOC vs)
      then show ?thesis by simp
    qed
    
    lemma par_blocks_same_length:
      assumes "is_ALLOC s\<^sub>1 b" 
      assumes "is_ALLOC s\<^sub>2 b"  
      shows "block_size s\<^sub>1 b = block_size s\<^sub>2 b"  
      by (metis assms(1) assms(2) c1.valid_block_trans c2.valid_block_trans block.disc(2) par_blocks_exist_before valid_block_trans_def)
        
    lemma block_size_combine[simp]: "block_size (mcombine s\<^sub>1 A s\<^sub>2) b = (
      if is_ALLOC s\<^sub>1 b \<and> \<not>is_FREED s\<^sub>2 b then block_size s\<^sub>1 b
      else if \<not>is_FREED s\<^sub>1 b \<and> is_ALLOC s\<^sub>2 b then block_size s\<^sub>2 b
      else 0
    )"  
      apply (cases "mapp s\<^sub>1 b"; cases "mapp s\<^sub>2 b")
      apply (auto simp: block_size_def)
      done
            
    lemma valid_mcombine[simp]: "is_valid_addr (mcombine s\<^sub>1 A s\<^sub>2) a \<longleftrightarrow> 
        (is_valid_addr s\<^sub>1 a \<and> \<not>is_FREED s\<^sub>2 (addr.block a)) 
      \<or> (is_valid_addr s\<^sub>2 a \<and> \<not>is_FREED s\<^sub>1 (addr.block a))"
      apply (cases a)
      subgoal for b i
        apply (cases "mapp s\<^sub>1 b"; cases "mapp s\<^sub>2 b"; simp)
        unfolding is_valid_addr_def
        by (auto simp: par_blocks_same_length)
      done        

    subsection \<open>Consistency\<close>  
      
    abbreviation "s' \<equiv> combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2"                                              

    (* TODO: Move *)
    lemma block_combine_FRESH_iff[simp]: "block_combine c\<^sub>1 A c\<^sub>2 = FRESH \<longleftrightarrow> c\<^sub>1=FRESH \<and> c\<^sub>2=FRESH"
      by (cases c\<^sub>1; cases c\<^sub>2; simp)

    lemma is_FRESH'_eq: "is_FRESH s' b \<longleftrightarrow> is_FRESH s\<^sub>1 b \<and> is_FRESH s\<^sub>2 b \<and> b\<notin>a\<^sub>1\<union>a\<^sub>2"  
      by (auto simp: combine_states_def c1.is_FRESH'_eq c2.is_FRESH'_eq)
      
    lemma is_ALLOC'_eq: "is_ALLOC s' b \<longleftrightarrow> (b\<notin>f\<^sub>1\<union>f\<^sub>2) \<and> (b\<in>a\<^sub>1\<union>a\<^sub>2 \<or> is_ALLOC s b)"  
      apply (auto simp: combine_states_def)
      subgoal by (smt (verit, best) c1.is_FREED'_eq block.disc(2) block_combine_add_simps(2))
      subgoal by (metis (no_types, lifting) c2.is_FREED'_eq block.disc(2) block_combine_add_simps(3))
      subgoal by (smt (z3) c1.is_ALLOC'_eq c2.is_ALLOC'_eq block_combine.simps(1) block_combine_add_simps(2) is_ALLOC_conv)

      subgoal by (metis (mono_tags, lifting) alloc_blocks_def c1.acc_a_alloc c1.is_ALLOC'_eq c2.is_FREED'_eq block.distinct_disc(4) block.exhaust_disc block_combine_add_simps(1) mem_Collect_eq par_blocks_exist_before)
      subgoal by (smt (z3) c1.is_FREED'_eq c2.is_ALLOC'_eq c2.is_FREED'_eq block.exhaust_disc block_combine.simps(1) block_combine.simps(7) is_alloc_def) 
      subgoal by (metis (no_types, lifting) c1.is_ALLOC'_eq c2.is_ALLOC'_eq block_combine.simps(7) is_alloc_def)
            
      done
          
    lemma is_FREED'_eq: "is_FREED s' b \<longleftrightarrow> b\<in>f\<^sub>1\<union>f\<^sub>2 \<or> is_FREED s b"  
      apply (auto simp: combine_states_def)
      subgoal using c1.is_FREED'_eq c2.is_FREED'_eq block_combine.elims by blast
      subgoal by (metis (mono_tags, lifting) c1.is_FREED'_eq block_combine_add_simps(2))
      subgoal by (smt (verit) c2.is_FREED'_eq block_combine_add_simps(3))
      subgoal by (simp add: c2.valid_trans_imps(1))
      done
      
    lemma valid_addr': "is_valid_addr s' a \<longleftrightarrow> 
        (is_valid_addr s\<^sub>1 a \<and> addr.block a \<notin> f\<^sub>2) 
      \<or> (is_valid_addr s\<^sub>2 a \<and> addr.block a \<notin> f\<^sub>1)"
      unfolding combine_states_def 
      apply clarsimp
      by (smt (verit, del_insts) addr.case_eq_if block_size_noblock(3) c1.acc_consistent_loc_axioms c1.acc_f_freed c2.acc_consistent_loc_axioms c2.acc_f_freed block.distinct(5) freed_blocks_def acc_consistent_loc.valid_block_trans is_alloc_def is_valid_addr_def mem_Collect_eq valid_block_trans_def zero_order(3))
  
      
      
    lemma get_addr_combine: 
      assumes "is_valid_addr s' a" 
      shows "get_addr s' a = (if a\<in>w\<^sub>2 \<or> addr.block a \<in> a\<^sub>2 then get_addr s\<^sub>2 a else get_addr s\<^sub>1 a)"  
    proof (cases a)
      case [simp]: (ADDR b i)
      
      from assms have [simp]: "0\<le>i" unfolding is_valid_addr_def by auto
      
      show ?thesis 
      proof (cases "b \<in> a\<^sub>2")
        case True
        hence "is_FRESH s\<^sub>1 b"
          by (smt (verit) alloc_blocks_def c1.acc_a_alloc c2.acc_a_alloc disjoint_iff feasible mem_Collect_eq spar_feasible_def)
        then show ?thesis
          using True
          by (auto simp add: combine_states_def get_addr_def)
        
      next
        case [simp]: False
        show ?thesis proof (cases "ADDR b i\<in>w\<^sub>2")
          case [simp]: True

          have A2: "is_ALLOC s\<^sub>2 b"
            using assms \<open>b\<notin>a\<^sub>2\<close>
            apply (simp add: valid_addr')
            apply (simp add: is_valid_addr_alt)
            apply auto
            by (metis True UnI1 Un_upper2 addr.sel(1) c1.valid_trans_imps(1) c2.acc_ref_not_fresh c2.is_FREED'_eq block.exhaust_disc image_eqI subsetD)
      
          have "is_ALLOC s b"
            by (smt (verit, best) False \<open>is_ALLOC s\<^sub>2 b\<close> alloc_blocks_def c2.acc_a_alloc c2.valid_block_trans block.exhaust_disc mem_Collect_eq valid_block_trans_def)

          have A1: "is_ALLOC s\<^sub>1 b"
            by (smt (verit, best) ADDR \<open>is_ALLOC s b\<close> addr.case assms block_size_combine c1.valid_block_trans combine_states_def is_valid_addr_alt not_less_zero valid_block_trans_def)
                                  
          show ?thesis using A1 A2
            apply (cases "mapp s\<^sub>1 b"; cases "mapp s\<^sub>2 b"; simp)
            apply (auto simp add: combine_states_def get_addr_def split: if_splits)
            by (smt (verit, best) A1 A2 ADDR True addr.case assms block_size_def block.simps(10) is_valid_addr_alt list_combine_inth mem_Collect_eq par_blocks_same_length)
          
        next
          case [simp]: False
          
          show ?thesis proof (cases "is_FRESH s\<^sub>2 b")
            case True
            then show ?thesis 
              apply simp
              by (simp add: combine_states_def get_addr_def)
              
          next
            case False
            have A2: "is_ALLOC s\<^sub>2 b"
              by (metis (no_types, lifting) ADDR False addr.case_eq_if addr.sel(1) assms block.exhaust_disc combine_states_def is_valid_addr_alt valid_mcombine)

            hence "is_ALLOC s b"
              by (simp add: c2.is_ALLOC'_eq)
            
            hence A1: "is_ALLOC s\<^sub>1 b"
              by (metis (no_types, lifting) ADDR addr.case addr.sel(1) assms c1.valid_trans_imps(2) combine_states_def is_valid_addr_alt valid_mcombine)
              
            have [simp]: "0\<le>i' \<Longrightarrow> nat i = nat i' \<longleftrightarrow> i=i'" for i' using \<open>0\<le>i\<close>
              by presburger
              
            show ?thesis using A1 A2
              apply (cases "mapp s\<^sub>1 b"; cases "mapp s\<^sub>2 b"; simp)
              
              apply (auto simp add: combine_states_def get_addr_def split: if_splits)
              apply (subst list_combine_inth)
              subgoal by (metis block_size_def block.disc(3) block.simps(10) par_blocks_same_length)
              apply auto
              done
              
          qed
        qed
      qed
    qed
            
    lemma get_addr1_orig: "\<lbrakk>is_valid_addr s a; is_valid_addr s' a; a \<notin> w\<^sub>1\<rbrakk> \<Longrightarrow> get_addr s\<^sub>1 a = get_addr s a"
      using c1.acc_nw_untouched c1.valid_if_not_freed valid_addr' by blast
      
    lemma get_addr2_orig: "\<lbrakk>is_valid_addr s a; is_valid_addr s' a; a \<notin> w\<^sub>2\<rbrakk> \<Longrightarrow> get_addr s\<^sub>2 a = get_addr s a"
      using c2.addr_orig_val c2.acc_nw_untouched valid_addr' by blast
      
    lemmas get_addr_orig = get_addr1_orig get_addr2_orig
      
    lemma consistent': "acc_consistent s (i\<^sub>1+i\<^sub>2) s'"
      unfolding acc_consistent_def Let_def split
      apply (intro conjI allI ballI)
      subgoal for b
        using c1.acc_ref_not_fresh[of b] c2.acc_ref_not_fresh[of b]
        by (auto simp: is_FRESH'_eq)
      subgoal for b
        using c1.acc_ref_not_freed[of b] c2.acc_ref_not_freed[of b]
        by (auto simp: )
      subgoal for a
        using c1.rw_valid_s c2.rw_valid_s by auto
      subgoal for a
        using c1.rw_valid_s' c2.rw_valid_s' apply (clarsimp simp: is_ALLOC'_eq)
        by (metis Un_iff c1.acc_ref_not_fresh c1.is_ALLOC'_eq c1.is_FREED'_eq c2.acc_ref_not_fresh c2.is_ALLOC'_eq c2.is_FREED'_eq block.disc(2) block.exhaust_disc image_eqI valid_addr')
      subgoal for b \<comment> \<open>Valid block trans\<close>
        using c1.valid_block_trans[of b] c2.valid_block_trans[of b]
        by (cases "mapp s\<^sub>1 b"; cases "mapp s\<^sub>2 b"; cases "mapp s b"; simp add: valid_block_trans_def combine_states_def)
      subgoal 
        by (auto simp: c1.acc_a_alloc c2.acc_a_alloc alloc_blocks_def is_FRESH'_eq)
      subgoal        
        by (auto simp: c1.acc_f_freed c2.acc_f_freed freed_blocks_def is_FREED'_eq)
        
      subgoal for a \<comment> \<open>Non-written addresses untouched\<close>
        by (auto simp: get_addr_combine get_addr_orig)
      done
        
    lemma alloc_block'_eq: "alloc_blocks s s' = alloc_blocks s s\<^sub>1 \<union> alloc_blocks s s\<^sub>2"
      using c1.acc_a_alloc c2.acc_a_alloc consistent' acc_consistent_loc.acc_a_alloc acc_consistent_loc.intro acc_plus_simps(3) by blast
      
    lemma alloc_disj: "a\<^sub>1 \<inter> a\<^sub>2 = {}"
      using feasible spar_feasible_def by auto

    lemma alloc_free_dj: "a\<^sub>1\<inter>f\<^sub>2 = {}"
        using alloc_disj c1.a_dj_alloc c2.f_valid_or_alloc by auto
        
    lemma free_alloc_dj: "f\<^sub>1\<inter>a\<^sub>2 = {}"
        using alloc_disj c2.a_dj_alloc c1.f_valid_or_alloc by auto
      
      
      
    lemma alloc_addrs_approx_disj: "c1.allocated_addrs_approx \<inter> c2.allocated_addrs_approx = {}"
      using feasible spar_feasible_def by auto

    lemma alloc_addrs_disj: "c1.allocated_addrs \<inter> c2.allocated_addrs = {}"
      using alloc_addrs_approx_disj c1.allocated_addrs_approx c2.allocated_addrs_approx by blast

    lemma alloc_freed_addrs_approx_disj: 
      "c1.allocated_addrs_approx \<inter> c2.freed_addrs_approx = {}"
      "c2.allocated_addrs_approx \<inter> c1.freed_addrs_approx = {}"
      using alloc_free_dj free_alloc_dj by auto
      
    lemma alloc_freed_addrs_disj: 
      "c1.allocated_addrs \<inter> c2.freed_addrs = {}"
      "c2.allocated_addrs \<inter> c1.freed_addrs = {}"
      using c1.valid_s_not_alloc c2.freed_valid_s
      using c1.freed_valid_s c2.valid_s_not_alloc
       by auto
      

         
    (* Stronger version of no-race as lemma, 
      assuming acc_consistent + feasible!
    *)  
    lemma acc_norace_strong:
      shows "acc_norace i\<^sub>1 i\<^sub>2 = (
      let m\<^sub>1 = w\<^sub>1 \<union> {a. addr.block a \<in> a\<^sub>1 \<union> f\<^sub>1} in
      let m\<^sub>2 = w\<^sub>2 \<union> {a. addr.block a \<in> a\<^sub>2 \<union> f\<^sub>2} in
        (r\<^sub>1\<union>m\<^sub>1) \<inter> (m\<^sub>2) = {}
      \<and> (m\<^sub>1) \<inter> (r\<^sub>2\<union>m\<^sub>2) = {})
      "
      apply (simp add: Let_def acc_norace_def set_eq_iff)
      using alloc_addrs_approx_disj 
      c1.a_dj_valid c2.rw_valid_or_alloc
      c1.rw_valid_or_alloc c2.a_dj_valid
      free_alloc_dj alloc_free_dj
      by blast
    
    
    
    (* Properties of combine, for presentation in paper *)    
    
    lemma 
    assumes "b \<in> a\<^sub>2\<union>f\<^sub>2"  
    shows 
      "is_FRESH s' b = is_FRESH s\<^sub>2 b" "is_FREED s' b = is_FREED s\<^sub>2 b" "is_ALLOC s' b = is_ALLOC s\<^sub>2 b"
      using assms
      apply (simp_all add: is_FRESH'_eq is_FREED'_eq is_ALLOC'_eq)
      using c1.is_FRESH'_eq c2.is_FREED'_eq c2.is_FRESH'_eq assms apply blast
      using c1.is_FREED'_eq c2.is_FREED'_eq free_alloc_dj apply blast
      using c1.is_ALLOC'_eq c2.is_ALLOC'_eq free_alloc_dj assms apply blast
      done
      
    lemma 
    assumes "b \<notin> a\<^sub>2\<union>f\<^sub>2"  
    shows 
      "is_FRESH s' b = is_FRESH s\<^sub>1 b" "is_FREED s' b = is_FREED s\<^sub>1 b" "is_ALLOC s' b = is_ALLOC s\<^sub>1 b"
      using assms
      apply (simp_all add: is_FRESH'_eq is_FREED'_eq is_ALLOC'_eq)
      using c1.is_FRESH'_eq c2.is_FREED'_eq c2.is_FRESH'_eq assms apply blast
      using c1.is_FREED'_eq c2.is_FREED'_eq free_alloc_dj apply blast
      using c1.is_ALLOC'_eq c2.is_ALLOC'_eq free_alloc_dj assms apply blast
      done
    
    
    lemma "is_FRESH s' b \<longleftrightarrow> (if b \<in> a\<^sub>2\<union>f\<^sub>2 then is_FRESH s\<^sub>2 b else is_FRESH s\<^sub>1 b)"
      apply (simp add: is_FRESH'_eq)
      using c1.is_FRESH'_eq c2.is_FREED'_eq c2.is_FRESH'_eq by blast
    
    lemma "is_FREED s' b \<longleftrightarrow> (if b \<in> a\<^sub>2\<union>f\<^sub>2 then is_FREED s\<^sub>2 b else is_FREED s\<^sub>1 b)"
      apply (simp add: is_FREED'_eq)
      using c1.is_FREED'_eq c2.is_FREED'_eq free_alloc_dj by auto
    
    lemma "is_ALLOC s' b \<longleftrightarrow> (if b \<in> a\<^sub>2\<union>f\<^sub>2 then is_ALLOC s\<^sub>2 b else is_ALLOC s\<^sub>1 b)"
      apply (simp add: is_ALLOC'_eq)
      using c1.is_ALLOC'_eq c2.is_ALLOC'_eq free_alloc_dj by auto

    lemma 
      fixes b i
      defines "a \<equiv> ADDR b i"
      assumes "is_ALLOC s' b" 
      shows "get_addr s' a = (if a\<in>w\<^sub>2 \<or> b\<in>a\<^sub>2 \<or> b\<in>f\<^sub>2 then get_addr s\<^sub>2 a else get_addr s\<^sub>1 a)"  
      apply (cases "is_valid_addr s' a")
      subgoal
        using assms(2)
        by (auto simp: get_addr_combine a_def is_ALLOC'_eq)
      subgoal
        using assms(2)
        apply (auto simp add: is_valid_addr_alt a_def get_addr_def)
        apply (auto simp: block_size_def split: block.splits)
        
        subgoal
          by (metis (no_types, lifting) UnI1 Un_commute addr.sel(1) addr.simps(2) assms(2) block_size_def c2.acc_consistent_loc_axioms c2.acc_ref_not_fresh c2.is_FREED'_eq block.simps(10) image_eqI acc_consistent_loc.rw_valid_s' is_ALLOC_conv is_FREED'_eq is_valid_addr_def valid_addr')
        subgoal
          by (smt (verit, ccfv_SIG) Un_iff alloc_blocks_def c1.acc_a_alloc c1.is_ALLOC'_eq c1.is_FRESH'_eq c2.acc_a_alloc c2.is_ALLOC'_eq block.disc(1) block.disc(2) block.disc(3) block.distinct(5) block.sel block_combine.simps(1) combine_states_def free_alloc_dj i_nth_simp(3) is_FREED'_eq le_eq_less_or_eq linorder_le_cases mapp_combine mem_Collect_eq par_blocks_exist_before)
        subgoal 
          by (meson UnI2 assms(2) is_ALLOC'_eq)
        subgoal
          by (metis Un_iff block_size_combine block_size_def c1.is_ALLOC'_eq c2.is_FREED'_eq block.collapse block.disc(3) block.distinct(5) block.simps(10) combine_states_def i_nth_simp(3) is_ALLOC'_eq is_FREED'_eq linorder_not_le)
        done
      done        
    
  end

  text \<open>Consistent, feasible, and race free parallel executions\<close>  
  locale valid_parallel_execution =
    fixes s s\<^sub>1 i\<^sub>1 s\<^sub>2 i\<^sub>2
    assumes c1[simp]: "acc_consistent s i\<^sub>1 s\<^sub>1"
    assumes c2[simp]: "acc_consistent s i\<^sub>2 s\<^sub>2"
    assumes feasible: "spar_feasible i\<^sub>1 i\<^sub>2"
    assumes norace: "acc_norace i\<^sub>1 i\<^sub>2"
  begin  

    sublocale feasible_parallel_execution by (unfold_locales) (auto simp: feasible)
      
      
    lemma write_disjoint: "w\<^sub>1 \<inter> w\<^sub>2 = {}"
      using norace unfolding acc_norace_def Let_def by auto

    
    subsection \<open>Symmetry\<close>  
      
    lemma combine_states_sym: "combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2 = combine_states s\<^sub>2 i\<^sub>1 s\<^sub>1"
      apply (clarsimp simp: mext)
      subgoal for b
        unfolding combine_states_def
        apply simp
        apply (cases "mapp s\<^sub>1 b"; cases "mapp s\<^sub>2 b"; simp)
        proof goal_cases
          case [simp]: (1 vs\<^sub>1 vs\<^sub>2)
          
          (* TODO: we break the abstraction barrier of get_addr twice! *)
          
          obtain vs where [simp]: "mapp s b = ALLOC vs" 
            using par_blocks_exist_before[of b] 
            by (cases "mapp s b"; simp)
          
          have [simp]: "length vs\<^sub>1 = length vs" 
            using c1.valid_block_trans[of b] unfolding valid_block_trans_def block_size_def by auto
          have [simp]: "length vs\<^sub>2 = length vs"
            using c2.valid_block_trans[of b] unfolding valid_block_trans_def block_size_def by auto
          
          have [simp]:
            "get_addr s\<^sub>1 (ADDR b i) = i_nth vs\<^sub>1 i" 
            "get_addr s\<^sub>2 (ADDR b i) = i_nth vs\<^sub>2 i" 
            for i by (simp_all add: get_addr_def)
          
          have [simp]:
            "is_valid_addr s (ADDR b i) \<longleftrightarrow> 0\<le>i \<and> nat i<length vs" 
            "is_valid_addr s\<^sub>1 (ADDR b i) \<longleftrightarrow> 0\<le>i \<and> nat i<length vs" 
            "is_valid_addr s\<^sub>2 (ADDR b i) \<longleftrightarrow> 0\<le>i \<and> nat i<length vs" 
            for i   
            by (simp_all add: is_valid_addr_def block_size_def)
            
          
          show ?case
            using write_disjoint c1.acc_nw_untouched[of "ADDR b _"]
            using write_disjoint c2.acc_nw_untouched[of "ADDR b _"]
            apply (auto simp: list_eq_iff_nth_eq list_combine_nth eq_nat_nat_iff)
            by (metis int_nat_eq nat_int order_refl)
          
        qed
      done
      
    lemma symmetric: "valid_parallel_execution s s\<^sub>2 i\<^sub>2 s\<^sub>1 i\<^sub>1"  
      apply unfold_locales
      using feasible spar_feasible_sym acc_norace_sym norace
      by auto
      
      
    lemma freed_disj: "f\<^sub>1 \<inter> f\<^sub>2 = {}"  
      using norace unfolding acc_norace_def Let_def
      apply auto
      by (metis IntI UnI2 addr.sel(1) emptyE mem_Collect_eq)
      
    lemma freed_addrs_approx_disj: "c1.freed_addrs_approx \<inter> c2.freed_addrs_approx = {}"
      using freed_disj by fastforce 

    lemma freed_addrs_disj: "c1.freed_addrs \<inter> c2.freed_addrs = {}"
      using freed_addrs_approx_disj c1.freed_addrs_approx c2.freed_addrs_approx by blast
      
    lemma valid_addr'': "Collect (is_valid_addr s') =
      (Collect (is_valid_addr s\<^sub>1) - c2.freed_addrs) \<union> (Collect (is_valid_addr s\<^sub>2) - c1.freed_addrs)"
      apply (auto simp: valid_addr')
      subgoal
        using c2.freed_addrs_approx by blast
      subgoal 
        using c1.freed_addrs_approx by blast
      subgoal 
        by (simp add: c1.freed_addrs_def)
      subgoal 
        by (simp add: c2.freed_addrs_def)
      subgoal 
        by (smt Diff_iff UnE alloc_blocks_def c2.freed_addrs_def c2.is_FREED'_eq block.distinct(2) disjoint_iff c1.acc_a_alloc c2.acc_a_alloc c1.valid_addrs'_subset mem_Collect_eq spar_feasible_def subsetD feasible)
      subgoal by (simp add: addr.case_eq_if c1.is_ALLOC'_eq is_valid_addr_alt)
      subgoal 
        by (smt Diff_iff UnE alloc_blocks_def c1.freed_addrs_def c1.is_FREED'_eq block.distinct(2) disjoint_iff c1.acc_a_alloc c2.acc_a_alloc c2.valid_addrs'_subset mem_Collect_eq spar_feasible_def subsetD feasible)
      subgoal using freed_disj by blast
      done
      

    lemma valid_addr'_outside_wa_eq_orig:
      assumes "is_valid_addr s' a" "a \<notin> w\<^sub>1" "addr.block a \<notin> a\<^sub>1" "a \<notin> w\<^sub>2" "addr.block a \<notin> a\<^sub>2"
      shows "get_addr s\<^sub>1 a = get_addr s a" "get_addr s\<^sub>2 a = get_addr s a"
      subgoal
        apply (rule get_addr1_orig)
        using assms
        apply auto
        using c1.allocated_addrs_approx c1.valid_s'_alt c2.allocated_addrs_approx c2.valid_s'_alt valid_addr' by auto
      subgoal
        apply (rule get_addr2_orig)
        using assms
        apply auto
        using c1.allocated_addrs_approx c1.valid_s'_alt c2.allocated_addrs_approx c2.valid_s'_alt valid_addr' by auto
      done
            
                        
  end      

end
