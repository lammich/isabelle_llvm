section \<open>Generic Block Allocator --- Reasoning Setup\<close>
theory Sep_Block_Allocator_RS
imports Sep_Lift "../basic/LLVM_Basic_Main"
begin

  lemma list\<alpha>_at_len: "list\<alpha> \<alpha> xs (length xs) = 0"
    by (auto simp: list\<alpha>_def)
  
  lemma list\<alpha>_gt_len: "i\<ge>length xs \<Longrightarrow> list\<alpha> \<alpha> xs i = 0"
    by (auto simp: list\<alpha>_def)
  
  lemma list\<alpha>_snoc: "list\<alpha> \<alpha> (xs@[x]) = 0(length xs := \<alpha> x) + list\<alpha> \<alpha> xs"
    apply (rule ext)
    apply (auto simp: list\<alpha>_def nth_append)
    done
    
  lemma list\<alpha>_in_range: "list\<alpha> \<alpha> xs i \<noteq> 0 \<Longrightarrow> i<length xs"
    by (auto simp: list\<alpha>_def split: if_splits)
  
  lemma list\<alpha>_in_rangeD: "list\<alpha> \<alpha> xs = x \<Longrightarrow> x i \<noteq> 0 \<Longrightarrow> i<length xs"
    by (auto simp: list\<alpha>_def split: if_splits)

  lemma list\<alpha>_splitE:
    assumes "list\<alpha> \<alpha> xs = fun_upd 0 i p + fun_upd f i 0"  
    assumes "p\<noteq>0"
    obtains "i<length xs" "\<alpha> (xs!i) = p"
    using assms 
    by (auto simp: list\<alpha>_def fun_eq_iff split: if_splits)
    
  lemma option\<alpha>_splitE:  
    assumes "option\<alpha> \<alpha> v = p"
    assumes "p\<noteq>0"
    obtains x where "v=Some x" "\<alpha> x = p"
    using assms by (cases v) auto

  locale block_allocator2 = block_allocator1 static_err mem_err bload bstore bcheck_addr
    for static_err :: 'err
    and mem_err :: 'err
    and bload :: "'baddr::this_addr \<Rightarrow> ('val,_,'block,'err,'i::interference) M"
    and bstore :: "'val \<Rightarrow> 'baddr \<Rightarrow> (unit,_,'block,'err,'i) M"
    and bcheck_addr :: "'baddr \<Rightarrow> (unit,_,'block,'err,'i) M"
    
  + fixes \<alpha>b :: "'block \<Rightarrow> 'ablock::unique_zero_sep_algebra"
      and bpto :: "'val \<Rightarrow> 'baddr \<Rightarrow> 'ablock \<Rightarrow> bool"
      and tag_of :: "'block \<Rightarrow> 'tag"
      and is_complete_tag :: "'ablock \<Rightarrow> 'tag \<Rightarrow> bool"
      
    assumes bload_rule: "\<And>x a. htriple \<alpha>b (bpto x a) (bload a) (\<lambda>r. \<up>(r=x) ** bpto x a)"
        and bstore_rule: "\<And>x xx a. htriple \<alpha>b (bpto xx a) (bstore x a) (\<lambda>_. bpto x a)"
        and bload_pres_tag: "\<And>s a. wlp (bload a) (\<lambda>_ s'. tag_of s' = tag_of s) s"
        and bstore_pres_tag: "\<And>s a x. wlp (bstore a x) (\<lambda>_ s'. tag_of s' = tag_of s) s"
        and complete_tag: 
          "\<And>f. \<lbrakk>is_complete_tag ablock (tag_of cblock); ablock ## f; \<alpha>b cblock = ablock + f\<rbrakk> \<Longrightarrow> f=0"
        and bpto_notZ: "\<And>x a. \<not>bpto x a 0"
  begin
  
    definition \<alpha>tag :: "'block \<Rightarrow> 'tag tsa_opt" where "\<alpha>tag blk \<equiv> TRIV (tag_of blk)"
    definition \<alpha> :: "'block memory \<Rightarrow> nat \<Rightarrow> 'ablock \<times> 'tag tsa_opt" 
      where "\<alpha> \<equiv> \<lambda>MEMORY blocks \<Rightarrow> list\<alpha> (option\<alpha> (\<lambda>x. (\<alpha>b x, \<alpha>tag x))) blocks"
    definition pto :: "'val \<Rightarrow> 'baddr addr rptr \<Rightarrow> (nat \<Rightarrow> 'ablock \<times> 'tag tsa_opt) \<Rightarrow> bool" 
      where "pto x \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> \<lambda>s. \<exists>ablk. s=0(bi:=(ablk,0)) \<and> bpto x ba ablk | _ \<Rightarrow> sep_false"
    
    definition tag :: "'tag \<Rightarrow> 'baddr addr rptr \<Rightarrow> (nat \<Rightarrow> 'ablock \<times> 'tag tsa_opt) \<Rightarrow> bool" 
      where "tag t \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> EXACT (0(bi:=(0,TRIV t))) ** \<up>(ba=this_addr \<and> t\<in>range tag_of) | _ \<Rightarrow> sep_false"
    definition block :: "'ablock \<Rightarrow> 'baddr addr rptr \<Rightarrow> (nat \<Rightarrow> 'ablock \<times> 'tag tsa_opt) \<Rightarrow> bool"
      where "block b \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> EXACT (0(bi:=(b,0))) ** \<up>(ba=this_addr) | _ \<Rightarrow> sep_false"
  
    
    lemma alloc_rule: "htriple \<alpha> \<box> (alloc b) (\<lambda>r. block (\<alpha>b b) r ** tag (tag_of b) r)"
      apply (rule htripleI')
      apply (auto simp: alloc_def wp_def run_simps sep_algebra_simps split: option.splits)
    proof -
      fix s :: "'block memory"
      obtain blocks where [simp]: "s = MEMORY blocks" by (cases s)
      
      show "\<exists>p'. p' ## \<alpha> s \<and>
              \<alpha> (put' memory.the_memory\<^sub>L (get' memory.the_memory\<^sub>L s @ [Some b]) s) = p' + \<alpha> s \<and>
              (block (\<alpha>b b) (RP_ADDR (ADDR (length (get' memory.the_memory\<^sub>L s)) this_addr)) \<and>*
               tag (tag_of b) (RP_ADDR (ADDR (length (get' memory.the_memory\<^sub>L s)) this_addr)))
               p'"
        apply (rule exI[where x="0(length blocks := (\<alpha>b b, TRIV (tag_of b)))"]; intro conjI)
        apply (clarsimp_all simp: \<alpha>_def block_def tag_def \<alpha>tag_def sep_algebra_simps list\<alpha>_at_len)
        subgoal by (simp add: list\<alpha>_snoc)
        subgoal
          apply (subst EXACT_split[symmetric])
          apply (auto simp: sep_algebra_simps)
          done
        done
    qed
  
    lemma complete_splitE:
      assumes C: "is_complete_tag blk t"
      assumes DISJ: "f i ## (blk, TRIV t)"
      assumes AEQ: "list\<alpha> (option\<alpha> (\<lambda>x. (\<alpha>b x, \<alpha>tag x))) xs = f + fun_upd 0 i (blk, TRIV t)"
      obtains cblk where 
        "i<length xs" "xs!i = Some cblk" "blk = \<alpha>b cblk" "t = tag_of cblk" "f i = 0"
    proof -
      have [simp]: "i<length xs"
        apply (rule list\<alpha>_in_rangeD[OF AEQ])
        apply (auto simp: sep_algebra_simps DISJ)
        done

      obtain fib fit where [simp]: "f i = (fib,fit)"  by (cases "f i")
                
      from DISJ have [simp]: "blk ## fib" "fit = 0" 
        by (auto simp: sep_algebra_simps)

              
      obtain cblk where [simp]: "xs!i = Some cblk" "\<alpha>b cblk = blk + fib" "t = tag_of cblk"
        using fun_cong[OF AEQ, of i]
        apply (cases "xs!i")
        apply (auto simp: list\<alpha>_def sep_algebra_simps if_splits \<alpha>tag_def)
        done
        
      from complete_tag[OF C[simplified], of fib, simplified] have [simp]: "fib=0" .
      
      show ?thesis
        apply (rule that[of cblk])
        apply (auto simp: sep_algebra_simps)
        done
    qed        
    
    lemma free_rule: "htriple \<alpha> (block blk a ** tag t a ** \<up>(is_complete_tag blk t)) (free a) (\<lambda>_. \<box>)"
      apply (rule htripleI')
      subgoal for p s f
        apply (cases s)
        apply (auto simp: free_def wp_def run_simps sep_algebra_simps split: option.splits addr.splits rptr.splits)
        apply (auto simp: block_def tag_def sep_algebra_simps pred_lift_extract_simps)
        apply (all \<open>subst (asm) EXACT_split[symmetric] sep_disj_fun_def; clarsimp simp: sep_algebra_simps\<close>)
        apply (auto simp: \<alpha>_def sep_algebra_simps merge_fun_singleton split_fun_upd_0)
        subgoal 
          apply (erule (2) complete_splitE)
          by auto
        subgoal 
          apply (erule (2) complete_splitE)
          by auto
        subgoal for xs i
          by (force simp: sep_algebra_simps dest: sep_disj_funD[where x=i] list\<alpha>_in_rangeD[where i=i])
        subgoal 
          apply (erule (2) complete_splitE)
          by auto
        done  
      done
  
      
    definition "block_lifter bi \<equiv> \<lparr> 
      sep_lifter.lift = \<lambda>x. (0(bi:=(x,0))),
      sep_lifter.project = (\<lambda>f. fst (f bi)),
      sep_lifter.carve = (\<lambda>f. f(bi:=(0,snd (f bi)))),
      sep_lifter.splittable = (\<lambda>f. True),
      sep_lifter.L = lens_of_bi bi,
      sep_lifter.\<alpha>b = \<alpha>,
      sep_lifter.\<alpha>s = \<alpha>b,
      sep_lifter.tyb = \<lambda>_. (),
      sep_lifter.tys = tag_of
          \<rparr>"
      
    lemma block_lifter_simps[simp]:      
      "sep_lifter.lift (block_lifter bi) = (\<lambda>x. (0(bi:=(x,0))))"
      "sep_lifter.project (block_lifter bi) = (\<lambda>f. fst (f bi))"
      "sep_lifter.carve (block_lifter bi) = (\<lambda>f. f(bi:=(0,snd (f bi))))"
      "sep_lifter.splittable (block_lifter bi) = (\<lambda>f. True)"
      "sep_lifter.L (block_lifter bi) = lens_of_bi bi"
      "sep_lifter.\<alpha>b (block_lifter bi) = \<alpha>"
      "sep_lifter.\<alpha>s (block_lifter bi) = \<alpha>b"
      "sep_lifter.tyb (block_lifter bi) = (\<lambda>_. ())"
      "sep_lifter.tys (block_lifter bi) = tag_of"
      unfolding block_lifter_def by auto
          
    sublocale block_lifter: sep_lifter "block_lifter bi"
    proof -

      have aux1[intro]: "a ## fst b \<Longrightarrow> b ## (a, 0)" for a b
        by (cases b) (auto simp: sep_algebra_simps )
        
      show "sep_lifter (block_lifter bi)"
        apply unfold_locales
        apply (auto simp: sep_algebra_simps sep_disj_funD[where x=bi])
        apply (auto 
          simp: lens_of_bi_def \<alpha>_def list\<alpha>_def option\<alpha>_alt \<alpha>tag_def sep_algebra_simps
          split: memory.splits if_splits option.splits
          del: ext intro!: ext)
        done  
    qed    
       
    lemma pto_null_eq[simp]: "pto x RP_NULL = sep_false" by (auto simp: pto_def)
    
    lemma pto_addr_eq[simp]: "pto x (RP_ADDR (ADDR bi ba)) = block_lifter.lift_assn bi (bpto x ba)"
      unfolding pto_def block_lifter.lift_assn_def
      apply (rule ext)
      apply (auto simp: sep_algebra_simps)
      by (metis (no_types, hide_lams) fun_upd_same fun_upd_triv fun_upd_upd prod_Z_lower(1) surjective_pairing zero_fun_def)
    
      
    fun rptr_cases where "rptr_cases (RP_NULL) = ()" | "rptr_cases (RP_ADDR (ADDR _ _)) = ()"
    
    lemma load_rule: "htriple \<alpha> (pto x a) (load a) (\<lambda>r. \<up>(x=r) ** pto x a)"
      unfolding load_def
      apply (cases a rule: rptr_cases.cases; simp)
      apply (rule cons_post_rule)
      apply (rule block_lifter.lift_operation[simplified, OF _ _ bload_rule])
      apply (simp add: bpto_notZ)
      apply (rule bload_pres_tag)
      apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
      done
      
    lemma store_rule: "htriple \<alpha> (pto xx a) (store x a) (\<lambda>_. pto x a)"  
      unfolding store_def
      apply (cases a rule: rptr_cases.cases; simp)
      apply (rule cons_post_rule)
      apply (rule block_lifter.lift_operation[simplified, OF _ _ bstore_rule])
      apply (simp add: bpto_notZ)
      apply (rule bstore_pres_tag)
      apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
      done
        
  end


subsection \<open>Address Arithmetic\<close>  
  
  (*
    ptr ~ ptr :: bool   same base
  
    ptr - ptr :: int    if same base
    ptr + int :: ptr
  

    ~ is equivalence relation
    p ~ p
    p\<^sub>1 ~ p\<^sub>2 \<longleftrightarrow> p\<^sub>2 ~ p\<^sub>1
    p\<^sub>1~p\<^sub>2 \<and> p\<^sub>2~p\<^sub>3 \<longrightarrow> p\<^sub>1~p\<^sub>3 
        
    p + i\<^sub>1 + i\<^sub>2 = p + (i\<^sub>1+i\<^sub>2)
    p + 0 = p
    p ~ p+i
    
    p\<^sub>1~p\<^sub>2 \<Longrightarrow> p\<^sub>2 + (p\<^sub>1-p\<^sub>2) = p\<^sub>1
  *)

  term "a+b"
  
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

  instantiation rptr :: (addr_algebra) addr_algebra begin
    fun abase_rptr where "abase_rptr (RP_ADDR a) \<longleftrightarrow> abase a" | "abase_rptr RP_NULL \<longleftrightarrow> False"

    lemma abase_rptr_alt: "abase p \<longleftrightarrow> (case p of (RP_ADDR a) \<Rightarrow> abase a | RP_NULL \<Rightarrow> False)"
      by (cases p; simp)
      
    fun acompat_rptr where
      "acompat_rptr (RP_ADDR a\<^sub>1) (RP_ADDR a\<^sub>2) \<longleftrightarrow> a\<^sub>1 ~\<^sub>a a\<^sub>2"
    | "acompat_rptr _ _ \<longleftrightarrow> False"
    
    lemma acompat_rptr_alt: "p\<^sub>1 ~\<^sub>a p\<^sub>2 \<longleftrightarrow> (case (p\<^sub>1,p\<^sub>2) of (RP_ADDR a\<^sub>1, RP_ADDR a\<^sub>2) \<Rightarrow> a\<^sub>1 ~\<^sub>a a\<^sub>2 | _ \<Rightarrow> False)"
      by (cases p\<^sub>1; cases p\<^sub>2; simp)
        
    fun adiff_rptr where
      "adiff_rptr (RP_ADDR a\<^sub>1) (RP_ADDR a\<^sub>2) = (a\<^sub>1 -\<^sub>a a\<^sub>2)"
    | "adiff_rptr (RP_NULL) (RP_NULL) = 0"
    | "adiff_rptr _ _ = undefined"

    lemma adiff_rptr_alt: "p\<^sub>1 -\<^sub>a p\<^sub>2 = (case (p\<^sub>1,p\<^sub>2) of (RP_ADDR a\<^sub>1, RP_ADDR a\<^sub>2) \<Rightarrow> a\<^sub>1 -\<^sub>a a\<^sub>2 | (RP_NULL,RP_NULL) \<Rightarrow> 0 | _ \<Rightarrow> undefined)"
      by (cases p\<^sub>1; cases p\<^sub>2; simp)
        
    fun aidx_rptr where
      "aidx_rptr (RP_ADDR a) i = RP_ADDR (a +\<^sub>a i)"
    | "aidx_rptr RP_NULL _ = RP_NULL"

    lemma aidx_rptr_alt: "p\<^sub>1 +\<^sub>a i = (case p\<^sub>1 of RP_ADDR a\<^sub>1 \<Rightarrow> RP_ADDR (a\<^sub>1 +\<^sub>a i) | _ \<Rightarrow> RP_NULL)"
      by (cases p\<^sub>1; simp)
        
    lemma ptr_neq_null_conv: "p\<noteq>RP_NULL \<longleftrightarrow> (\<exists>a. p=RP_ADDR a)" by (cases p) (auto)
    
    instance
      apply standard
      apply (intro part_equivpI sympI transpI)
      apply (meson acompat_equiv acompat_rptr.simps(1) part_equivp_def)
      apply (auto 
        simp: acompat_rptr_alt aidx_rptr_alt adiff_rptr_alt acompat_dom
        split: rptr.splits
        intro!: sympI transpI reflpI
        intro: acompat_sym acompat_trans)
      done
      
  end
  
  fun rptr_the_block_index where
    "rptr_the_block_index (RP_ADDR (ADDR bi _)) = bi" | "rptr_the_block_index _ = undefined"
  
  
  instantiation addr :: (addr_algebra) addr_algebra begin
    fun abase_addr where "abase_addr (ADDR bi ba) \<longleftrightarrow> abase ba"
    fun acompat_addr where "ADDR bi\<^sub>1 ba\<^sub>1 ~\<^sub>a ADDR bi\<^sub>2 ba\<^sub>2 \<longleftrightarrow> bi\<^sub>1=bi\<^sub>2 \<and> ba\<^sub>1~\<^sub>aba\<^sub>2"
    fun aidx_addr where "ADDR bi ba +\<^sub>a i = ADDR bi (ba +\<^sub>a i)"
    fun adiff_addr where "ADDR bi\<^sub>1 ba\<^sub>1 -\<^sub>a ADDR bi\<^sub>2 ba\<^sub>2 = ba\<^sub>1 -\<^sub>a ba\<^sub>2"
    
    lemma abase_addr_alt: "abase = (\<lambda>(ADDR bi ba) \<Rightarrow> abase ba)" by (intro ext) (auto split: addr.splits)
    lemma acomp_addr_alt: "(~\<^sub>a) = (\<lambda>ADDR bi\<^sub>1 ba\<^sub>1 \<Rightarrow> \<lambda>ADDR bi\<^sub>2 ba\<^sub>2 \<Rightarrow> bi\<^sub>1=bi\<^sub>2 \<and> ba\<^sub>1~\<^sub>aba\<^sub>2)" by (intro ext) (auto split: addr.splits)
    lemma aidx_addr_alt: "(+\<^sub>a) = (\<lambda>ADDR bi ba \<Rightarrow> \<lambda>i. ADDR bi (ba +\<^sub>a i))" by (intro ext) (auto split: addr.splits)
    lemma adiff_addr_alt: "(-\<^sub>a) = (\<lambda>ADDR bi\<^sub>1 ba\<^sub>1 \<Rightarrow> \<lambda>ADDR bi\<^sub>2 ba\<^sub>2 \<Rightarrow> ba\<^sub>1 -\<^sub>a ba\<^sub>2)" by (intro ext) (auto split: addr.splits)

    instance
      apply standard
      apply (intro part_equivpI sympI transpI)
      apply (meson acompat_equiv acompat_addr.simps(1) part_equivp_def)
      apply (auto 
        simp: abase_addr_alt acomp_addr_alt aidx_addr_alt adiff_addr_alt acompat_dom
        split: addr.splits 
        intro: acompat_sym acompat_trans) 
      done
  
  end
    
    
    
end
