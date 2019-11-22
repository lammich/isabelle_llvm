section \<open>Array-Blocks --- Reasoning Setup\<close>
theory Sep_Array_Block_RS
imports "../basic/LLVM_Basic_Main" Sep_Block_Allocator_RS
begin

type_synonym 'aval ablock = "nat \<Rightarrow> 'aval"

instantiation baddr :: (this_addr) addr_algebra begin
  definition "abase \<equiv> \<lambda>BADDR i va \<Rightarrow> va=this_addr"
  definition "(~\<^sub>a) \<equiv> \<lambda>BADDR i1 va1 \<Rightarrow> \<lambda>BADDR i2 va2 \<Rightarrow> va1=this_addr \<and> va2=this_addr"
  definition "(-\<^sub>a) \<equiv> \<lambda>BADDR i1 va1 \<Rightarrow> \<lambda>BADDR i2 va2 \<Rightarrow> i1 - i2"
  definition "(+\<^sub>a) \<equiv> \<lambda>BADDR i va \<Rightarrow> \<lambda>j. BADDR (i+j) va"

  lemma abase_baddr_simp[simp]: "abase (BADDR i va) \<longleftrightarrow> va=this_addr"
    by (simp add: abase_baddr_def)
  lemma acompat_baddr_simp[simp]: "BADDR i1 va1 ~\<^sub>a BADDR i2 va2 \<longleftrightarrow> va1=this_addr \<and> va2=this_addr"
    by (simp add: acompat_baddr_def)
  lemma adiff_baddr_simp[simp]: "BADDR i1 va1 -\<^sub>a BADDR i2 va2 = i1 - i2"
    by (simp add: adiff_baddr_def)
  lemma aidx_baddr_simp[simp]: "BADDR i va +\<^sub>a j = BADDR (i+j) va"
    by (simp add: aidx_baddr_def)
  
  instance
    apply standard
    apply (intro part_equivpI sympI transpI)
    apply (auto 
      simp: abase_baddr_def acompat_baddr_def adiff_baddr_def aidx_baddr_def
      split: baddr.splits)
    done

end


locale array_block2 = array_block1 static_err mem_err vload vstore vgep
    for static_err :: 'err
    and mem_err :: 'err
    and vload :: "'vaddr::this_addr \<Rightarrow> ('val,_,'val,'err) M"
    and vstore :: "'val \<Rightarrow> 'vaddr \<Rightarrow> (unit,_,'val,'err) M"
    and vgep :: "'vaddr \<Rightarrow> 'vidx \<Rightarrow> ('vaddr,_,'val,'err) M"
    
+ fixes \<alpha>v :: "'val \<Rightarrow> 'aval::unique_zero_sep_algebra"
    and vpto :: "'val \<Rightarrow> 'vaddr \<Rightarrow> 'aval \<Rightarrow> bool"
    and vcomplete :: "'aval \<Rightarrow> bool"
    
  assumes vload_rule: "htriple \<alpha>v (vpto x va) (vload va) (\<lambda>r. \<up>(r=x) ** vpto x va)" 
      and vstore_rule: "htriple \<alpha>v (vpto xx va) (vstore x va) (\<lambda>_. vpto x va)"
      and vpto_notZ: "\<And>x a. \<not>vpto x a 0"
      and vcompleteD: "\<And>v v'. \<lbrakk>vcomplete v; v##v'\<rbrakk> \<Longrightarrow> v'=0"
      and vpto_this: "\<And>v av. vpto v this_addr av \<longleftrightarrow> av = \<alpha>v v"
      and \<alpha>v_complete: "\<And>v. vcomplete (\<alpha>v v)"
      
      
begin

  (*
  lemma is_arr_baddr_idx[simp]: "is_arr_baddr (idx_baddr a i) \<longleftrightarrow> is_arr_baddr a"
    by (auto simp: is_arr_baddr_def idx_baddr_def split: baddr.splits)
  
  lemma idx_baddr_add[simp]: "idx_baddr (idx_baddr a i) j = idx_baddr a (i+j)"
    by (auto simp: idx_baddr_def split: prod.splits baddr.splits)
    
  definition "idx_ptr \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> \<lambda>i. RP_ADDR (ADDR bi (idx_baddr ba i)) | RP_NULL \<Rightarrow> \<lambda>i. RP_NULL"
  *)
  
  (* TODO: Rename to is_block_ptr! *)    
  definition is_block_ptr :: "'vaddr baddr addr rptr \<Rightarrow> bool" 
    where "is_block_ptr \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> ba=this_addr | _ \<Rightarrow> False"
  
  
  (*definition "is_arr_ptr \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> is_arr_baddr ba | _ \<Rightarrow> False"*)
  
  (* 
  lemma is_arr_ptr_simps[simp]:
    "is_arr_ptr (RP_ADDR (ADDR bi ba)) = is_arr_baddr ba"    
    "is_arr_ptr RP_NULL \<longleftrightarrow> False"
    by (auto simp: is_arr_ptr_def)
  *)

  
  lemma is_block_ptr_simps[simp]:
    "\<not>is_block_ptr RP_NULL"
    "is_block_ptr (RP_ADDR (ADDR bi ba)) \<longleftrightarrow> ba=this_addr"
    by (auto simp: is_block_ptr_def)
    
  lemma block_ptr_imp_abase[simp, intro]: "is_block_ptr p \<Longrightarrow> abase p"  
    by (auto simp: is_block_ptr_def this_addr_baddr_def split: rptr.splits addr.splits)
    
  
  (*
  
  lemma idx_ptr_add[simp]: "idx_ptr (idx_ptr a i) j = idx_ptr a (i+j)"
    by (auto simp: idx_ptr_def split: rptr.splits addr.splits)
    
  lemma is_arr_ptr_idx[simp]: "is_arr_ptr (idx_ptr p i) \<longleftrightarrow> is_arr_ptr p"
    by (cases p) (auto simp: idx_ptr_def is_arr_ptr_def split: rptr.splits addr.splits)
  *)  
    
  lemma \<alpha>v_notZ[simp]: "\<alpha>v v \<noteq> 0"  
    using vpto_notZ vpto_this by fastforce  
  
  definition "\<alpha> \<equiv> list\<alpha> \<alpha>v"

  definition pto :: "'val \<Rightarrow> 'vaddr baddr \<Rightarrow> 'aval ablock \<Rightarrow> bool"
    where "pto \<equiv> \<lambda>x. \<lambda>BADDR i va \<Rightarrow> \<lambda>s. \<exists>v. i\<ge>0 \<and> s=0(nat i:=v) \<and> vpto x va v"
  
  definition tag_of :: "'val block \<Rightarrow> int" where "tag_of \<equiv> int o length"
  
  definition "is_complete_tag ablk n \<equiv> 0\<le>n \<and> (\<forall>i. (ablk i \<noteq> 0 \<longleftrightarrow> i<nat n) \<and> (\<forall>i. ablk i \<noteq> 0 \<longrightarrow> vcomplete (ablk i)))"
    
  
  definition "array_lifter i \<equiv> idx_lifter (\<lambda>_. ()) \<alpha>v i"
  
  lemma array_lifter_simps[simp]: 
    "sep_lifter.\<alpha>s (array_lifter i) = \<alpha>v"  
    "sep_lifter.\<alpha>b (array_lifter i) = \<alpha>"  
    "sep_lifter.L (array_lifter i) = idx\<^sub>L i"
    unfolding array_lifter_def \<alpha>_def by auto
  
  interpretation array_lifter: sep_lifter "array_lifter i" for i
    unfolding array_lifter_def by simp

  lemma pto_is_lift: "pto x = (\<lambda>BADDR i va \<Rightarrow> (\<up>(i\<ge>0) ** array_lifter.lift_assn (nat i) (vpto x va)))"  
    unfolding array_lifter.lift_assn_def
    apply (rule ext)
    apply (clarsimp simp: array_lifter_def pto_def split: baddr.splits)
    apply (intro ext)
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
    by (metis fun_upd_triv fun_upd_upd)
    
  lemma lift_is_pto: "i\<ge>0 \<Longrightarrow> array_lifter.lift_assn (nat i) (vpto x va) = pto x (BADDR i va)"  
    by (simp add: pto_is_lift sep_algebra_simps pred_lift_extract_simps)
    
  declare vpto_notZ[simp]  
    
  
  lemma load_rule: "htriple \<alpha> (pto x va) (load va) (\<lambda>r. \<up>(r=x) ** pto x va)"
    unfolding load_def
    supply pto_is_lift[simp]
    apply (cases va; clarsimp simp: htriple_extract_pre_pure sep_algebra_simps)
    using array_lifter.lift_operation[simplified, OF _ vload_rule, simplified] 
    .
    
  lemma store_rule: "htriple \<alpha> (pto xx va) (store x va) (\<lambda>_. pto x va)"
    unfolding store_def
    supply pto_is_lift[simp]
    apply (cases va; clarsimp simp: htriple_extract_pre_pure sep_algebra_simps)
    using array_lifter.lift_operation[simplified, OF _ vstore_rule, simplified] 
    .
    
  
  lemma load_pres_tag: "wlp (load a) (\<lambda>_ s'. tag_of s' = tag_of s) s"
    unfolding load_def 
    apply (auto simp: wlp_def run_simps tag_of_def split: prod.splits option.splits baddr.splits)
    apply (rule mwp_trivI)
    by auto

  lemma store_pres_tag: "wlp (store a x) (\<lambda>_ s'. tag_of s' = tag_of s) s"
    unfolding store_def 
    apply (auto simp: wlp_def run_simps tag_of_def split: prod.splits option.splits baddr.splits)
    apply (rule mwp_trivI)
    by auto
    
  lemma complete_tag: 
    "\<lbrakk>is_complete_tag ablock (tag_of cblock); ablock ## f; \<alpha> cblock = ablock + f\<rbrakk> \<Longrightarrow> f = 0"  
    apply (auto simp: is_complete_tag_def tag_of_def)
    by (smt \<alpha>_def disjoint_zero_sym list\<alpha>_in_range sep_add_disj_eq sep_disj_fun_def sep_disj_zero unique_zero vcompleteD)
    
  (* TODO: Move *)
  lemma Z_upd_eq_Z_iff[simp]: "0(i:=x) = 0 \<longleftrightarrow> x=0" by (auto simp: fun_eq_iff)
  
  lemma pto_notZ: "\<not> pto x a 0"
    apply (cases a)
    apply (auto simp: pto_def sep_algebra_simps)
    done
      
  lemma checked_idx_baddr_rule: "abase a 
    \<Longrightarrow> htriple \<alpha> (pto xx (a +\<^sub>a i)) (checked_idx_baddr a i) (\<lambda>r. \<up>(r=a +\<^sub>a i) ** pto xx (a +\<^sub>a i))"
    apply (rule htripleI')
    unfolding checked_idx_baddr_def check_addr_def pto_is_lift
    apply (clarsimp simp: pred_lift_extract_simps split: baddr.splits)
    apply (frule (1) array_lifter.infer_pre_get_with_frame, simp, simp)
    apply (force simp: wp_def run_simps aidx_baddr_def abase_baddr_def sep_algebra_simps split: prod.splits baddr.splits)
    done
    

  sublocale ba: block_allocator2 static_err mem_err load store check_addr \<alpha> pto tag_of is_complete_tag
    apply unfold_locales
    apply (rule load_rule)
    apply (rule store_rule)
    apply (rule load_pres_tag)
    apply (rule store_pres_tag)
    apply (rule complete_tag; assumption)
    apply (rule pto_notZ)
    done
       
      
  lemma list\<alpha>_rep_nn: "list\<alpha> \<alpha>v (replicate n v) n = 0"
    by (auto simp: list\<alpha>_def)
  
    
  lemma pto_this_exact: "pto x (BADDR i this_addr) = (\<up>(i\<ge>0) ** EXACT (0(nat i:=\<alpha>v x)))" 
    by (auto simp: pto_def vpto_this pred_lift_extract_simps del: ext intro!: ext)

  lemma ba_pto_this_exact: 
    "\<lbrakk>is_block_ptr p; i\<ge>0\<rbrakk> 
    \<Longrightarrow> ba.pto x (p +\<^sub>a i) = EXACT (0(rptr_the_block_index p := (0(nat i:=\<alpha>v x),0)))"  
    apply (auto 
      simp: ba.pto_def aidx_baddr_def pto_this_exact this_addr_baddr_def 
      simp: pred_lift_extract_simps is_block_ptr_def
      split: rptr.splits addr.splits baddr.splits)
    done
  
  lemma lift_pto_exact: "i\<ge>0 \<Longrightarrow> ba.block_lifter.lift_assn bi (pto v (this_addr +\<^sub>a i)) = EXACT (0(bi := (0(nat i:=\<alpha>v v),0)))"  
    apply (auto 
      simp:  aidx_baddr_def pto_this_exact this_addr_baddr_def 
      simp: pred_lift_extract_simps is_block_ptr_def
      split: rptr.splits addr.splits baddr.splits)
    done
    

  (* TODO: Move *)  
  lemma atLeast_lessThan_plus1: 
    "l\<le>v \<Longrightarrow> {l..<1+v::int} = insert v {l..<v}" 
    "l\<le>v \<Longrightarrow> {l..<v+1::int} = insert v {l..<v}" 
    by auto
    
  lemma sep_set_img_int_range_to_nat: "(\<Union>*i\<in>{0..<int n}. f i) = (\<Union>*i\<in>{0..<n}. f (int i))"  
    apply (induction n)
    apply (auto simp: atLeast_lessThan_plus1 atLeast0_lessThan_Suc)
    done
    
    
  lemma ba_block_alt: 
    "ba.block (\<alpha> (init v n)) p = (\<up>(is_block_ptr p) ** (\<Union>*i\<in>{0..<int n}. ba.pto v (p +\<^sub>a i)))"
  proof -
    have ba_block_alt_aux: "(\<Union>*i\<in>{0..<int n}. EXACT (0(x1 := (0(nat i := \<alpha>v v), 0)))) = EXACT (0(x1 := (list\<alpha> \<alpha>v (replicate n v), 0)))"
      for x1::nat
      apply (induction n)
      supply replicate_Suc_conv_snoc[simp] replicate_Suc[simp del]
      subgoal by (auto simp: sep_algebra_simps del: ext intro!: ext)
      subgoal
        apply simp
        by (auto 
          simp: list\<alpha>_snoc sep_algebra_simps sep_disj_fun_def atLeast0_lessThan_Suc atLeast_lessThan_plus1 sep_conj_def list\<alpha>_rep_nn
          cong del: if_cong 
          del: ext intro!: ext)
      done
    
    have foo: "\<lbrakk>P=Q; Q \<Longrightarrow> X=Y\<rbrakk> \<Longrightarrow> (\<up>P**X) = (\<up>Q**Y)" for P Q X Y by auto
    have [simp]: "(\<Union>*x\<in>{0..<int n}. ba.pto v ((RP_ADDR (ADDR x1 (this_addr +\<^sub>a x))))) 
      = (\<Union>*x\<in>{0..<int n}. EXACT (0(x1 := (0(nat x := \<alpha>v v), 0))))" for x1 
      apply (rule sep_set_img_cong)
      apply (auto simp: lift_pto_exact)
      done
  
    note [simp del] = ba.pto_addr_eq  
      
    show ?thesis
      unfolding init_def ba.block_def
      by (auto 
        split: rptr.splits addr.splits 
        simp: sep_algebra_simps
        simp: \<alpha>_def ba_block_alt_aux 
        intro!: foo
        )
  qed    

  
  lemma ba_block_exs_alt_aux: 
    assumes "n\<ge>0"
    shows "(\<Union>*i\<in>{0..<n}. (EXS x. ba.pto x ((RP_ADDR (ADDR bi (this_addr +\<^sub>a i)))))) 
      = (EXS xs. \<up>(int (length xs) = n) ** EXACT (0(bi := (list\<alpha> \<alpha>v xs, 0))))"  
    using assms
  proof (induction n rule: int_induct[where k=0])
    case base
    then show ?case by (auto simp: sep_algebra_simps pred_lift_extract_simps del: ext intro!: ext)
  next
    case (step1 n)

    
        
    note [simp] = \<open>0\<le>n\<close>
    note IH = step1.IH[simplified]

    have [simp]: "n+1\<noteq>0" using \<open>0\<le>n\<close> by linarith
        
    note replicate_Suc_conv_snoc[simp] replicate_Suc[simp del]
    show ?case
      apply (simp add: atLeast_lessThan_plus1)
      apply (simp add: IH)
      apply (rule ext)
      apply (auto simp: sep_algebra_simps pred_lift_extract_simps sep_disj_fun_def sep_conj_def list\<alpha>_at_len lift_pto_exact)
      subgoal for x xs
        apply (rule exI[where x="xs@[x]"])
        apply (auto del: ext intro!: ext simp: list\<alpha>_snoc sep_algebra_simps list\<alpha>_at_len
          simp: this_addr_baddr_def pto_this_exact
        )
        done
      subgoal for xs
        apply (rule exI[where x="last xs"])
        apply (rule exI[where x="butlast xs"]; simp)
        apply (cases xs rule: rev_cases)
        apply (auto simp: list\<alpha>_gt_len sep_algebra_simps list\<alpha>_snoc del: ext intro!: ext)
        done
      done
  next    
    case (step2 n) thus ?case by (auto)     
  qed 
  
  lemma ba_block_exs_alt: 
    "\<lbrakk>is_block_ptr p; n\<ge>0\<rbrakk> \<Longrightarrow> (\<Union>*i\<in>{0..<n}. EXS v. ba.pto v (p +\<^sub>a i)) = (EXS blk. \<up>(int (length blk) = n) ** ba.block (\<alpha> blk) p)"
    unfolding init_def ba.block_def
    supply [simp del] = ba.pto_addr_eq
    apply (cases p rule: ba.rptr_cases.cases; simp)
    apply (rule ext)
    apply (auto 
      split: rptr.splits addr.splits 
      simp: sep_algebra_simps pred_lift_extract_simps \<alpha>_def ba_block_exs_alt_aux
      )
    done
    
  lemma tag_of_init[simp]: "tag_of (init v n) = int n" by (auto simp: tag_of_def init_def)

  lemma ba_allocn_rule: "htriple ba.\<alpha> \<box> (ba_allocn v n) (\<lambda>r. (\<Union>*i\<in>{0..<int n}. ba.pto v (r +\<^sub>a i)) ** ba.tag (int n) r ** \<up>(abase r))"
    unfolding ba_allocn_def
    apply (rule cons_rule[OF ba.alloc_rule])
    apply simp
    apply (simp add: ba_block_alt sep_algebra_simps pred_lift_extract_simps)
    done

  (* TODO: Move to gen_wp locale *)          
  lemma wp_cons: "wp c Q s \<Longrightarrow> (\<And>x s. Q x s \<Longrightarrow> Q' x s) \<Longrightarrow> wp c Q' s"  
    by (simp add: wp_monoI)
    
  lemma blk_complete_tag[simp]: "is_complete_tag (\<alpha> blk) (int (length blk))"  
    by (auto simp: is_complete_tag_def \<alpha>_def list\<alpha>_def \<alpha>v_complete)

  (* TODO: is_base_ptr: This logic is already encoded in ba.tag! Try to get rid of is_base_ptr! *)  
  lemma ba_tag_extr_baseptr: "ba.tag n p = (\<up>(is_block_ptr p \<and> 0\<le>n) ** ba.tag n p)"  
    apply (rule ext)
    apply (auto simp: ba.tag_def sep_algebra_simps pred_lift_extract_simps split: addr.splits rptr.splits)
    apply (auto simp: tag_of_def)
    done
    
  lemma ba_freen_rule: "htriple ba.\<alpha> ((\<Union>*i\<in>{0..<n}. EXS v. ba.pto v (p+\<^sub>ai)) \<and>* ba.tag n p) (ba.free p) (\<lambda>_. \<box>)"
    apply (subst ba_tag_extr_baseptr)
    apply (rule htripleI')
    apply (clarsimp simp: sep_algebra_simps pred_lift_extract_simps)
    apply (simp add: ba_block_exs_alt)
    apply (clarsimp simp: sep_algebra_simps pred_lift_extract_simps)
    
    subgoal for pp s f blk
      supply R = ba.free_rule[of "\<alpha> blk" p "int (length blk)"]
      apply (rule R[THEN htripleD', THEN wp_cons])
      apply assumption+
      apply (simp add: sep_algebra_simps)
      apply (simp add: sep_algebra_simps)
      done
    done
    
  lemma checked_idx_baddr_pres_tag: "wlp (checked_idx_baddr (BADDR a b) i) (\<lambda>_ s'. tag_of s' = tag_of sa) sa"  
    by (auto simp: wlp_def checked_idx_baddr_def check_addr_def run_simps split: prod.splits baddr.splits)
    
  (* TODO: Move *)  
  lemma return_rule: "htriple \<alpha> P (return x) (\<lambda>r. \<up>(r=x)**P)" for \<alpha>
    by vcg
    
  (* TODO: Move *)  
  lemma wlp_return[simp]: "wlp (return x) Q s = Q x s"
    by (auto simp: wlp_def run_simps)
    
  lemma checked_idx_ptr_rule: "abase p 
    \<Longrightarrow> htriple ba.\<alpha> (ba.pto xx (p +\<^sub>a i)) (checked_idx_ptr p i) (\<lambda>r. \<up>(r=p +\<^sub>a i) ** ba.pto xx (p +\<^sub>a i))"
    unfolding checked_idx_ptr_def
    apply (cases p rule: ba.rptr_cases.cases; simp add: zoom_bind)
    supply [vcg_rules] = ba.block_lifter.lift_operation[simplified, OF _ _ checked_idx_baddr_rule]
    supply [vcg_rules] = ba.block_lifter.lift_operation[simplified, OF _ _ return_rule]
    supply [simp] = pto_notZ checked_idx_baddr_pres_tag abase_baddr_def
    supply [named_ss fri_prepare_simps] = aidx_baddr_simp
    supply [split] = baddr.splits
    apply vcg
    done
    
end
  
end

