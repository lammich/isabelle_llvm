section \<open>The LLVM Memory Model\<close>
theory LLVM_Memory
imports 
  Sep_Value 
  Sep_Array_Block
  "../../lib/LLVM_Integer" 
begin

  text \<open>In this theory, we assemble the final LLVM memory model from the 
    block-allocator, array-block, and value concepts.
    
    For a better abstraction barrier, we create an own layer of data types.
  \<close>

  subsection \<open>Monad Setup\<close>
  datatype err = is_static: STATIC_ERROR string | MEM_ERROR | UNINIT_ERROR | OVERFLOW_ERROR
  hide_const (open) is_static


  subsection \<open>Primitive Values\<close>
  datatype llvm_primval = PV_PTR "vaddr baddr addr rptr" | PV_INT lint
  
  datatype llvm_primval_struct = PVS_PTR | PVS_INT nat
  
  fun struct_of_primval where
    "struct_of_primval (PV_PTR _) = PVS_PTR"
  | "struct_of_primval (PV_INT i) = PVS_INT (width i)"

  fun init_primval where
    "init_primval PVS_PTR = PV_PTR RP_NULL"
  | "init_primval (PVS_INT w) = PV_INT (lconst w 0)"
  
  lemma struct_of_init_primval_aux: "struct_of_primval (init_primval s) = s"
    by (induction s) auto
  
  subsection \<open>Instantiation of the Generic Memory Model\<close>  
  interpretation structured_value struct_of_primval init_primval by standard (auto simp: struct_of_init_primval_aux)
  
  instantiation list :: (type) this_addr begin definition [simp]: "this_addr = []" instance .. end
  
  interpretation ab: array_block1 "STATIC_ERROR ''''" MEM_ERROR "vload MEM_ERROR::_ \<Rightarrow> (llvm_primval val,_,_,_) M" "vstore MEM_ERROR" "checked_gep MEM_ERROR" .
    

  subsection \<open>Memory Model Interface\<close>
  
  subsubsection \<open>Types\<close>
  text \<open>We wrap the concepts of pointer, value, memory, and value-structure in to 
    their own datatypes, to set a clear abstraction barrier between the internals 
    of the memory model, and its interface.\<close>
  
  type_synonym base_llvm_addr = "vaddr baddr addr"
  type_synonym base_llvm_ptr = "vaddr baddr addr rptr"
  type_synonym base_llvm_val = "llvm_primval val"
  type_synonym base_llvm_block = "base_llvm_val block"
  type_synonym base_llvm_memory = "base_llvm_val block memory"
  type_synonym base_llvm_vstruct = "llvm_primval_struct vstruct"
      
  datatype llvm_ptr = LLVM_PTR (the_ptr: "base_llvm_ptr")
  datatype llvm_val = LLVM_VAL (the_val: "base_llvm_val")
  datatype llvm_memory = LLVM_MEMORY (the_memory: "base_llvm_memory")
  datatype llvm_vstruct = LLVM_VSTRUCT (the_vstruct: "base_llvm_vstruct")
    
  hide_const (open) the_ptr the_val the_memory the_vstruct

  subsubsection \<open>Functions\<close>
  text \<open>Internal functions\<close> (* TODO: Clearly mark by name! *)
  definition "llvm_zoom_base \<alpha> m \<equiv> doM {r\<leftarrow>mblock llvm_memory.the_memory LLVM_MEMORY m; return (\<alpha> r)}"
  definition "llvm_store_unchecked x p \<equiv> llvm_zoom_base id (ab.ba.store (llvm_val.the_val x) (llvm_ptr.the_ptr p))"

  text \<open>Interface Functions\<close>
  definition "llvm_vstruct v \<equiv> LLVM_VSTRUCT (struct_of_val (llvm_val.the_val v))"
    
  definition "llvm_load p \<equiv> llvm_zoom_base LLVM_VAL (ab.ba.load (llvm_ptr.the_ptr p))"
  definition "llvm_store x p \<equiv> doM {
    xx \<leftarrow> llvm_load p;
    fcheck (STATIC_ERROR ''Value structure mismatch'') (llvm_vstruct xx = llvm_vstruct x);
    llvm_store_unchecked x p
  }"


  definition "llvm_allocn v n \<equiv> llvm_zoom_base LLVM_PTR (ab.ba_allocn (llvm_val.the_val v) n)"
  definition "llvm_free p \<equiv> llvm_zoom_base id (ab.ba.free (llvm_ptr.the_ptr p))"
    
  definition "llvm_check_ptr p \<equiv> llvm_zoom_base id (ab.ba.check_ptr (llvm_ptr.the_ptr p))"
  
  definition "llvm_checked_idx_ptr p i \<equiv> llvm_zoom_base LLVM_PTR (ab.checked_idx_ptr (llvm_ptr.the_ptr p) i)"
  definition "llvm_checked_gep p i \<equiv> llvm_zoom_base LLVM_PTR (ab.checked_gep_ptr (llvm_ptr.the_ptr p) i)"
  
  
  definition "llvm_empty_memory \<equiv> LLVM_MEMORY ab.ba.empty_memory"
  
  
  fun llvm_is_int where
    "llvm_is_int (LLVM_VAL (PRIMITIVE (PV_INT _))) = True"
  | "llvm_is_int _ = False"  
  
  fun llvm_is_ptr where
    "llvm_is_ptr (LLVM_VAL (PRIMITIVE (PV_PTR _))) = True"
  | "llvm_is_ptr _ = False"  
  
  fun llvm_is_pair where
    "llvm_is_pair (LLVM_VAL (PAIR _ _)) = True"
  | "llvm_is_pair _ = False"  
    
  definition "llvm_int i \<equiv> LLVM_VAL (PRIMITIVE (PV_INT i))"
  definition "llvm_null \<equiv> LLVM_PTR RP_NULL"
  definition "llvm_ptr p \<equiv> LLVM_VAL (PRIMITIVE (PV_PTR (llvm_ptr.the_ptr p)))"
  definition "llvm_pair a b \<equiv> LLVM_VAL (PAIR (llvm_val.the_val a) (llvm_val.the_val b))"

  definition "llvm_the_int v \<equiv> case v of LLVM_VAL (PRIMITIVE (PV_INT i)) \<Rightarrow> i"
  definition "llvm_the_ptr p \<equiv> case p of LLVM_VAL (PRIMITIVE (PV_PTR p)) \<Rightarrow> LLVM_PTR p"
  definition "llvm_the_pair p \<equiv> case p of LLVM_VAL (PAIR a b) \<Rightarrow> (LLVM_VAL a, LLVM_VAL b)"
    
  fun llvm_is_s_int where
    "llvm_is_s_int w (LLVM_VSTRUCT (VS_PRIMITIVE (PVS_INT w'))) \<longleftrightarrow> w'=w"
  | "llvm_is_s_int _ _ \<longleftrightarrow> False"  
      
  fun llvm_is_s_ptr where
    "llvm_is_s_ptr (LLVM_VSTRUCT (VS_PRIMITIVE (PVS_PTR))) \<longleftrightarrow> True"
  | "llvm_is_s_ptr _ \<longleftrightarrow> False"  

  fun llvm_is_s_pair where
    "llvm_is_s_pair (LLVM_VSTRUCT (VS_PAIR _ _)) \<longleftrightarrow> True"
  | "llvm_is_s_pair _ \<longleftrightarrow> False"  
  
        
  definition "llvm_s_int w \<equiv> LLVM_VSTRUCT (VS_PRIMITIVE (PVS_INT w))"
  definition "llvm_s_ptr \<equiv> LLVM_VSTRUCT (VS_PRIMITIVE (PVS_PTR))"
  definition "llvm_s_pair a b \<equiv> LLVM_VSTRUCT (VS_PAIR (llvm_vstruct.the_vstruct a) (llvm_vstruct.the_vstruct b))"

  
  (* TODO: Cleanly spread zero-initializer over memory model levels! *)
  fun zero_initializer where
    "zero_initializer (VS_PAIR a b) = PAIR (zero_initializer a) (zero_initializer b)"
  | "zero_initializer (VS_PRIMITIVE PVS_PTR) = PRIMITIVE (PV_PTR RP_NULL)"
  | "zero_initializer (VS_PRIMITIVE (PVS_INT n)) = PRIMITIVE (PV_INT (lconst n 0))"

  definition "llvm_zero_initializer s = LLVM_VAL (zero_initializer (llvm_vstruct.the_vstruct s))"
  
  lemma llvm_is_simps[simp]:
    " llvm_is_int (llvm_int i)"
    "\<not>llvm_is_int (llvm_ptr p)"
    "\<not>llvm_is_int (llvm_pair v\<^sub>1 v\<^sub>2)"
    
    "\<not>llvm_is_ptr (llvm_int i)"
    " llvm_is_ptr (llvm_ptr p)"
    "\<not>llvm_is_ptr (llvm_pair v\<^sub>1 v\<^sub>2)"
  
    "\<not>llvm_is_pair (llvm_int i)"
    "\<not>llvm_is_pair (llvm_ptr p)"
    " llvm_is_pair (llvm_pair v\<^sub>1 v\<^sub>2)"
    unfolding llvm_int_def llvm_ptr_def llvm_pair_def 
    by auto
    
  
  lemma llvm_the_int_inv[simp]: "llvm_the_int (llvm_int i) = i"
    by (auto simp: llvm_the_int_def llvm_int_def)

  lemma llvm_the_ptr_inv[simp]: "llvm_the_ptr (llvm_ptr p) = p"
    by (auto simp: llvm_the_ptr_def llvm_ptr_def)
    
  lemma llvm_the_pair_inv[simp]: "llvm_the_pair (llvm_pair a b) = (a,b)"
    by (auto simp: llvm_the_pair_def llvm_pair_def)
    
  lemma llvm_int_inj[simp]: "llvm_int a = llvm_int b \<longleftrightarrow> a=b" by (auto simp: llvm_int_def)
  lemma llvm_ptr_inj[simp]: "llvm_ptr a = llvm_ptr b \<longleftrightarrow> a=b" by (cases a; cases b) (auto simp: llvm_ptr_def)
  lemma llvm_pair_inj[simp]: "llvm_pair a b = llvm_pair a' b' \<longleftrightarrow> a=a' \<and> b=b'" 
    by (auto simp: llvm_pair_def llvm_val.the_val_def split: llvm_val.splits)  
      
  lemma llvm_v_disj[simp]:  
    "llvm_int i \<noteq> llvm_ptr p"
    "llvm_int i \<noteq> llvm_pair a b"
    "llvm_ptr p \<noteq> llvm_int i"
    "llvm_ptr p \<noteq> llvm_pair a b"
    "llvm_pair a b \<noteq> llvm_int i"
    "llvm_pair a b \<noteq> llvm_ptr p"
    unfolding llvm_int_def llvm_ptr_def llvm_pair_def by auto 
            
  lemma llvm_s_int[simp]: "llvm_vstruct (llvm_int i) = llvm_s_int (width i)"
    by (auto simp: llvm_vstruct_def llvm_s_int_def llvm_int_def)

  lemma llvm_s_ptr[simp]: "llvm_vstruct (llvm_ptr p) = llvm_s_ptr"
    by (auto simp: llvm_vstruct_def llvm_s_ptr_def llvm_ptr_def)
      
  lemma llvm_s_pair[simp]: "llvm_vstruct (llvm_pair a b) = llvm_s_pair (llvm_vstruct a) (llvm_vstruct b)"
    by (auto simp: llvm_vstruct_def llvm_s_pair_def llvm_pair_def)

  lemma llvm_s_pair_inj[simp]: "llvm_s_pair a b = llvm_s_pair c d \<longleftrightarrow> a=c \<and> b=d"
    unfolding llvm_s_pair_def by (cases a; cases b) auto
  
  lemma llvm_s_disj[simp]:
    "llvm_s_int w \<noteq> llvm_s_ptr"
    "llvm_s_int w \<noteq> llvm_s_pair t1 t2"
    "llvm_s_ptr \<noteq> llvm_s_int w"
    "llvm_s_ptr \<noteq> llvm_s_pair t1 t2"
    "llvm_s_pair t1 t2 \<noteq> llvm_s_int w"
    "llvm_s_pair t1 t2 \<noteq> llvm_s_ptr"
    unfolding llvm_s_int_def llvm_s_ptr_def llvm_s_pair_def 
    by auto
    
  lemma llvm_vstruct_cases[cases type]:
    obtains w where "s = llvm_s_int w" | "s = llvm_s_ptr" | s\<^sub>1 s\<^sub>2 where "s = llvm_s_pair s\<^sub>1 s\<^sub>2"
  proof (cases s)
    case [simp]: (LLVM_VSTRUCT x)
    show ?thesis proof (cases x)
      case [simp]: (VS_PAIR x11 x12)
      show ?thesis using that
        by (clarsimp simp: llvm_s_pair_def) (metis llvm_vstruct.sel)
      
    next
      case (VS_PRIMITIVE x2)
      then show ?thesis apply (cases x2)
        using that by (auto simp: llvm_s_ptr_def llvm_s_int_def)
    qed
  qed
  
  lemma llvm_v_cases[cases type]:
    obtains i where "v = llvm_int i" | p where "v = llvm_ptr p" | v1 v2 where "v = llvm_pair v1 v2"
    apply (cases v) subgoal for x apply (cases x)
    subgoal apply (auto simp: llvm_pair_def) by (metis llvm_val.sel)
    subgoal for xx apply (cases xx)
      apply (auto simp: llvm_int_def llvm_ptr_def)
      by (metis llvm_ptr.sel)
      done
    done
  
  lemma struct_of_zero_initializer[simp]: "struct_of_val (zero_initializer s) = s"  
    by (induction s rule: zero_initializer.induct) auto
    
  lemma llvm_vstruct_of_zero_initializer[simp]: "llvm_vstruct (llvm_zero_initializer s) = s"
    unfolding llvm_zero_initializer_def llvm_vstruct_def by simp

  lemma llvm_zero_initializer_simps[simp]:
    "llvm_zero_initializer (llvm_s_int w) = llvm_int (lconst w 0)"
    "llvm_zero_initializer llvm_s_ptr = llvm_ptr llvm_null"
    "llvm_zero_initializer (llvm_s_pair s1 s2) = llvm_pair (llvm_zero_initializer s1) (llvm_zero_initializer s2)"
    unfolding llvm_zero_initializer_def llvm_s_int_def llvm_s_ptr_def llvm_s_pair_def
      llvm_int_def llvm_ptr_def llvm_null_def llvm_pair_def
    by auto
  
  
    
          
    
  subsection \<open>Alternative Characterizations\<close>  
    
  text \<open>These are some alternative characterizations, that might be easier to present, 
    but break the abstraction barriers.
    
    Note that this section adds nothing to the memory model itself, it only derives
    alternative characterizations of the existing functions.
  \<close>
  
  subsubsection \<open>Setup\<close>
  
  define_lenses llvm_memory  
  define_lenses rptr
    
  (* TODO: Move to Lenses Library *)
  definition "no\<^sub>L \<equiv> LENS (\<lambda>_. None) (\<lambda>_ _. None)"
  lemma no_hlens[simp]: "hlens no\<^sub>L"
    unfolding no\<^sub>L_def apply unfold_locales apply (auto split:if_splits) done
    
  lemma noL_pre[simp]:
    "\<not>pre_get no\<^sub>L s"  
    "\<not>pre_put no\<^sub>L s"  
    unfolding no\<^sub>L_def apply (auto split:if_splits) done
    
  lemma noL_comp_left[simp]: "no\<^sub>L \<bullet>\<^sub>L L = no\<^sub>L"
    by (cases L; auto simp: no\<^sub>L_def comp\<^sub>L_def)

  lemma noL_comp_right[simp]: "L \<bullet>\<^sub>L no\<^sub>L = no\<^sub>L"
    by (cases L; auto simp: no\<^sub>L_def comp\<^sub>L_def)
    
  lemma epre_get_noL[simp]: "epre_get (lift_lens e no\<^sub>L) s = Some e" by simp
    
  lemma use_lift_noL[simp]: "use (lift_lens e no\<^sub>L) = fail e"
    apply rule
    apply (auto simp: run_simps)
    done
  
  lemma assign_lift_noL[simp]: "lift_lens e no\<^sub>L ::= x = fail e"
    apply rule
    apply (auto simp: run_simps)
    done
  
  (* TODO: Move to Lenses Library *)
    
  definition "assertL \<Phi> \<equiv> if \<Phi> then id\<^sub>L else no\<^sub>L"
  lemma assertL_hlens[simp]: "hlens (assertL \<Phi>)"
    unfolding assertL_def apply unfold_locales apply (auto split:if_splits) done
  
  lemma assertL_True[simp]: "assertL True = id\<^sub>L" unfolding assertL_def id\<^sub>L_def by auto
  lemma assertL_False[simp]: "assertL False = no\<^sub>L" unfolding assertL_def id\<^sub>L_def by auto
  
  lemma pre_get_assertL[simp]: "pre_get (assertL \<Phi>) x = \<Phi>" by (cases \<Phi>; auto)
  
  subsubsection \<open>Alternative Characterization of Memory Functions\<close>
  
  fun baddr_lens where "baddr_lens (BADDR i va) = assertL (i\<ge>0) \<bullet>\<^sub>L idx\<^sub>L (nat i) \<bullet>\<^sub>L lens_of_vaddr va"
  fun addr_lens where "addr_lens (ADDR bi ba) = the_memory\<^sub>L \<bullet>\<^sub>L memory.the_memory\<^sub>L \<bullet>\<^sub>L idx\<^sub>L bi \<bullet>\<^sub>L the\<^sub>L \<bullet>\<^sub>L baddr_lens ba"
  
  lemma baddr_lens[simp]: "lens (baddr_lens ba)" by (cases ba) auto
  lemma addr_lens[simp]: "lens (addr_lens a)" by (cases a) auto
  
  definition "ptr_lens p \<equiv> assertL (llvm_ptr.the_ptr p \<noteq> RP_NULL) \<bullet>\<^sub>L addr_lens (rptr.the_addr (llvm_ptr.the_ptr p))"
  
  lemma ptr_lens_null[simp]: "ptr_lens (LLVM_PTR RP_NULL) = no\<^sub>L"
    unfolding ptr_lens_def by auto

  find_theorems assertL  
    
  lemma llvm_load_alt_aux: "xs!i = k \<Longrightarrow> xs[i:=k] = xs" by auto
    
  lemma llvm_load_alt: "llvm_load p = doM { r\<leftarrow>use (lift_lens MEM_ERROR (ptr_lens p)); return (LLVM_VAL r)}"
    unfolding llvm_load_def llvm_zoom_base_def ptr_lens_def ab.ba.load_def
    apply (cases p; simp)
    subgoal for pp apply (cases pp; simp)
      subgoal for addr
        apply (rule) 
        subgoal for s apply (cases s; simp)
          unfolding ab.load_def ab.ba.lens_of_bi_def vload_def
          apply (cases addr; clarsimp simp: run_simps split!: option.splits)
          apply (auto simp: run_simps llvm_load_alt_aux split!: baddr.splits option.splits)
          done
        done 
      done 
    done
  
  lemma "llvm_store x p = doM { 
    let L = (lift_lens MEM_ERROR (ptr_lens p));
    xx \<leftarrow> use L;
    fcheck (STATIC_ERROR ''Value structure mismatch'') (llvm_vstruct (LLVM_VAL xx) = llvm_vstruct x);
    L ::= llvm_val.the_val x
  }"
    unfolding llvm_store_def llvm_zoom_base_def ab.ba.store_def llvm_load_alt
    apply (induction x rule: llvm_val.induct; cases p; simp ) (* TODO: How to access case-rule for llvm_val? Induction is overkill here! *)
    subgoal for val pp
      apply (cases pp; simp)
      subgoal for addr 
        apply (rule)
        subgoal for s apply (cases s; simp)
        apply (cases addr; simp add: Let_def)
        apply (auto simp: run_simps mwp_def split: addr.splits option.splits mres.splits)
        apply (determ \<open>thin_tac "_"\<close>)+
        unfolding llvm_store_unchecked_def ab.ba.store_def llvm_zoom_base_def ptr_lens_def ab.ba.lens_of_bi_def
        apply (auto simp: run_simps mwp_def split!: option.splits mres.split)
        apply (auto simp: run_simps ab.store_def vstore_def split: baddr.splits if_splits option.splits)
        apply (case_tac x42)
        apply auto
        done
      done
    done
  done
  
  
  lemma "llvm_allocn v n = llvm_zoom_base LLVM_PTR
     (zoom (lift_lens (STATIC_ERROR []) memory.the_memory\<^sub>L)
       (doM {
          blocks \<leftarrow> Monad.get;
          Monad.set (blocks @ [Some (replicate n (llvm_val.the_val v))]);
          return (RP_ADDR (ADDR (length blocks) this_addr))
        }))"
    by (simp add: llvm_allocn_def ab.ba_allocn_def ab.ba.alloc_def ab.init_def)

    
  lemma "llvm_free p = llvm_zoom_base id
     (zoom (lift_lens (STATIC_ERROR []) memory.the_memory\<^sub>L)
     (case llvm_ptr.the_ptr p of RP_NULL \<Rightarrow> fail MEM_ERROR
      | RP_ADDR (ADDR bi ba) \<Rightarrow> doM {
            fcheck MEM_ERROR (ba = this_addr);
            blocks \<leftarrow> Monad.get;
            fcheck MEM_ERROR (bi<length blocks \<and> blocks!bi\<noteq>None);
            Monad.set (blocks[bi:=None])
          }))"
    apply rule
    apply (auto 
      simp: run_simps llvm_free_def ab.ba.free_def llvm_zoom_base_def
      split: rptr.splits option.splits addr.splits
      )
    done
    
  
end
