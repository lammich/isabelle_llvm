section \<open>Values\<close>
theory Sep_Value
imports 
  "../../lib/Monad"
begin

  subsection \<open>Values and Addresses\<close>
  datatype 'a val = STRUCT (fields: "'a val list") | PRIMITIVE (the: 'a)
  hide_const (open) val.fields val.the
  define_lenses (open) val
  
  datatype va_item = PFLD (the_va_item_idx: nat)
  type_synonym vaddr = "va_item list"
  
  subsection \<open>Focusing on Address\<close>
  fun lens_of_item where
    "lens_of_item (PFLD i) = val.fields\<^sub>L \<bullet>\<^sub>L idx\<^sub>L i"
  
  definition "lens_of_vaddr vp = foldr (\<lambda>i L. lens_of_item i \<bullet>\<^sub>L L) vp id\<^sub>L"
  
  lemma lens_of_vaddr_simps[simp]:
    "lens_of_vaddr [] = id\<^sub>L"
    "lens_of_vaddr (i#is) = lens_of_item i \<bullet>\<^sub>L lens_of_vaddr is"
    unfolding lens_of_vaddr_def
    by auto
    
  lemma ex_two_vals[simp, intro]: "\<exists>a b::'a val. a \<noteq> b" by auto

  lemma lens_of_item_rnl[simp, intro!]: "rnlens (lens_of_item i :: 'a val \<Longrightarrow> 'a val)"  
  proof (cases i)
    case [simp]: (PFLD i)
    show ?thesis 
      apply (rule rnlensI[where x="PRIMITIVE undefined" and y="STRUCT undefined" and s="STRUCT (replicate (Suc i) undefined)"])
      by simp_all
      
  qed

  lemma lens_of_item_hlens[simp, intro!]: "hlens (lens_of_item i :: 'a val \<Longrightarrow> 'a val)"  
    by (cases i) (auto)
  
  
  lemma lens_of_vaddr_rnl[simp, intro!]: "rnlens (lens_of_vaddr vp)"
    by (induction vp) auto
  
  lemma lens_of_vaddr_hlens[simp, intro!]: "hlens (lens_of_vaddr vp)"
    by (induction vp) auto
    
  lemma lens_of_item_complete[simp, intro!]: "complete_lens (lens_of_item i)"
    apply (rule)
    apply (simp; fail)
    by (meson lens.get_put lens.get_put_pre lens_of_item_rnl rnlens_def)
    
  subsection \<open>Loading and Storing Address\<close>
  definition "vload err a \<equiv> zoom (lift_lens err (lens_of_vaddr a)) Monad.get"  
  definition "vstore err x a \<equiv> zoom (lift_lens err (lens_of_vaddr a)) (Monad.set x)"

  
  subsection \<open>GEP\<close>
  
  definition "checked_gep err addr item \<equiv> doM {
    let addr = addr@[item];
    use (lift_lens err (lens_of_vaddr addr));
    return addr
  }"
  
  
  subsection \<open>Structure of Value\<close>
  datatype 's vstruct = VS_STRUCT "'s vstruct list" | VS_PRIMITIVE 's
  
  locale structured_value_defs =
    fixes struct_of_primval :: "'a \<Rightarrow> 's"
      and init_primval :: "'s \<Rightarrow> 'a"
  begin
    fun struct_of_val :: "'a val \<Rightarrow> 's vstruct" where
      "struct_of_val (STRUCT fs) = VS_STRUCT (map struct_of_val fs)"
    | "struct_of_val (PRIMITIVE x) = VS_PRIMITIVE (struct_of_primval x)"

    fun init_val :: "'s vstruct \<Rightarrow> 'a val" where
      "init_val (VS_STRUCT fs) = STRUCT (map init_val fs)"
    | "init_val (VS_PRIMITIVE ps) = PRIMITIVE (init_primval ps)"  
      
  end    
  
  lemmas structured_value_code[code] =
    structured_value_defs.struct_of_val.simps
    structured_value_defs.init_val.simps
  
  locale structured_value = structured_value_defs struct_of_primval init_primval 
    for struct_of_primval :: "'a \<Rightarrow> 's"
      and init_primval :: "'s \<Rightarrow> 'a" +
    assumes struct_of_init_primval[simp]: "struct_of_primval (init_primval s) = s"  
  begin
  
    lemma put_preserves_struct:
      assumes "pre_get (lens_of_vaddr a) s"
      assumes "struct_of_val (get' (lens_of_vaddr a) s) = struct_of_val x"
      shows "struct_of_val (put' (lens_of_vaddr a) x s) = struct_of_val s"
      using assms
    proof (induction a arbitrary: s)
      case Nil
      then show ?case by auto
    next
      case (Cons i as)
      then show ?case 
        by (cases s; cases i; simp add: map_upd_eq)
        
    qed
    
    lemma struct_of_init[simp]: "struct_of_val (init_val s) = s"
      apply (induction s) 
      by (auto simp: map_idI)
    
    
  end
  
end
