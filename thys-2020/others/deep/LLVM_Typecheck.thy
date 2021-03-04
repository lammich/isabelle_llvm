theory LLVM_Typecheck
  imports 
    LLVM_Semantics LLVM_Pretty
begin
abbreviation "no_static_err e \<equiv> \<not>err.is_static e"

lemma fold_elens[simp]:
  "\<lbrakk>elens L; \<And>x. x\<in>list.set xs \<Longrightarrow> elens (f x)\<rbrakk> \<Longrightarrow> elens (fold (\<lambda>x p. p \<bullet> f x) xs L)"
  by (induction xs arbitrary: L) auto

lemma foldr_elens[simp]:
  "\<lbrakk>elens L; \<And>x. x\<in>list.set xs \<Longrightarrow> elens (f x)\<rbrakk> \<Longrightarrow> elens (foldr (\<lambda>x p. f x \<bullet> p) xs L)"
  by (induction xs arbitrary: L) auto


lemma [simp]: "elens (array_item\<^sub>L idx)" by (auto simp: array_item\<^sub>L_def)
lemma [simp]: "elens (struct_field\<^sub>L idx)" by (auto simp: struct_field\<^sub>L_def)

lemma [simp]: "elens (lens_of_vai vai)" by (cases vai) auto

lemma [simp]: "elens (lens_of_vaddr va)" unfolding lens_of_vaddr_def by auto


lemma [simp]: "put' mem\<^sub>L x s = MEM x"
  by (auto simp: mem\<^sub>L_def split: memory.split)

lemma blockL_pre_simp[simp]: "epre_get (blockL b) \<mu> = (
  if \<not> the_block b < length (get' mem\<^sub>L \<mu>) then
    Some (STATIC_ERROR ''lens'')
  else if (get' mem\<^sub>L \<mu>)!the_block b = None then
    Some MEM_ERROR
  else
    None
)"
  unfolding blockL_def
  by (auto split: option.split)

lemma blockL_get_simp[simp]:
  "\<lbrakk>the_block b < length (get' mem\<^sub>L \<mu>); (get' mem\<^sub>L \<mu>)!the_block b = Some (v,bty)\<rbrakk>
    \<Longrightarrow> eget' (blockL b) \<mu> = v"
  unfolding blockL_def
  by (auto split: option.split)

lemma blockL_put_simp[simp]:
  "\<lbrakk>the_block b < length (get' mem\<^sub>L \<mu>); (get' mem\<^sub>L \<mu>)!the_block b = Some (vv,bty)  \<rbrakk>
    \<Longrightarrow> eput' (blockL b) v \<mu> = MEM (get' mem\<^sub>L \<mu> [the_block b := Some (v,bty)])"
  unfolding blockL_def
  by (auto split: option.split)


lemma lens_of_vaddr_Nil[simp]:
  "lens_of_vaddr [] = (id\<^sub>L)\<^sub>S"
  by (auto simp: lens_of_vaddr_def)

lemma lens_of_vaddr_Cons[simp]:
  "lens_of_vaddr (va#vas) = lens_of_vai va \<bullet> lens_of_vaddr vas"
  by (auto simp: lens_of_vaddr_def)


lemma of_type_inv2[simp]:
  "of_type \<mu>T (TARRAY n bT) bv \<longleftrightarrow> (\<exists>vs. bv = VARRAY vs \<and> n = length vs \<and> (\<forall>v\<in>list.set vs. of_type \<mu>T bT v))"
  by (cases bv) auto


lemma [simp]:
  "epre_get (array_item\<^sub>L i) x = (case x of VARRAY vs \<Rightarrow> if i<length vs then None else Some MEM_ERROR | _ \<Rightarrow> Some (STATIC_ERROR ''lens''))"
  "epre_put (array_item\<^sub>L i) v x = epre_get (array_item\<^sub>L i) x"
  "i<length vs \<Longrightarrow> eget' (array_item\<^sub>L i) (VARRAY vs) = vs!i"
  "i<length vs \<Longrightarrow> eput' (array_item\<^sub>L i) v (VARRAY vs) = VARRAY (vs[i:=v])"
  by (auto simp: array_item\<^sub>L_def split: option.split val.splits)

lemma [simp]:
  "epre_get (struct_field\<^sub>L i) x = (case x of VSTRUCT vs \<Rightarrow> if i<length vs then None else Some (STATIC_ERROR ''lens'') | _ \<Rightarrow> Some (STATIC_ERROR ''lens''))"
  "epre_put (struct_field\<^sub>L i) v x = epre_get (struct_field\<^sub>L i) x"
  "i<length vs \<Longrightarrow> eget' (struct_field\<^sub>L i) (VSTRUCT vs) = vs!i"
  "i<length vs \<Longrightarrow> eput' (struct_field\<^sub>L i) v (VSTRUCT vs) = VSTRUCT (vs[i:=v])"
  by (auto simp: struct_field\<^sub>L_def split: option.split val.splits)

lemma tyco_get_lens_of_vaddr_aux:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T"
  shows "case epre_get (lens_of_vaddr p) bv of
    None \<Rightarrow> of_type \<mu>T T (eget' (lens_of_vaddr p) bv)
  | Some e \<Rightarrow> \<not>err.is_static e
  "
  using assms
  apply (induction bT p T arbitrary: bv rule: vaddr_of_type.induct)
  apply (auto split: option.splits val.splits simp: Ball_def in_set_conv_nth list_all2_conv_all_nth)
  apply force+
  done

lemma tyco_get_lens_of_vaddr:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T"
  shows "epre_get (lens_of_vaddr p) bv = None \<Longrightarrow> of_type \<mu>T T (eget' (lens_of_vaddr p) bv)"
    and "epre_get (lens_of_vaddr p) bv = Some e \<Longrightarrow> \<not>err.is_static e"
  using tyco_get_lens_of_vaddr_aux[OF assms] by (auto)

lemma tyco_put_lens_of_vaddr_aux:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T" "of_type \<mu>T T v"
  shows "case epre_put (lens_of_vaddr p) v bv of
      None \<Rightarrow> of_type \<mu>T bT (eput' (lens_of_vaddr p) v bv)
    | Some e \<Rightarrow> \<not>err.is_static e"
  using assms
  apply (induction bT p T arbitrary: bv rule: vaddr_of_type.induct)
  apply (auto split: option.splits val.splits simp: Ball_def in_set_conv_nth list_all2_conv_all_nth nth_list_update)
  apply force+
  done

lemma tyco_put_lens_of_vaddr:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T" "of_type \<mu>T T v"
  shows "epre_put (lens_of_vaddr p) v bv = None \<Longrightarrow> of_type \<mu>T bT (eput' (lens_of_vaddr p) v bv)"
    and "epre_put (lens_of_vaddr p) v bv = Some e \<Longrightarrow> \<not>err.is_static e"
  using tyco_put_lens_of_vaddr_aux[OF assms] by (auto)


lemma tyco_use_lens_of_addr:
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "addr_of_type \<mu>T a T"
  shows "mwp (run (use (lens_of_addr a)) \<mu>) bot no_static_err bot (\<lambda>v \<mu>'. \<mu>'=\<mu> \<and> of_type \<mu>T T v)"
  using assms
  apply (cases a)
  apply (auto
    simp: run_simps addr_of_type_def Let_def mem_of_type_def list_all2_conv_all_nth
    simp: tyco_get_lens_of_vaddr
    split: if_splits option.splits)
  done

lemma tyco_put_lens_of_addr:
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "addr_of_type \<mu>T a T"
  assumes "of_type \<mu>T T v"
  shows "mwp (run ((lens_of_addr a := v)) \<mu>) bot no_static_err bot (\<lambda>_ \<mu>'. mem_of_type \<mu>T \<mu>')"
  using assms
  apply (cases a)
  apply (auto 0 3
    simp: run_simps addr_of_type_def Let_def mem_of_type_def list_all2_conv_all_nth
    simp: tyco_put_lens_of_vaddr nth_list_update
    split: if_splits option.splits)
  done


term "allocate"

fun memT_le where "memT_le (MEM_TYPE \<mu>T) (MEM_TYPE \<mu>T') \<longleftrightarrow>
  length \<mu>T \<le> length \<mu>T' \<and> (\<forall>i<length \<mu>T. \<mu>T'!i = None \<or> \<mu>T'!i=\<mu>T!i)"

lemma memT_le_refl[intro!,simp]: "memT_le \<mu>T \<mu>T"
  by (cases \<mu>T) auto

lemma memT_le_trans[trans]: "memT_le \<mu>T\<^sub>1 \<mu>T\<^sub>2 \<Longrightarrow> memT_le \<mu>T\<^sub>2 \<mu>T\<^sub>3 \<Longrightarrow> memT_le \<mu>T\<^sub>1 \<mu>T\<^sub>3"
  apply (cases \<mu>T\<^sub>1;cases \<mu>T\<^sub>2;cases \<mu>T\<^sub>3)
  apply auto
  by (metis less_le_trans)

lemma memT_le_idx_conv:
  "\<lbrakk>memT_le \<mu>T \<mu>T'; i<length (memT.memT \<mu>T); memT.memT \<mu>T' ! i \<noteq> None \<rbrakk> \<Longrightarrow> memT.memT \<mu>T' ! i = memT.memT \<mu>T ! i"
  by (cases \<mu>T; cases \<mu>T'; auto)

lemma memT_le_idx_conv1:
  "\<lbrakk> memT_le \<mu>T \<mu>T'; i<length (memT.memT \<mu>T); memT.memT \<mu>T' ! i = Some T \<rbrakk> \<Longrightarrow> memT.memT \<mu>T ! i = Some T  "
  using memT_le_idx_conv by auto

lemma addr_of_type_memT_le: "\<lbrakk>memT_le \<mu>T \<mu>T'; addr_of_type \<mu>T a T\<rbrakk> \<Longrightarrow> addr_of_type \<mu>T' a T"
  apply (cases \<mu>T; cases \<mu>T'; simp)
  apply (auto simp: addr_of_type_def Let_def split: if_splits option.splits)
  done

lemma of_type_memT_le:
  assumes "memT_le \<mu>T \<mu>T'"
  assumes "of_type \<mu>T T v"
  shows "of_type \<mu>T' T v"
  using assms
  apply (induction T v rule: of_type.induct)
  apply (auto simp: addr_of_type_memT_le list_all2_conv_all_nth)
  done


lemma tyco_block_allocate_aux:
  fixes \<mu>T T
  defines "\<mu>T' \<equiv> MEM_TYPE (memT.memT \<mu>T @ [Some T])"
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "of_type \<mu>T T v"
  shows "memT_le \<mu>T \<mu>T'" "mem_of_type \<mu>T' (MEM (get' mem\<^sub>L \<mu> @ [Some (v,bty)]))"
proof -
  show 1: "memT_le \<mu>T \<mu>T'"
    unfolding \<mu>T'_def by (cases \<mu>T) auto

  have [simp]: "length (memT.memT \<mu>T') = Suc (length (get' mem\<^sub>L \<mu>))"
    using assms(2) unfolding \<mu>T'_def
      by (cases \<mu>T) (auto simp: mem_of_type_def list_all2_lengthD)

  have [simp]: "memT.memT \<mu>T' ! length (get' mem\<^sub>L \<mu>) = Some T"
    using assms(2)
    by (auto simp: \<mu>T'_def nth_append mem_of_type_def list_all2_lengthD)

  have [simp]: "get' mem\<^sub>L \<mu> ! i = None" if "i<length (memT.memT \<mu>T)" "memT.memT \<mu>T' ! i = None" for i
  proof -
    from that have "memT.memT \<mu>T ! i = None" unfolding \<mu>T'_def
      by (cases \<mu>T) (auto simp: nth_append split: if_splits)
    with assms(2) that show ?thesis
      by (auto simp: mem_of_type_def list_all2_conv_all_nth)
  qed

  show "mem_of_type \<mu>T' (MEM (get' mem\<^sub>L \<mu> @ [Some (v,bty)]))"
    using assms(2,3) 1
    unfolding mem_of_type_def
    by (auto
      simp: list_all2_conv_all_nth nth_append less_Suc_eq_le of_type_memT_le rel_option_iff memT_le_idx_conv1
      split: option.splits)

qed

lemma tyco_block_allocate:
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "of_type \<mu>T T v"
  shows "mwp (run (block_allocate bty v) \<mu>) bot no_static_err bot (\<lambda>p \<mu>'.
    \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> the_block p < length (memT.memT \<mu>T') \<and> memT.memT \<mu>T'!the_block p = Some T)"
  using tyco_block_allocate_aux[OF assms]
  by (fastforce
    simp: block_allocate_def run_simps
    split: option.splits
    dest: mem_of_type_lengthD[symmetric])

lemma tyco_block_free_aux1:
  assumes "b < length (\<mu>T)"
  shows "memT_le (MEM_TYPE \<mu>T) (MEM_TYPE (\<mu>T [b := None]))"
  using assms
  by (auto simp: nth_list_update)

lemma tyco_block_free_aux2:
  assumes "the_block b < length (get' mem\<^sub>L \<mu>)"
  assumes "mem_of_type \<mu>T \<mu>"
  shows "mem_of_type (MEM_TYPE (memT.memT \<mu>T [the_block b := None])) (MEM (get' mem\<^sub>L \<mu>[the_block b := None]))"
  using assms
  apply (cases \<mu>; cases \<mu>T)
  apply (auto simp: mem_of_type_def list_all2_conv_all_nth nth_list_update)
  apply (auto simp: rel_option_iff of_type_memT_le[OF tyco_block_free_aux1] split: option.splits)
  done


lemma tyco_block_free:
  assumes "mem_of_type \<mu>T \<mu>"
  shows "mwp (run (block_free bty b) \<mu>) bot no_static_err bot (\<lambda>p \<mu>'.
    \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>')"
  using assms apply (cases \<mu>T)
  using tyco_block_free_aux2[OF _ assms(1)]
  by (auto 0 4
    simp: block_free_def run_simps mem_of_type_lengthD
    intro: tyco_block_free_aux1
    split: option.splits)


definition "tyI_exec_state \<mu>T sT s \<equiv>
    mem_of_type \<mu>T (get' exec_state.memory\<^sub>L s)
  \<and> rel_fun (=) (rel_option (of_type \<mu>T)) sT (get' exec_state.lvars\<^sub>L s)"


abbreviation "fcheck' msg \<equiv> fcheck (shows msg)"
abbreviation "fail' msg \<equiv> fail (shows msg)"

definition "lvty\<^sub>L x \<equiv> lift_lens (''Undef local variable '' +#+ shows (lvar_name.the_name x)) (fun\<^sub>L x \<bullet>\<^sub>L the\<^sub>L)"

lemma [simp]: "elens (lvty\<^sub>L x)"
  by (auto simp: lvty\<^sub>L_def)

fun check_int_type where
  "check_int_type (TINT w) = fcheck' (''i0 type'') (w\<noteq>0)"
| "check_int_type ty = fail (''Expected int type, but got '' +#+ shows_of ty)"

fun tyco_load_opr where
  "tyco_load_opr ty (OP_ICONST _) = doM { check_int_type ty; return ty }"
| "tyco_load_opr ty (OP_LVAR x) = doM { 
    ty' \<leftarrow> use (lvty\<^sub>L x); 
    fcheck (shows_of x o shows '' declared as '' o shows_of ty' o shows '' but used as '' o shows_of ty) (ty=ty'); 
    return ty' }"

lemma tyco_load_opr:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_opr ty x) sT = SUCC T sT'"
  shows "mwp (run (load_opr ty x) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> sT'=sT \<and> T=ty \<and> of_type \<mu>T T v)"
  using assms
  apply (cases x; simp)
  apply (auto simp: run_simps split: option.splits type.splits if_splits)
  subgoal for v
    by (auto simp: tyI_exec_state_def lvty\<^sub>L_def lvar\<^sub>L_def dest: rel_funD[where x=v and y=v])
  subgoal for v e
    by (auto simp: lvar\<^sub>L_def lvty\<^sub>L_def tyI_exec_state_def dest: rel_funD[where x=v and y=v])
  done

lemma tyco_to_int:
  assumes "of_type \<mu>T (TINT w) v"
  shows "mwp (run (to_lint v) s) bot no_static_err bot (\<lambda>i s'. s'=s \<and> width i = w)"
  using assms by (auto simp: to_lint_def run_simps split: val.splits sum.splits)

lemma tyco_to_bool:
  assumes "of_type \<mu>T (TINT 1) v"
  shows "mwp (run (to_bool v) s) bot no_static_err bot (\<lambda>_ s'. s'=s)"
  using assms by (auto simp: to_bool_def to_lint_def run_simps split: val.splits sum.splits)

lemma tyco_to_addr:
  assumes "of_type \<mu>T (TPTR ty) v"
  shows "mwp (run (to_addr v) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> addr_of_type \<mu>T v ty)"
  using assms by (auto simp: to_addr_def run_simps split: val.splits option.splits)


definition "tyco_load_int ty opr \<equiv> doM {
    fcheck (''Expected integer type, but got '' +#+ shows_of ty) (is_TINT ty);
    tyco_load_opr ty opr;
    return ()
  }"

definition "tyco_load_bool ty opr \<equiv> doM {
    fcheck (''Expected i1 type, but got '' +#+ shows_of ty) (ty = TINT 1);
    tyco_load_opr ty opr;
    return ()
  }"

definition "tyco_load_addr ty opr \<equiv> doM {
    fcheck (''Expected pointer type, but got '' +#+ shows_of ty) (is_TPTR ty);
    tyco_load_opr ty opr;
    return ()
  }"



lemma tyco_load_int:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_int ty x) sT = SUCC () sT'"
  shows "mwp (run (load_int ty x) s) bot no_static_err bot (\<lambda>i s'. \<exists>w. s'=s \<and> sT'=sT \<and> ty = TINT w \<and> width i = w)"
  using assms
  apply (cases ty)
  by (auto
    simp: run_simps load_int_def tyco_load_int_def
    intro!: mwp_cons[OF tyco_load_opr] mwp_cons[OF tyco_to_int]
    elim!: mwp_eq_cases
    split: if_splits
    )

lemma tyco_load_bool:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_bool ty x) sT = SUCC () sT'"
  shows "mwp (run (load_bool ty x) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> sT'=sT \<and> ty=TINT 1)"
  using assms
  by (auto
    simp: run_simps load_bool_def tyco_load_bool_def
    intro!: mwp_cons[OF tyco_load_opr] mwp_cons[OF tyco_to_bool]
    elim!: mwp_eq_cases
    split: if_splits
    )

lemma tyco_load_addr:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_addr ty x) sT = SUCC () sT'"
  shows "mwp (run (load_addr ty x) s) bot no_static_err bot
    (\<lambda>v s'. \<exists>ty'. s'=s \<and> sT'=sT \<and> ty=TPTR ty' \<and> addr_of_type \<mu>T v ty')"
  using assms
  apply (cases ty)
  apply (auto
    simp: run_simps load_addr_def tyco_load_addr_def
    intro!: mwp_cons[OF tyco_load_opr] mwp_cons[OF tyco_to_addr]
    elim!: mwp_eq_cases
    split: if_splits
    )
  done

lemma of_type_uninit[simp]: "of_type \<mu>T ty (uninit ty)"
  apply (induction ty rule: uninit.induct)
  apply (auto simp: list_all2_conv_all_nth)
  done

lemma rel_fun_opt_memT_le_mono:
  "\<lbrakk>rel_fun (=) (rel_option (of_type \<mu>T)) sT s; memT_le \<mu>T \<mu>T'\<rbrakk>
       \<Longrightarrow> rel_fun (=) (rel_option (of_type \<mu>T')) sT s"
  apply (rule rel_funI, drule rel_funD, assumption; clarsimp)
  subgoal for x
    by (cases "sT x"; cases "s x"; simp add: of_type_memT_le)
  done

lemma rel_opt_memT_le_mono:
  "\<lbrakk>rel_option (of_type \<mu>T) T v; memT_le \<mu>T \<mu>T'\<rbrakk>
       \<Longrightarrow> rel_option (of_type \<mu>T') T v"
  by (cases "T"; cases "v"; simp add: of_type_memT_le)


lemma tyco_instr_alloca:
  assumes "tyI_exec_state \<mu>T sT s"
  shows "mwp (run (instr_alloca ty n) s) bot no_static_err bot
    (\<lambda>r s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> addr_of_type \<mu>T' r ty)"
  using assms
  apply (auto
    simp: instr_alloca_def run_simps tyI_exec_state_def
    intro!: mwp_cons[OF tyco_block_allocate[where T="TARRAY (nat n) ty"]]
    split: option.splits)
  apply (cases s; simp)
  apply (intro exI conjI, assumption, assumption)
  apply (simp add: rel_fun_opt_memT_le_mono)
  apply (auto simp: addr_of_type_def Let_def split: option.splits)
  done

lemma tyco_instr_malloc:
  assumes "tyI_exec_state \<mu>T sT s"
  shows "mwp (run (instr_malloc ty n) s) bot no_static_err bot
    (\<lambda>r s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> addr_of_type \<mu>T' r ty)"
  using assms
  apply (auto
    simp: instr_malloc_def llb_malloc_def run_simps tyI_exec_state_def
    intro!: mwp_cons[OF tyco_block_allocate[where T="TARRAY (nat n) ty"]]
    split: option.splits)
  apply (cases s; simp)
  apply (intro exI conjI, assumption, assumption)
  apply (simp add: rel_fun_opt_memT_le_mono)
  apply (auto simp: addr_of_type_def Let_def split: option.splits)
  done

lemma tyco_instr_free:
  assumes "tyI_exec_state \<mu>T sT s"
  shows "mwp (run (instr_free x) s) bot no_static_err bot
    (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s')"
  using assms
  apply (auto
    simp: instr_free_def llb_free_def run_simps tyI_exec_state_def
    intro!: mwp_cons[OF tyco_block_free]
    split: option.splits addr.splits list.splits va_item.splits nat.splits)
  apply (cases s; simp)
  apply (intro exI conjI, assumption, assumption)
  apply (simp add: rel_fun_opt_memT_le_mono)
  done


  definition "tyco_instr_arith2 ty op1 op2 = doM {
    tyco_load_int ty op1;
    tyco_load_int ty op2;
    return (Some ty)
  }"
  
  definition "tyco_instr_arith_cmp ty op1 op2 = doM {
    tyco_load_int ty op1;
    tyco_load_int ty op2;
    return (Some (TINT 1))
  }"                                  

  definition "tyco_instr_trunc ty op1 ty' = doM {
    tyco_load_int ty op1;
    case (ty,ty') of
      (TINT w1, TINT w2) \<Rightarrow> doM {
        fcheck' ''i0 type'' (w2>0);
        fcheck (''Trunc must go to smaller width, but this one goes from '' +#+ shows_of ty o shows '' to '' o shows_of ty') (w1>w2);
        return (Some ty')
      }
    | _ \<Rightarrow> fail' ''trunc type error''
  }"

  definition "tyco_instr_ext ty op1 ty' = doM {
    tyco_load_int ty op1;
    case (ty,ty') of
      (TINT w1, TINT w2) \<Rightarrow> doM {
        fcheck' ''Ext must go to greater width'' (w1<w2);
        return (Some ty')
      }
    | _ \<Rightarrow> fail' ''ext type error''
  }"

  primrec tyco_exec_basic_instr_aux :: "_ \<Rightarrow> (_,unit,_,_) M" where
    "tyco_exec_basic_instr_aux (ADD ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (SUB ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (MUL ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (UDIV ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (UREM ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (SDIV ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (SREM ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (SHL ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (LSHR ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (ASHR ty op1 op2) = tyco_instr_arith2 ty op1 op2"

  | "tyco_exec_basic_instr_aux (TRUNC_TO ty op1 ty') = tyco_instr_trunc ty op1 ty'"
  | "tyco_exec_basic_instr_aux (ZEXT_TO ty op1 ty') = tyco_instr_ext ty op1 ty'"
  | "tyco_exec_basic_instr_aux (SEXT_TO ty op1 ty') = tyco_instr_ext ty op1 ty'"
     
  | "tyco_exec_basic_instr_aux (ICMP code ty op1 op2) = tyco_instr_arith_cmp ty op1 op2"
     
  | "tyco_exec_basic_instr_aux (basic_instr_aux.AND ty op1 op2) = tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (basic_instr_aux.OR ty op1 op2) =  tyco_instr_arith2 ty op1 op2"
  | "tyco_exec_basic_instr_aux (basic_instr_aux.XOR ty op1 op2) = tyco_instr_arith2 ty op1 op2"

  | "tyco_exec_basic_instr_aux (ALLOCA ty tyi opr) = doM {
      tyco_load_int tyi opr;
      return (Some (TPTR ty))
    }"
  | "tyco_exec_basic_instr_aux (MALLOC ty tyi opr) = doM {
      tyco_load_int tyi opr;
      return (Some (TPTR ty))
    }"
  | "tyco_exec_basic_instr_aux (FREE ty opr) = doM {
      tyco_load_addr ty opr;
      return None
    }"
  | "tyco_exec_basic_instr_aux (LOAD ty typ opr) = doM {
      tyco_load_addr (typ) opr;
      fcheck' ''LOAD: Type mismatch'' (typ = TPTR ty);
      return (Some ty)
    }"
  | "tyco_exec_basic_instr_aux (STORE tyv oprv typ oprp) = doM {
      tyco_load_opr tyv oprv;
      tyco_load_addr typ oprp;
      fcheck' ''STORE: Incompatible types'' (typ = TPTR tyv);
      return None
    }"
  | "tyco_exec_basic_instr_aux (INSERT_A_VALUE bty bopr ety eopr idx) = doM {
      tyco_load_opr bty bopr;
      tyco_load_opr ety eopr;
      fcheck' ''insert_a_value type mismatch'' (case bty of TARRAY _ ety' \<Rightarrow> ety=ety' | _ \<Rightarrow> False);
      return (Some bty)
    }"
  | "tyco_exec_basic_instr_aux (INSERT_S_VALUE bty bopr ety eopr idx) = doM {
      tyco_load_opr bty bopr;
      tyco_load_opr ety eopr;
      fcheck' ''insert_s_value type mismatch'' (case bty of
         TSTRUCT ftys \<Rightarrow> idx<length ftys \<and> ftys!idx = ety
       | _ \<Rightarrow> False);
      return (Some bty)
    }"
  | "tyco_exec_basic_instr_aux (EXTRACT_A_VALUE bty bopr idx) = doM {
      tyco_load_opr bty bopr;
      case bty of
        TARRAY _ ty \<Rightarrow> return (Some ty)
      | _ \<Rightarrow> fail' ''extract_a_value type mismatch''
    }"
  | "tyco_exec_basic_instr_aux (EXTRACT_S_VALUE bty bopr idx) = doM {
      tyco_load_opr bty bopr;
      case bty of
        TSTRUCT ftys \<Rightarrow> doM {
          fcheck' ''Field index out of range'' (idx < length ftys);
          return (Some (ftys!idx))
        }
      | _ \<Rightarrow> fail' ''extract_s_value type mismatch''
    }"
  | "tyco_exec_basic_instr_aux (OFS_PTR bty bopr ity iopr) = doM {
      tyco_load_addr (TPTR bty) bopr;
      tyco_load_int ity iopr;
      return (Some (TPTR bty))
    }"
  | "tyco_exec_basic_instr_aux (INDEX_A_PTR bty bopr ity iopr) = doM {
      tyco_load_addr (TPTR bty) bopr;
      tyco_load_int ity iopr;
      case bty of
        TARRAY _ ty \<Rightarrow> return (Some (TPTR ty))
      | _ \<Rightarrow> fail' ''index_a_ptr type mismatch''
    }"
  | "tyco_exec_basic_instr_aux (INDEX_S_PTR bty bopr idx) = doM {
      tyco_load_addr (TPTR bty) bopr;
      case bty of
        TSTRUCT ftys \<Rightarrow> doM {
          fcheck' ''index_s_ptr field index out of range'' (idx < length ftys);
          return (Some (TPTR (ftys!idx)))
        }
      | _ \<Rightarrow> fail' ''index_s_ptr type mismatch''
    }"
                              

  definition "param_args_match \<mu>T params args \<equiv> list_all2 (of_type \<mu>T) (map fst params) args"

  primrec tyco_exec_nt_instr_aux :: "_ \<Rightarrow> _ \<Rightarrow> (_,unit,_,_) M" where
    "tyco_exec_nt_instr_aux \<pi> (BASIC i) = tyco_exec_basic_instr_aux i"
  | "tyco_exec_nt_instr_aux \<pi> (CALL ty name args) = doM {
      proc \<leftarrow> lookup (''Undefined procedure: '' +#+ shows_of name) (proc_map \<pi>) name;
      mmap (uncurry tyco_load_opr) args;
      fcheck' ''Argument type mismatch'' (map fst (procedure.params proc) = map fst args);
      return (procedure.rtype proc)
    }"


lemma tyco_instr_load:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "addr_of_type \<mu>T addr T"
  shows "mwp (run (instr_load addr) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> of_type \<mu>T T v)"
  using assms
  by (auto
    simp: run_simps instr_load_def llb_load_def Let_def tyI_exec_state_def
    split: option.splits if_splits
    intro!: tyco_use_lens_of_addr[THEN mwp_cons])

named_theorems_rev tyco_rules

method tyco_step = (
    (rule tyco_rules[THEN mwp_cons]; assumption?; clarsimp?)
  | (auto simp: run_simps elim!: mwp_eq_cases split: option.splits if_splits)
)

method tyco = use nothing in \<open>insert method_facts, tyco_step+\<close>

lemmas [tyco_rules] = tyco_load_int tyco_load_bool tyco_instr_alloca
  tyco_instr_malloc tyco_instr_free tyco_load_addr tyco_instr_load tyco_load_opr
  tyco_use_lens_of_addr tyco_put_lens_of_addr
  tyco_block_free


lemma same_type_imp_same_struct: "of_type \<mu>T T a \<Longrightarrow> of_type \<mu>T T b \<Longrightarrow> same_struct a b"
  apply (induction T a arbitrary: b rule: of_type.induct)
  apply (auto simp: list_all2_conv_all_nth)
  apply (case_tac [!] b)
  apply (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)+
  done


lemma tyco_instr_store[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "addr_of_type \<mu>T addr T"
  assumes "of_type \<mu>T T v"
  shows "mwp (run (instr_store v addr) s) bot no_static_err bot (\<lambda>_ s'. tyI_exec_state \<mu>T sT s')"
  using assms
  unfolding instr_store_def llb_store_def Let_def tyI_exec_state_def
  apply (cases s)
  apply clarsimp
  apply tyco
  apply (simp add: same_type_imp_same_struct)
  apply tyco
  done

(*lemma [simp]:
  "pre_get addr.vaddr\<^sub>L x"
  "get' addr.vaddr\<^sub>L (ADDR blk va) = va"
  "put' addr.vaddr\<^sub>L va' (ADDR blk va) = ADDR blk va'"
  by (auto simp: addr.vaddr\<^sub>L_def split: addr.splits)

lemma [simp]:
  "pre_get va_item.aidx\<^sub>L va = is_VA_ARRAY_IDX va"
  "get' va_item.aidx\<^sub>L (VA_ARRAY_IDX idx) = idx"
  "put' va_item.aidx\<^sub>L idx' (VA_ARRAY_IDX idx) = VA_ARRAY_IDX idx'"
  by (auto split: va_item.split)
*)


lemma vaddr_of_type_change_last_array_idx: "vaddr_of_type bT (vas @ [VA_ARRAY_IDX i]) T
  \<Longrightarrow> vaddr_of_type bT (vas @ [VA_ARRAY_IDX i']) T"
  apply (induction bT vas T rule: vaddr_of_type.induct)
  apply auto
  apply (case_tac bT; case_tac T; auto)
  done

lemma vaddr_of_type_append_aidx:
  assumes "vaddr_of_type bT vas (TARRAY n T)"
  shows "vaddr_of_type bT (vas @ [VA_ARRAY_IDX idx]) T"
  using assms
  apply (induction bT vas T rule: vaddr_of_type.induct)
  apply auto
  done

lemma addr_of_type_append_aidx:
  assumes "addr_of_type \<mu>T addr (TARRAY n T)"
  shows "addr_of_type \<mu>T (put' addr.vaddr\<^sub>L (get' addr.vaddr\<^sub>L addr @ [VA_ARRAY_IDX idx]) addr) T"
  using assms
  apply (cases addr)
  unfolding addr_of_type_def Let_def
  apply (auto simp: vaddr_of_type_append_aidx split: if_splits option.splits)
  done

lemma vaddr_of_type_append_fidx:
  assumes "vaddr_of_type bT vas (TSTRUCT Ts)"
  assumes "idx < length Ts"
  shows "vaddr_of_type bT (vas @ [VA_FIELD_IDX idx]) (Ts!idx)"
  using assms
  apply (induction bT vas T\<equiv>"Ts!idx" rule: vaddr_of_type.induct)
  apply auto
  done

lemma addr_of_type_append_fidx:
  assumes "addr_of_type \<mu>T addr (TSTRUCT Ts)"
  assumes "idx < length Ts"
  shows "addr_of_type \<mu>T (put' addr.vaddr\<^sub>L (get' addr.vaddr\<^sub>L addr @ [VA_FIELD_IDX idx]) addr) (Ts!idx)"
  using assms
  apply (cases addr)
  unfolding addr_of_type_def Let_def
  apply (auto simp: vaddr_of_type_append_fidx split: if_splits option.splits)
  done

lemma tyco_instr_ofs_addr[tyco_rules]:
  assumes "addr_of_type \<mu>T a ty"
  shows "mwp (run (llb_ofs_addr a i) s) bot no_static_err bot (\<lambda>a' s'. s'=s \<and> addr_of_type \<mu>T a' ty)"
  using assms
  apply (cases a)
  subgoal for blk va
    apply (cases va rule: rev_cases)
    subgoal by (auto simp: run_simps llb_ofs_addr_def split: option.splits)
    subgoal for vas vai
      apply (cases vai)
      by (auto
        simp: run_simps llb_ofs_addr_def addr_of_type_def Let_def
        elim!: vaddr_of_type_change_last_array_idx
        split: option.splits)
    done
  done

thm memT_le_refl

lemma tyco_instr_arith2[tyco_rules]: 
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_instr_arith2 ty a b) sT = SUCC T sT'"
  assumes "\<And>x y. \<not>ovf x y \<Longrightarrow> width x = width y \<Longrightarrow> width (f x y) = width y"
  shows "mwp (run (instr_arith2 ovf f ty a b) s) bot no_static_err bot 
    (\<lambda>vv s'. \<exists>v. vv=Some v \<and> s'=s \<and> T=Some ty \<and> sT'=sT \<and> of_type \<mu>T ty v)"
  using assms unfolding tyco_instr_arith2_def instr_arith2_def
  by tyco

lemma tyco_instr_arith_cmp[tyco_rules]: 
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_instr_arith_cmp ty a b) sT = SUCC T sT'"
  shows "mwp (run (instr_arith_cmp f ty a b) s) bot no_static_err bot 
    (\<lambda>vv s'. \<exists>v. vv=Some v \<and> s'=s \<and> T=Some (TINT 1) \<and> sT'=sT \<and> of_type \<mu>T (TINT 1) v)"
  using assms unfolding tyco_instr_arith_cmp_def instr_arith_cmp_def
  by tyco


lemma tyco_instr_trunc[tyco_rules]: 
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_instr_trunc ty a ty') sT = SUCC T sT'"
  shows "mwp (run (instr_trunc ty a ty') s) bot no_static_err bot 
    (\<lambda>vv s'. \<exists>v. vv=Some v \<and> s'=s \<and> T=Some ty' \<and> sT'=sT \<and> of_type \<mu>T ty' v)"
  using assms unfolding tyco_instr_trunc_def instr_trunc_def
  supply type.splits[split]
  by tyco

lemma tyco_instr_ext[tyco_rules]: 
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_instr_ext ty a ty') sT = SUCC T sT'"
  assumes "f\<in>{zext,sext}"
  shows "mwp (run (instr_ext f ty a ty') s) bot no_static_err bot 
    (\<lambda>vv s'. \<exists>v. vv=Some v \<and> s'=s \<and> T=Some ty' \<and> sT'=sT \<and> of_type \<mu>T ty' v)"
  using assms unfolding tyco_instr_ext_def instr_ext_def
  supply type.splits[split]
  by tyco


lemma tyco_exec_basic_instr_aux[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_exec_basic_instr_aux instr) sT = SUCC T sT'"
  shows "mwp (run (exec_basic_instr_aux instr) s) bot no_static_err bot
    (\<lambda>v s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> rel_option (of_type \<mu>T') T v)"
  using assms
  apply (cases instr; simp)
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal unfolding bitSHL'_def by tyco
  subgoal unfolding bitASHR'_def by tyco
  subgoal unfolding bitLSHR'_def by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal
    supply [split] = type.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
    unfolding ll_insert_a_value'_def put_same_struct_def
    by tyco
  subgoal
    supply [split] = type.splits val.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
      and [simp] = list_all2_conv_all_nth
    unfolding ll_insert_s_value'_def put_same_struct_def
    by tyco
  subgoal
    supply [split] = type.splits val.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
      and [simp] = list_all2_conv_all_nth
    unfolding ll_extract_a_value'_def put_same_struct_def
    by tyco
  subgoal
    supply [split] = type.splits val.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
      and [simp] = list_all2_conv_all_nth
    unfolding ll_extract_s_value'_def put_same_struct_def
    by tyco
  subgoal by tyco
  subgoal
    supply [split] = type.splits
    supply [simp] = addr_of_type_append_aidx
    unfolding llb_idx_array_def to_idx_def
    by tyco
  subgoal
    supply [split] = type.splits
    supply [simp] = addr_of_type_append_fidx
    unfolding llb_idx_field_def to_idx_def
    apply tyco
    done
  done

lemma tyco_mmap_load_opr[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (mmap (uncurry tyco_load_opr) ops) sT = (SUCC uus sT' :: (_,'e,_,_) mres)"
  shows "mwp (run (mmap (uncurry load_opr) ops) s) bot no_static_err bot
    (\<lambda>vs s'. sT'=sT \<and> s'=s \<and> list_all2 (of_type \<mu>T) (map fst ops) vs)"
  using assms(2)
proof (induction ops arbitrary: uus)
  case Nil
  then show ?case by tyco
next
  case (Cons ty_opr ops)

  obtain ty opr where [simp]: "ty_opr=(ty,opr)" by (cases ty_opr)

  from Cons.prems obtain T sTh where
        1: "run (tyco_load_opr ty opr) sT = (SUCC T sTh :: (_,'e,_,_) mres)"
    and 2: "run (mmap (uncurry tyco_load_opr) ops) sTh = (SUCC (tl uus) sT' :: (_,'e,_,_) mres)  "
    by (auto simp: run_simps elim!: mwp_eq_cases)

  note [tyco_rules] = tyco_load_opr[OF assms(1) 1] Cons.IH[simplified]
  show ?case using 2 by tyco
qed

lemma run_noexcept[run_simps]:
  "run (noexcept m) s = mwp (run m s) NTERM FAIL (\<lambda>_ _. FAIL (STATIC_ERROR ''noexcept'')) SUCC"
  unfolding noexcept_def
  by (simp add: run_simps cong del: mwp_cong)


definition tyco_define_lvar :: "type \<Rightarrow> lvar_name \<Rightarrow> (_,unit,_,_) M" where
  "tyco_define_lvar ty name \<equiv> (doM {
    l\<leftarrow>get;
    fcheck (''lvar redefined: '' +#+ shows_of name) (name \<notin> dom l);
    let l = l(name\<mapsto>ty);
    set l
  })"

lemma tyco_define_lvar[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "of_type \<mu>T ty v"
  assumes "run (tyco_define_lvar ty name) sT = SUCC () sT'"
  shows "mwp (run (define_lvar name v) s) bot no_static_err bot (\<lambda>_ s'.
    tyI_exec_state \<mu>T sT' s')"
  using assms
  unfolding define_lvar_def tyco_define_lvar_def tyI_exec_state_def
  apply tyco
    apply (metis (full_types) option.rel_distinct(1) rel_funD)
  using rel_funD by fastforce


primrec tyco_exec_nt_instr_noe where
  "tyco_exec_nt_instr_noe \<pi> (NT_INSTR resname i) = doM {
    rT \<leftarrow> tyco_exec_nt_instr_aux \<pi> i;
    case resname of
      None \<Rightarrow> return ()
    | Some resvar \<Rightarrow> doM {
      rT \<leftarrow> mget (lift_lens (shows ''Binding void result'') the\<^sub>L) rT;
      tyco_define_lvar rT resvar
    }
  }"

definition "tyco_exec_nt_instr \<pi> i \<equiv> mfail (\<lambda>e. shows_of i o shows '': '' o e) (tyco_exec_nt_instr_noe \<pi> i)"

context
  fixes proc :: procedure
begin

  definition "check_defined_label label \<equiv> 
    fcheck (''Undefined label: '' +#+ shows_of label) (label \<in> fst`list.set (procedure.blocks proc))"

  primrec tyco_exec_t_instr_noe where
    "tyco_exec_t_instr_noe (RETURN_VOID) =
      fcheck' ''Non-void procedure returns void'' (procedure.rtype proc = None)"
  | "tyco_exec_t_instr_noe (RETURN ty opr) = doM {
      tyco_load_opr ty opr;
      fcheck (''Procedure return type mismatch: Expected '' +#+ shows_of (procedure.rtype proc) o shows '' but got '' o shows_of ty) (procedure.rtype proc = Some ty)
    }"
  | "tyco_exec_t_instr_noe (BR label) = check_defined_label label"
  | "tyco_exec_t_instr_noe (CBR ty opr lt lf) = doM {
      tyco_load_bool ty opr;
      check_defined_label lt;
      check_defined_label lf
  }"

  definition "tyco_exec_t_instr i \<equiv> mfail (\<lambda>e. shows_of i o shows '': '' o e) (tyco_exec_t_instr_noe i)"


  lemma tyco_check_defined_label_iff[simp]:
    "run (check_defined_label l) sT = SUCC () sT' \<longleftrightarrow> (l\<in>fst`list.set (procedure.blocks proc) \<and> sT' = sT)"  
    unfolding check_defined_label_def
    by tyco
    

  lemma tyco_exec_t_instr[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_t_instr instr) sT = SUCC uu sT'"
    shows "mwp (run (exec_t_instr instr) s) bot no_static_err
      (\<lambda>rv s'. s'=s \<and> sT'=sT \<and> rel_option (of_type \<mu>T) (procedure.rtype proc) rv)
      (\<lambda>l s'. s'=s \<and> sT'=sT \<and> l\<in>fst`list.set (procedure.blocks proc))"
    using assms
    unfolding tyco_exec_t_instr_def
    apply (cases instr; simp)
    by tyco

  definition "tyco_exec_block \<pi> \<equiv> \<lambda>BBLOCK ntis ti\<Rightarrow> doM {
    \<comment> \<open>Execute nonterminal instructions\<close>
    mfold' (tyco_exec_nt_instr \<pi>) ntis;
    \<comment> \<open>Execute terminal instruction\<close>
    tyco_exec_t_instr ti
  }"


  definition "tyco_exec_block_reset \<pi> block \<equiv> doM {
    saved_lts \<leftarrow> get;
    mmblock get (\<lambda>_. set saved_lts) (tyco_exec_block \<pi> block)
  }"


end

definition "tyco_exec_proc \<pi> proc \<equiv>
  case proc of PROC params prologue blocks rtype \<Rightarrow> doM {
    mblock (\<lambda>_. Map.empty) (\<lambda>_. ()) (doM {

      \<comment> \<open>Define Parameters\<close>
      mfold' (uncurry tyco_define_lvar) params;

      \<comment> \<open>Execute Prologue\<close>
      tyco_exec_block proc \<pi> prologue;

      \<comment> \<open>Execute Blocks\<close>
      mmap (tyco_exec_block_reset proc \<pi>) (map snd blocks);

      return ()
    })
}"


(*
definition "tyco_exec_proc \<pi> proc args \<equiv>
  case proc of PROC params prologue blocks rtype \<Rightarrow> doM {
    fcheck (''|arg| != |param|'') (length params = length args);
    fcheck (''arg-types !~ param-types'') (args = map fst params);
    mblock (\<lambda>_. Map.empty) (\<lambda>_. ()) (doM {

      (* Define Parameters*)
      mfold' (uncurry tyco_define_lvar) params;

      (* Execute Prologue *)
      tyco_exec_block proc \<pi> prologue;

      (* Execute Blocks *)
      mmap (tyco_exec_block_reset proc \<pi>) (map snd blocks);

      return ()
    })
}"
*)

locale tyco_exec_proc_name_IH =
  fixes exec_proc_name :: "proc_name \<times> val list \<Rightarrow> (val option, unit, memory, err) M"
    and \<pi> :: program
  assumes tyco_exec_proc_name[tyco_rules]: "\<lbrakk>
    proc_map \<pi> pname = Some proc;
    param_args_match \<mu>T (procedure.params proc) args;
    mem_of_type \<mu>T \<mu>
  \<rbrakk> \<Longrightarrow> mwp (run (exec_proc_name (pname,args)) \<mu>) top no_static_err bot
    (\<lambda>r \<mu>'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) r)"
begin

  lemma tyco_exec_nt_instr_aux[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_nt_instr_aux \<pi> instr) sT = SUCC T sT'"
    shows "mwp (run (exec_nt_instr_aux exec_proc_name instr) s) top no_static_err bot
      (\<lambda>v s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> rel_option (of_type \<mu>T') T v)"
    using assms
    apply (cases instr; simp)
    subgoal by tyco
    subgoal
      supply [simp] = tyI_exec_state_def param_args_match_def
      supply [intro] = rel_fun_opt_memT_le_mono
      by tyco
    done

  lemma tyco_exec_nt_instr[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_nt_instr \<pi> instr) sT = SUCC T sT'"
    shows "mwp (run (exec_nt_instr exec_proc_name instr) s) top no_static_err bot
      (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s')"
    using assms
    unfolding tyco_exec_nt_instr_def
    apply (cases instr; simp)
    supply [simp] = option.rel_sel
    by tyco

  lemma tyco_exec_nt_instrs[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (mfold' (tyco_exec_nt_instr \<pi>) instrs) sT = SUCC T sT'"
    shows "mwp (run (mfold' (exec_nt_instr exec_proc_name) instrs) s) top no_static_err bot
        (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s')"
    using assms
  proof (induction instrs arbitrary: \<mu>T sT s)
    case Nil
    then show ?case by tyco
  next
    case (Cons a instrs)

    from Cons.prems show ?case
      supply [dest] = memT_le_trans
      apply tyco
      (* Have to apply this rule explicitly, as assumption must be applied to
        first subgoal first, not to last subgoal as in default ;assumption?
      *)
      apply (rule Cons.IH[THEN mwp_cons], assumption)
      apply tyco
      done

  qed


  lemma tyco_exec_block[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_block proc \<pi> blk) sT = SUCC uu sT'"
    shows "mwp (run (exec_block exec_proc_name blk) s) top no_static_err
      (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) rv)
      (\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> l\<in>fst`list.set (procedure.blocks proc))"
  proof -
    show ?thesis
      using assms unfolding exec_block_def tyco_exec_block_def
      apply (cases blk; simp)
      by tyco
  qed

  lemma tyco_exec_block_reset[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT'"
    shows "mwp (run (exec_block_reset exec_proc_name blk) s) top no_static_err
      (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> get' exec_state.lvars\<^sub>L s' = get' exec_state.lvars\<^sub>L s \<and> sT'=sT \<and> tyI_exec_state \<mu>T' sT s' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) rv)
      (\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> get' exec_state.lvars\<^sub>L s' = get' exec_state.lvars\<^sub>L s \<and> sT'=sT \<and> tyI_exec_state \<mu>T' sT s' \<and> l\<in>fst`list.set (procedure.blocks proc))"
    using assms
    unfolding tyco_exec_block_reset_def exec_block_reset_def
    apply tyco
    unfolding tyI_exec_state_def
    apply (auto intro: rel_fun_opt_memT_le_mono)
    done

  term tyco_exec_proc
  term exec_proc

  lemma tyco_mfold_define_lvar[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "map fst nvs = map snd tns"
    assumes "list_all2 (of_type \<mu>T) (map fst tns) (map snd nvs)"
    assumes "run (mfold' (uncurry tyco_define_lvar) tns) sT = SUCC () sT'"
    shows "mwp (run (mfold' (uncurry define_lvar) nvs) s) bot no_static_err bot (\<lambda>_ s'.
      tyI_exec_state \<mu>T sT' s'
    )"
    using assms
  proof (induction nvs arbitrary: tns sT s)
    case Nil
    then show ?case by tyco
  next
    case (Cons a nvs)

    note Cons.IH[tyco_rules]

    from Cons.prems show ?case
      by (cases a; clarsimp) tyco

  qed

  lemma tyI_exec_state_fresh[simp]:
    "tyI_exec_state \<mu>T Map.empty (mk_fresh_exec_state \<mu>) = mem_of_type \<mu>T \<mu>"
    by (auto simp: tyI_exec_state_def mk_fresh_exec_state_def)

  (* TODO: Move *)
  lemma tyI_exec_state_simp[simp]:
    "tyI_exec_state \<mu>T sT (EXEC_STATE lvs lbs \<mu>) \<longleftrightarrow> mem_of_type \<mu>T \<mu> \<and> rel_fun (=) (rel_option (of_type \<mu>T)) sT lvs"
    by (simp add: tyI_exec_state_def)

  lemma tyco_mfold_free_alloca_blocks[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    shows "mwp (run (mfold' (\<lambda>x. zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free bty x)) bs) s)
      bot no_static_err bot (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and>  tyI_exec_state \<mu>T' sT s')"
    using assms
  proof (induction bs arbitrary: s \<mu>T)
    case Nil
    then show ?case by tyco
  next
    case (Cons a bs)
    note Cons.IH

    from Cons.prems show ?case
      apply (cases s; simp add: )
      apply tyco
      subgoal for x1 x2 x3 sh \<mu>Th
        apply (rule Cons.IH[of \<mu>Th, THEN mwp_cons])
        by (auto simp: rel_fun_opt_memT_le_mono dest: memT_le_trans)
      done
  qed

  lemma exec_state_mem_of_typeI: "tyI_exec_state \<mu>T sT s \<Longrightarrow> mem_of_type \<mu>T (get' exec_state.memory\<^sub>L s)"
    unfolding tyI_exec_state_def by simp


  lemma tyco_exec_blocks_aux:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "l\<in>L"
    assumes IH: "\<And>l \<mu>Th sh. \<lbrakk> memT_le \<mu>T \<mu>Th; tyI_exec_state \<mu>Th sT sh; l\<in>L\<rbrakk> \<Longrightarrow>
      mwp (run (f l) sh) top no_static_err
        (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>Th \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> rel_option (of_type \<mu>T') rT rv)
        (\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>Th \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> l\<in>L)
    "
    shows "mwp (run (mwhile (\<lambda>_. return True) f l) s)
      top no_static_err (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and>  rel_option (of_type \<mu>T') rT rv) bot"
    apply (rule mwhile_invar_rule[OF refl,
      where I="\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> l\<in>L"])
    subgoal by simp
    subgoal using assms by auto
    subgoal
      apply tyco
      apply (rule IH[THEN mwp_cons])
      apply (assumption | simp)+
      apply (auto dest: memT_le_trans)
      done
    done


  lemma tyco_exec_block_reset_pres_sT_aux: "run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT' \<Longrightarrow> sT'=sT"
    unfolding tyco_exec_block_reset_def
    by (auto simp: run_simps elim!: mwp_eq_cases)

  lemma tyco_exec_block_reset_pres_sT[simp]:
    "NO_MATCH sT' sT \<Longrightarrow> run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT' \<longleftrightarrow>
    run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT \<and> sT'=sT"
    using tyco_exec_block_reset_pres_sT_aux by blast

  lemma mmap_tyco_exec_block_reset_pres_sT_aux:
    assumes "run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) ss'"
    shows "ss' = s"
    using assms
    apply (induction blks arbitrary: s uul)
    by (auto simp: run_simps elim!: mwp_eq_cases)

  lemma mmap_tyco_exec_block_reset_pres_sT[simp]:
    "NO_MATCH s' s \<Longrightarrow> run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) s'
      \<longleftrightarrow> run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) s \<and> s'=s"
    using mmap_tyco_exec_block_reset_pres_sT_aux[of proc blks s uul s'] by blast

  lemma run_tyco_mmapI:
    assumes "run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) ss'"
    assumes "blk\<in>List.set blks"
    shows "run (tyco_exec_block_reset proc \<pi> blk) s = SUCC () s"
    using assms
    by (auto simp: in_set_conv_decomp run_simps elim!: mwp_eq_cases)


(*
  lemma tyco_exec_proc[tyco_rules]:
    assumes "mem_of_type \<mu>T \<mu>"
    assumes "list_all2 (of_type \<mu>T) argTs args"
    assumes "run (tyco_exec_proc \<pi> proc argTs) () = SUCC () ()"
    shows "mwp (run (exec_proc exec_proc_name proc args) \<mu>) top no_static_err bot (\<lambda>_ \<mu>'.
      \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>'
    )"
  using assms
  unfolding tyco_exec_proc_def exec_proc_def
  (* TODO: Clean up this mess! *)
  apply (cases proc; clarsimp)
  supply [simp] = list_all2_lengthD[of _ argTs args, symmetric] exec_state_mem_of_typeI
  supply [dest] = memT_le_trans
  apply tyco
  apply (rule tyco_exec_blocks_aux[where L="fst`List.set (procedure.blocks proc)", THEN mwp_cons])
  apply (assumption)
  supply [simp] = weak_map_of_SomeI
  supply [elim!] = run_tyco_mmapI
  apply tyco
  apply (erule run_tyco_mmapI)
  using map_of_SomeD apply fastforce
  apply tyco
  apply (intro exI exec_state_mem_of_typeI conjI; assumption?)
  apply auto
  done
*)


  lemma tyco_exec_proc[tyco_rules]:
    assumes "mem_of_type \<mu>T \<mu>"
    assumes "list_all2 (of_type \<mu>T) (map fst (procedure.params proc)) args"
    assumes "run (tyco_exec_proc \<pi> proc) () = SUCC () ()"
    shows "mwp (run (exec_proc exec_proc_name proc args) \<mu>) top no_static_err bot (\<lambda>rv \<mu>'.
      \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) rv
    )"
  using assms
  unfolding tyco_exec_proc_def exec_proc_def
  (* TODO: Clean up this mess! *)
  apply (cases proc; clarsimp)
  supply [simp] = exec_state_mem_of_typeI rel_opt_memT_le_mono
  supply [dest] = memT_le_trans
  apply (frule list_all2_lengthD; simp)
  apply tyco
  apply (rule tyco_exec_blocks_aux[where L="fst`List.set (procedure.blocks proc)", THEN mwp_cons])
  apply (assumption)
  supply [simp] = weak_map_of_SomeI
  supply [elim!] = run_tyco_mmapI
  apply tyco
  apply (erule run_tyco_mmapI)
  using map_of_SomeD apply fastforce
  apply tyco
  apply (intro exI exec_state_mem_of_typeI conjI)
  prefer 2
  apply assumption
  apply auto
  done



end


fun distinct_w :: "'a list \<Rightarrow> 'a option" where
  "distinct_w [] = None"
| "distinct_w (x#xs) = (if x\<in>list.set xs then Some x else distinct_w xs)"

lemma distinct_w_none[simp]: "distinct_w xs = None \<longleftrightarrow> distinct xs"
  by (induction xs) auto

lemma distinct_w_some_imp_nd[simp]: "distinct_w xs = Some x \<Longrightarrow> \<not>distinct xs"
  by (induction xs) auto

lemma distinct_w_Some: "distinct_w xs = Some x \<Longrightarrow> count (mset xs) x \<ge> 2"
  apply (induction xs arbitrary: x) 
  apply (auto split: if_splits) 
  by (metis count_mset_0_iff not_numeral_le_zero)

definition "check_distinct pr xs \<equiv> case distinct_w xs of None \<Rightarrow> return () | Some x \<Rightarrow> fail (pr x)"

lemma check_distinct_iff[simp]: "run (check_distinct pr xs) s = SUCC () s' \<longleftrightarrow> (s'=s \<and> distinct xs)"
  unfolding check_distinct_def by tyco

definition "tyco_program \<pi> \<equiv> doM {
  check_distinct shows_of (map fst (program.procedures \<pi>));
  mmap (tyco_exec_proc \<pi> o snd) (program.procedures \<pi>);
  return ()
}"

lemma tyco_exec_proc_name[tyco_rules]:
  assumes "(run (exec_proc_name \<pi> (pname,args)) \<mu>) = r"
  assumes "proc_map \<pi> pname = Some proc"
  assumes "param_args_match \<mu>T (procedure.params proc) args"
  assumes "mem_of_type \<mu>T \<mu>"
  assumes TYCO_PROG: "run (tyco_program \<pi>) () = SUCC () ()"
  shows "mwp r top no_static_err bot
    (\<lambda>r \<mu>'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) r)"
  using assms(1-4)
proof (induction "(pname,args)" \<mu> r arbitrary: pname proc args \<mu>T rule: exec_proc_name_partial)
  case (nterm s)
  then show ?case by tyco
next
  case (step exec_proc_name s r)

  from step.hyps(1)[OF refl]
  interpret tyco_exec_proc_name_IH exec_proc_name \<pi> by unfold_locales


  from step.prems have "(pname,proc) \<in> List.set (program.procedures \<pi>)"
    by (auto simp: proc_map_def map_of_SomeD)
  with TYCO_PROG have "run (tyco_exec_proc \<pi> proc) () = SUCC () ()"
    unfolding tyco_program_def
    supply [dest!] = run_mmap_unit_state_elemD
    by tyco

  with step.hyps(2) step.prems show ?case
    unfolding param_args_match_def
    by tyco

qed

lemma mem_of_type_init[simp]: "mem_of_type (MEM_TYPE []) (MEM [])"
  by (auto simp: mem_of_type_def)



export_code tyco_program in SML

value "run (mfail (\<lambda>s. s '''') (tyco_program test)) ()"


typ "32 word"

end
