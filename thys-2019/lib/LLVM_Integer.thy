section \<open>LLVM like Integer Types with Flexible Bit-Width\<close>
theory LLVM_Integer
imports "HOL-Word.Word" Bits_Natural "Word_Lib.Word_Lemmas"
begin

(* TODO: Fix in Word.thy! 
  Introducing proper infix-syntax for signed comparisons. So, also (<s) and (<=s) get available.
*)
no_notation word_sle ("(_/ <=s _)" [50, 51] 50)
no_notation word_sless  ("(_/ <s _)" [50, 51] 50)
notation word_sle (infix "<=s" 50)
notation word_sless (infix "<s" 50)


(* Try to remove some useless stuff that Word_Lemmas imported via Complex_Main. *)

declare [[coercion_enabled = false]]

subsection \<open>Additional Lemmas\<close>

class len2 = len +
  assumes len2_not_1 [simp]: "LENGTH('a) \<noteq> Suc 0"

lemma len2_simps[simp]:
  "LENGTH('a::len2) > Suc 0"
  "LENGTH('a::len2) \<ge> 2"
  subgoal by (metis Suc_lessI len2_not_1 len_gt_0)
  subgoal using \<open>Suc 0 < LENGTH('a)\<close> by linarith
  done
  
lemma len2E: obtains n where "LENGTH('a::len2) = 2+n"
  apply (cases "LENGTH('a)"; simp)
  subgoal for k by (cases k; simp)
  done
  
instance bit0 :: (len) len2 
  by standard simp
  
instance bit1 :: (len) len2 
  by standard simp
  
definition "len2 (TYPE('a::len2)) \<equiv> True"  


(* Original theorem is in simpset, but useless due to non-normalized LHS *)
lemmas [simp] = word_sbin.norm_Rep[simplified]


lemma to_bl_scast_down: "is_down SCAST('a::len \<rightarrow> 'b::len) \<Longrightarrow> to_bl (SCAST('a \<rightarrow> 'b) w) = drop (LENGTH('a)-LENGTH('b)) (to_bl w)"  
  by (simp add: is_down scast_down_drop source_size target_size)
  
lemma [simp]: "from_bool \<Phi> = 0 \<longleftrightarrow> \<not>\<Phi>" by (rule from_bool_0)

declare word_unat.Rep_inject[simp del]
declare word_uint.Rep_inject[simp del]

lemma msb_uint_big: "msb (w::'a::len word) \<longleftrightarrow> uint w \<ge> 2^(LENGTH('a)-1)"      
  apply (simp add: msb_big) 
  by (metis One_nat_def Suc_pred' diff_le_self le_antisym len_gt_0 n_not_Suc_n p2_eq_0 uint_2p word_le_def word_neq_0_conv)

lemma msb_unat_big: "msb (w::'a::len word) \<longleftrightarrow> unat w \<ge> 2^(LENGTH('a)-1)"      
  by (simp add: msb_big word_le_nat_alt)

(* TODO: Move *)  
lemma word1_neqZ_is_one: "(a::1 word) \<noteq> 0 \<longleftrightarrow> a=1"  
  apply transfer
  subgoal for a
    apply (cases "bin_last a")
    by auto
  done
  
lemma word1_cases[cases type]: 
  fixes a :: "1 word" obtains (zero) "a=0" | (one) "a=1"
  apply (cases "a=0")
  by (auto simp: word1_neqZ_is_one)
  
(* TODO: Move *)  
lemma word1_NOT_eq: "~~(x::1 word) = x+1"
  by (auto simp: NOT_eq)

lemma upcast_no_msb[simp]: "LENGTH('small::len) < LENGTH('big::len) \<Longrightarrow> \<not>msb (UCAST('small \<rightarrow> 'big) x)" 
  apply (clarsimp simp: ucast_def msb_word_of_int)
  apply transfer
  using nth_bintr by auto
  

subsection \<open>Integer Division with Rounding Towards Zero\<close>

text \<open>Division with rounding towards zero\<close>

lemma int_sgn_cases: fixes a::int obtains (negative) "a<0" | (zero) "a=0" | (positive) "a>0"
  by (rule linorder_cases)

text \<open>Lemmas to match original definitions from this development to 
  definitions from Word-Library, to which we switched at some point.\<close>
lemma sdiv_int_original_def: "(a::int) sdiv b = (if a\<ge>0 \<longleftrightarrow> b\<ge>0 then \<bar>a\<bar> div \<bar>b\<bar> else - ( \<bar>a\<bar> div \<bar>b\<bar>))"
  apply (cases a rule: int_sgn_cases; cases b rule: int_sgn_cases)
  apply (auto simp: sdiv_int_def sgn_mult)
  done
  
lemma srem_int_original_def: "(a::int) smod b = (if a\<ge>0 then \<bar>a\<bar> mod \<bar>b\<bar> else - (\<bar>a\<bar> mod \<bar>b\<bar>))"
  apply (cases a rule: int_sgn_cases; cases b rule: int_sgn_cases)
  apply (auto 
    simp: smod_int_def sdiv_int_def sgn_mult algebra_simps 
    simp flip: minus_mod_eq_mult_div mult_minus_left)
  done  
  
  
text \<open>Standard properties of remainders\<close>
lemma div_rem_rtz_id: "(a::int) sdiv b * b + a smod b = a"
  by (simp add: smod_int_def)

lemma abs_rem_rtz_lt: "b\<noteq>0 \<Longrightarrow> \<bar>a smod b\<bar> < \<bar>b::int\<bar>"
  using srem_int_original_def by auto
  
text \<open>LLVM documentation: The remainder is either zero, or has the same sign as the dividend\<close>
lemma rem_rtz_sign: "(a::int) smod b = 0 \<or> sgn ((a::int) smod b) = sgn a"
  apply (clarsimp simp: srem_int_original_def)
  by (smt Euclidean_Division.pos_mod_sign sgn_pos zmod_trival_iff)
  

lemma sdiv_positive[simp]: "(a::int)\<ge>0 \<Longrightarrow> b\<ge>0 \<Longrightarrow> a sdiv b = a div b"
  by (simp add: sdiv_int_original_def)

lemma smod_positive[simp]: "(a::int)\<ge>0 \<Longrightarrow> b\<ge>0 \<Longrightarrow> a smod b = a mod b"
  by (auto simp: srem_int_original_def)


subsection \<open>Additions to @{theory "HOL-Word.Bits_Int"}\<close>
declare bin_to_bl_def[simp del]

(* TODO: Move *)
lemma map2_eq_Nil_conv[simp]: "map2 f a b = [] \<longleftrightarrow> a=[] \<or> b=[]"
  by (cases a; cases b; auto)
  
lemma bin_to_bl_eq_Nil_conv[simp]: "bin_to_bl w i = [] \<longleftrightarrow> w=0"
  by (metis bin_to_bl_aux.Z bin_to_bl_def size_bin_to_bl)

lemma bin_to_bl_aux_eq_Nil_conv[simp]: "bin_to_bl_aux w i acc = [] \<longleftrightarrow> w=0 \<and> acc=[]"
  by (metis bin_to_bl_aux.Z bin_to_bl_eq_Nil_conv take.simps(1) take_bin2bl_lem1)

lemma bl_to_bin_True [simp]: "bl_to_bin (True # bl) = bl_to_bin bl + 2^length bl"
  by (metis Bit_B1 add.commute add.right_neutral bin_bl_bin bin_cat_num bl_bin_bl bl_to_bin_aux.simps(2) bl_to_bin_aux_alt mult_1s(1) mult_zero_left numeral_code(1))

lemma bl_to_bin_append_num: "bl_to_bin (a@b) = 2^length b * bl_to_bin a + bl_to_bin b"
  by (simp add: bin_cat_num bl_to_bin_app_cat)

lemma bl_to_bin_rep_True: "bl_to_bin (replicate n True) = 2 ^ n - 1"
  by (metis bin_bl_bin bin_to_bl_minus1 bintr_Min)

lemma bl_to_bin_rep_T: "bl_to_bin (replicate n True @ bl) = 2 ^ length bl * (2 ^ n - 1) + bl_to_bin bl"
  by (simp add: bl_to_bin_append_num bl_to_bin_rep_True algebra_simps)

lemma bin_to_bl_strunc[simp]: 
  "w\<^sub>1 \<le> w\<^sub>2 + 1 \<Longrightarrow> bin_to_bl w\<^sub>1 (sbintrunc w\<^sub>2 i) = bin_to_bl w\<^sub>1 i"
  by (simp add: bintrunc_sbintrunc_le bl_to_bin_inj)

lemma bin_last_x2[simp]: "bin_last (2*n) = False" by (auto simp: bin_last_def)
lemma bin_rest_x2[simp]: "bin_rest (2*n) = n" by (auto simp: bin_rest_def)

lemma bin_to_bl_x2[simp]: "w\<noteq>0 \<Longrightarrow> bin_to_bl w (2*n) = bin_to_bl (w-1) n @ [False]"
  by (cases w) (auto simp: bin_to_bl_def bin_to_bl_aux_append)

lemma bin_to_bl_xp2[simp]:
  assumes "n\<le>w" 
  shows "bin_to_bl w (x * 2^n) = bin_to_bl (w-n) x @ replicate n False"
proof -
  have [simp]: "x * (2 * 2 ^ n) = 2 * (x*2^n)" for n by auto

  show ?thesis using assms
    by (induction n) (auto simp: drop_bin2bl[symmetric] replicate_append_same)
qed

lemma bintrunc_eq_if_in_range: "bintrunc w i = i \<longleftrightarrow> i\<in>uints w"
  by (simp add: bintrunc_mod2p int_mod_lem uints_num)

lemma sbintrunc_eq_if_in_range: "sbintrunc (w-Suc 0) i = i \<longleftrightarrow> i\<in>sints w"
  by (clarsimp simp: sints_def sbintrunc_eq_in_range)

lemma bl_to_bin_in_uints: "bl_to_bin x \<in> uints (length x)"
  using bl_to_bin_def bintrunc_eq_if_in_range by fastforce


(* TODO: This is probably a special case of a more general scheme! *)

method_setup pull_mods = \<open>Scan.succeed (fn ctxt =>  SIMPLE_METHOD' (
  CONVERSION (Conv.top_conv (K (Conv.try_conv (Conv.rewrs_conv @{thms pull_mods}))) ctxt)
))\<close>

method_setup pull_push_mods = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (
  CONVERSION (Conv.top_conv (K (Conv.try_conv (Conv.rewrs_conv @{thms pull_mods}))) ctxt)
  THEN' (full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms mod_mod_trivial push_mods}))
))\<close> \<open>Pull in, then push out modulos\<close>


subsection \<open>Signed integers in Two's Complement Representation\<close>

definition bl_to_sbin :: "bool list \<Rightarrow> int" 
  where "bl_to_sbin bl = sbintrunc (length bl - 1) (bl_to_bin bl)"

lemma bl_to_sbin_alt:
  "bl_to_sbin bl = (case bl of [] \<Rightarrow> 0 | b#bl \<Rightarrow> (if b then -(2^length bl) else 0) + bl_to_bin bl)"
  apply (auto simp: bl_to_sbin_def sbintrunc_mod2p bl_to_bin_ge0 bl_to_bin_lt2p split: list.splits)
  by (smt bl_to_bin_ge0 bl_to_bin_lt2p int_mod_eq')

lemma bl_sbin_bl[simp]: "bin_to_bl (length bs) (bl_to_sbin bs) = bs"
  unfolding bl_to_sbin_def by auto

lemma sbin_bl_bin[simp]:
  "0<w \<Longrightarrow> bl_to_sbin (bin_to_bl w i) = sbintrunc (w-1) i"
  unfolding bl_to_sbin_def by auto

lemma bl_to_sbin_in_sints: "bl_to_sbin x \<in> sints (length x)"
  using bl_to_sbin_def sbintrunc_eq_if_in_range by fastforce

subsection \<open>Lifting of Operations\<close>  

definition "cnv_uop1 f a \<equiv> bin_to_bl (length a) (f (bl_to_bin a))"
definition "cnv_uop2 nel f a b \<equiv> 
  if length a = length b then 
    bin_to_bl (length a) (f (bl_to_bin a) (bl_to_bin b))
  else nel ()"

definition "cnv_uop2b nel f a b \<equiv> if length a = length b then
    f (bl_to_bin a) (bl_to_bin b)
  else nel ()"

lemma cnv_uop1_correct[simp]: 
  "bl_to_bin (cnv_uop1 f a) = bintrunc (length a) (f (bl_to_bin a))
  \<and> length (cnv_uop1 f a) = length a"
  by (auto simp: cnv_uop1_def)

lemma cnv_uop2_correct[simp]: 
  "length a = length b 
    \<Longrightarrow> bl_to_bin (cnv_uop2 nel f a b) = bintrunc (length a) (f (bl_to_bin a) (bl_to_bin b))
      \<and> length (cnv_uop2 nel f a b) = length b"
  by (auto simp: cnv_uop2_def)

lemma cnv_uop2b_correct[simp]: 
  "length a = length b \<Longrightarrow> cnv_uop2b nel f a b = f (bl_to_bin a) (bl_to_bin b)"
  by (auto simp: cnv_uop2b_def)

definition "cnv_sop1 f a \<equiv> bin_to_bl (length a) (f (bl_to_sbin a))"
definition "cnv_sop2 nel f a b \<equiv> 
  if length a = length b then
    bin_to_bl (length a) (f (bl_to_sbin a) (bl_to_sbin b))
  else 
    nel ()"

definition "cnv_sop2b nel f a b \<equiv> if length a = length b then
    f (bl_to_sbin a) (bl_to_sbin b)
  else nel ()"

lemma length_cnv_sop1[simp]: "length (cnv_sop1 f a) = length a"
  unfolding cnv_sop1_def by auto

lemma cnv_sop1_correct[simp]: "a\<noteq>[] 
  \<Longrightarrow> bl_to_sbin (cnv_sop1 f a) = sbintrunc (length a - 1) (f (bl_to_sbin a))
    \<and> length (cnv_sop1 f a) = length a"
  by (auto simp: cnv_sop1_def)
  
lemma cnv_sop2_correct[simp]: "a\<noteq>[] \<Longrightarrow> length a = length b 
  \<Longrightarrow> bl_to_sbin (cnv_sop2 nel f a b) = sbintrunc (length a - 1) (f (bl_to_sbin a) (bl_to_sbin b))
    \<and> length (cnv_sop2 nel f a b) = length b"
  apply (auto simp: cnv_sop2_def)
  using sbin_bl_bin by fastforce

lemma cnv_sop2_correct'[simp]: "b\<noteq>[] \<Longrightarrow> length a = length b 
  \<Longrightarrow> bl_to_sbin (cnv_sop2 nel f a b) = sbintrunc (length a - 1) (f (bl_to_sbin a) (bl_to_sbin b))
    \<and> length (cnv_sop2 nel f a b) = length b"
  by (metis cnv_sop2_correct length_0_conv)
  
lemma cnv_sop2b_correct[simp]: 
  "length a = length b \<Longrightarrow> cnv_sop2b nel f a b = f (bl_to_sbin a) (bl_to_sbin b)"
  by (auto simp: cnv_sop2b_def)


lemma cnv_uop1_empty_iff[simp]: "cnv_uop1 f a = [] \<longleftrightarrow> a=[]"
  by (auto simp: cnv_uop1_def)

lemma cnv_uop2_empty_iff[simp]: "cnv_uop2 nel f a b = [] \<longleftrightarrow> (if length a = length b then a=[] else nel () = [])"
  by (auto simp: cnv_uop2_def)

lemma cnv_sop2_empty_iff[simp]: "cnv_sop2 nel f a b = [] \<longleftrightarrow> (if length a = length b then a=[] else nel () = [])"
  by (auto simp: cnv_sop2_def)

lemma cnv_sop1_empty_iff[simp]: "cnv_sop1 f a = [] \<longleftrightarrow> a=[]"
  by (auto simp: cnv_sop1_def)

subsubsection \<open>Operations Independent of Signed/Unsigned Interpretation \<close>

definition "signed_unsigned_compat1 f \<equiv> \<forall>w a. sbintrunc w (f (sbintrunc w a)) = sbintrunc w (f a)"
definition "signed_unsigned_compat2 f \<equiv> \<forall>w a b. sbintrunc w (f (sbintrunc w a) (sbintrunc w b)) = sbintrunc w (f a b)"

lemma cnv_uop1_to_sop1:
  assumes "signed_unsigned_compat1 f"
  shows "cnv_uop1 f a = cnv_sop1 f a"
  apply (auto simp: cnv_uop1_def cnv_sop1_def bl_to_sbin_def)
  using assms unfolding signed_unsigned_compat1_def
  by (metis (no_types, lifting) bin_bl_bin bintrunc_sbintruncS0 bl_bin_bl length_greater_0_conv size_bin_to_bl)

lemma cnv_uop2_to_sop2:
  assumes [simp]: "length a = length b"
  assumes "signed_unsigned_compat2 f"
  shows "cnv_uop2 nel f a b = cnv_sop2 nel f a b"
  apply (auto simp: cnv_uop2_def cnv_sop2_def bl_to_sbin_def)
  using assms(2) unfolding signed_unsigned_compat2_def
  by (metis (no_types, lifting) bin_bl_bin bintrunc_sbintruncS0 bl_bin_bl length_greater_0_conv size_bin_to_bl)

lemma cnv_uop1_compat_correct:
  assumes [simp]: "signed_unsigned_compat1 f"
  assumes [simp]: "a\<noteq>[]"
  shows "bl_to_sbin (cnv_uop1 f a) = sbintrunc (length a - 1) (f (bl_to_sbin a))"
  by (auto simp: cnv_uop1_to_sop1)

lemma cnv_uop2_compat_correct:
  assumes [simp]: "length a = length b"
  assumes [simp]: "signed_unsigned_compat2 f"
  assumes [simp]: "a\<noteq>[]"
  shows "bl_to_sbin (cnv_uop2 nel f a b) = sbintrunc (length a - 1) (f (bl_to_sbin a) (bl_to_sbin b))"
  by (auto simp: cnv_uop2_to_sop2)

lemma cnv_uop2_compat_correct':
  assumes [simp]: "length a = length b"
  assumes [simp]: "signed_unsigned_compat2 f"
  assumes [simp]: "b\<noteq>[]"
  shows "bl_to_sbin (cnv_uop2 nel f a b) = sbintrunc (length a - 1) (f (bl_to_sbin a) (bl_to_sbin b))"
  by (metis assms cnv_uop2_compat_correct length_0_conv)
  

lemma signed_unsigned_compat2_plus[simp]: "signed_unsigned_compat2 (+)"
  apply (auto simp: signed_unsigned_compat2_def sbintrunc_mod2p)
  apply (pull_push_mods)
  by (simp add: algebra_simps)
  
lemma signed_unsigned_compat2_minus[simp]: "signed_unsigned_compat2 (-)"
  apply (clarsimp simp: signed_unsigned_compat2_def sbintrunc_mod2p)
  apply (pull_push_mods)
  by (simp add: algebra_simps)

lemma signed_unsigned_compat2_mult[simp]: "signed_unsigned_compat2 (*)"
  apply (auto simp: signed_unsigned_compat2_def sbintrunc_mod2p)
  apply pull_push_mods
  by (simp add: algebra_simps)


subsection \<open>Bitwise Interpretation of Operations\<close>
text \<open>Provides an additional sanity check, by equating our definitions with the definitions found in
  @{theory "HOL-Word.Bits_Int"}. Unfortunately, they do not define minus there.\<close>

lemma cnv_plus_rbl_conv: "length a = length b \<Longrightarrow> cnv_uop2 nel (+) a b = rev (rbl_add (rev a) (rev b))"
  apply (rule sym)
  apply (subst bl_bin_bl[symmetric, of a])
  apply (subst bl_bin_bl[symmetric, of b])
  by (auto simp: cnv_uop2_def rbl_add simp del: bl_bin_bl)

lemma cnv_mult_rbl_conv: "length a = length b \<Longrightarrow> cnv_uop2 nel (*) a b = rev (rbl_mult (rev a) (rev b))"
  apply (rule sym)
  apply (subst bl_bin_bl[symmetric, of a])
  apply (subst bl_bin_bl[symmetric, of b])
  by (auto simp: cnv_uop2_def rbl_mult simp del: bl_bin_bl)

lemma cnv_AND_bl_conv: "length a = length b \<Longrightarrow> cnv_uop2 nel (AND) a b = map2 (\<and>) a b"
  apply (rule sym)
  apply (subst bl_bin_bl[symmetric, of a])
  apply (subst bl_bin_bl[symmetric, of b])
  by (auto simp: cnv_uop2_def bl_and_bin simp del: bl_bin_bl)

lemma cnv_OR_bl_conv: "length a = length b \<Longrightarrow> cnv_uop2 nel (OR) a b = map2 (\<or>) a b"
  apply (rule sym)
  apply (subst bl_bin_bl[symmetric, of a])
  apply (subst bl_bin_bl[symmetric, of b])
  by (auto simp: cnv_uop2_def bl_or_bin simp del: bl_bin_bl)

(* TODO: Lemma bl_xor_bin has non-normalized lhs! *)
lemma cnv_XOR_bl_conv: "length a = length b \<Longrightarrow> cnv_uop2 nel (XOR) a b = map2 (\<noteq>) a b"
  apply (rule sym)
  apply (subst bl_bin_bl[symmetric, of a])
  apply (subst bl_bin_bl[symmetric, of b])
  by (auto simp: bl_xor_bin[simplified] cnv_uop2_def simp del: bl_bin_bl)

lemma cnv_NOT_bl_conv: "cnv_uop1 (bitNOT) a = map Not a"
  apply (rule sym)
  apply (subst bl_bin_bl[symmetric, of a])
  apply (simp only: bl_not_bin)
  by (auto simp: cnv_uop1_def)

lemma cnv_SHL_bl_conv: "n\<le>length a \<Longrightarrow> cnv_uop1 (\<lambda>x. x * 2^n) a = drop n a @ replicate n False"
  by (auto simp: cnv_uop1_def bl_bin_bl_rep_drop)

lemma butlast_bin_to_bl_aux: "acc\<noteq>[] \<Longrightarrow> butlast (bin_to_bl_aux w i acc) = bin_to_bl_aux w i (butlast acc)"
  by (simp add: bin_to_bl_aux_alt butlast_append)

lemma bin_rest_div2[simp]: "bin_rest (n div 2) = bin_rest n div 2"
  by (auto simp: bin_rest_def)

lemma bin_last_div2[simp]: "bin_last (n div 2) = bin_last (bin_rest n)"
  by (auto simp: bin_rest_def)


find_theorems bin_to_bl_aux "(@)"


lemma bin_to_bl_Suc: "bin_to_bl (Suc w) i = bin_to_bl w (bin_rest i) @ [bin_last i]"
  by (simp add: bin_to_bl_aux_append bin_to_bl_def)


lemma "butlast (bin_to_bl w n) = bin_to_bl (w-1) (bin_rest n)" oops
  thm butlast_rest_bin


  find_theorems "bin_to_bl _ _ ! _"

lemma bin_to_bl_div2_shift: "\<lbrakk>w\<noteq>0; n\<ge>0; n<2^w\<rbrakk> \<Longrightarrow> bin_to_bl w (n div 2) = False # butlast (bin_to_bl w n)"
  apply (cases w; simp)
  apply (rule nth_equalityI)
  apply (auto simp: butlast_rest_bin bin_rest_def nth_Cons nth_bin_to_bl bin_nth_eq_mod split: nat.splits)
  done  


lemma div_div_p2_eq_div_p2s: 
  "w div (2^a) div (2^b) = (w::int) div 2^(a+b)"
  "w div 2 div (2^b) = (w::int) div 2^(Suc b)"
  by (simp_all add: div_mult2_eq power_add zdiv_zmult2_eq)

lemma bin_to_bl_div2p_shift: "\<lbrakk>n\<ge>0; n<2^w; k\<le>w\<rbrakk> \<Longrightarrow> bin_to_bl w (n div 2^k) = replicate k False @ take (w-k) (bin_to_bl w n)"
  apply (rule nth_equalityI)
  apply (auto simp: butlast_rest_bin bin_rest_def nth_Cons nth_append nth_bin_to_bl bin_nth_eq_mod split: nat.splits)
  subgoal 
    apply (simp add: div_div_p2_eq_div_p2s)
    by (smt Nat.le_add_diff Suc_leI div_pos_pos_trivial even_zero not_less power_strict_increasing_iff)
  subgoal 
    by (smt Nat.add_diff_assoc2 Suc_leI add.commute power_add zdiv_zmult2_eq zero_le_power_eq) 
  subgoal 
    by (smt Nat.add_diff_assoc2 Suc_leI add.commute power_add zdiv_zmult2_eq zero_le_power_eq) 
  done  
   
  

lemma cnv_LSHR_bl_conv: "n\<le>length a \<Longrightarrow> cnv_uop1 (\<lambda>x. x div 2^n) a = replicate n False @ take (length a - n) a"
  apply (cases "length a")
  apply (auto simp: cnv_uop1_def bin_to_bl_div2p_shift)
  by (metis bin_to_bl_div2p_shift bl_bin_bl bl_to_bin_ge0 bl_to_bin_lt2p)


text \<open>Note: This division is with rounding down!\<close>
lemma bin_to_bl_sdiv2_shift:
  assumes ran: "-(2^w)\<le>i" "i<2^w"
  shows "bin_to_bl (Suc w) (i div 2) = hd (bin_to_bl (Suc w) i) # butlast (bin_to_bl (Suc w) i)"
proof -
  have "\<lbrakk> \<not> 0 \<le> (i::int)\<rbrakk> \<Longrightarrow> i div (2*2^w) = -1" using ran
    by (smt cancel_div_mod_rules(2) div_pos_pos_trivial mod_add_self2 mult_cancel_left1 mult_minus_right)

  then show ?thesis using ran
    apply (rule_tac nth_equalityI)
    by (auto 
        simp: butlast_rest_bin bin_rest_def nth_Cons bl_sbin_sign nth_bin_to_bl bin_nth_eq_mod bin_sign_def sbintrunc_mod2p div_div_p2_eq_div_p2s 
        split: nat.splits)
qed  

lemma bin_to_bl_sdiv2p_shift:
  assumes ran: "-(2^w)\<le>i" "i<2^w" and K: "k<Suc w"
  shows "bin_to_bl (Suc w) (i div 2^k) = replicate k (hd (bin_to_bl (Suc w) i)) @ take (Suc w - k) (bin_to_bl (Suc w) i)"
proof -

  have "\<lbrakk>\<not>0\<le>i; x\<ge>w\<rbrakk> \<Longrightarrow> i div (2^x) = -1" for x using ran
    apply auto
    by (smt cancel_div_mod_rules(2) int_mod_eq' linorder_not_le mod_add_self2 mult_cancel_left1 mult_minus_right power_strict_increasing_iff)

  with ran K show ?thesis
    apply (rule_tac nth_equalityI)
    apply (auto 
        simp: butlast_rest_bin bin_rest_def nth_Cons bl_sbin_sign nth_bin_to_bl bin_nth_eq_mod bin_sign_def sbintrunc_mod2p div_div_p2_eq_div_p2s 
        simp: nth_append algebra_simps
        split: nat.splits)
    by (smt Nat.le_add_diff diff_is_0_eq' div_pos_pos_trivial even_zero less_imp_le power_strict_increasing_iff zero_less_diff)
qed    

lemma cnv_ASHR_bl_conv: "n<length a \<Longrightarrow> cnv_sop1 (\<lambda>x. x div 2^n) a = replicate n (hd a) @ take (length a - n) a"
  apply (cases "length a")
  apply (auto simp: cnv_sop1_def) 
  by (metis bin_to_bl_sdiv2p_shift bl_sbin_bl bl_to_sbin_def diff_Suc_1 sbintr_ge sbintr_lt)


subsection \<open>Signed and Unsigned Extension and Truncation\<close>

definition bl_trunc :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where "bl_trunc w bl \<equiv> drop (length bl - w) bl"

lemma bl_trunc_ge[simp]: "length bl < w \<Longrightarrow> bl_trunc w bl = bl"
  by (simp add: bl_trunc_def)

lemma trunc_bl_to_bin[simp]: "bl_to_bin (bl_trunc w bl) = bintrunc w (bl_to_bin bl)"
  by (simp add: bl_trunc_def trunc_bl2bin)

lemma trunc_bl_to_sbin[simp]: 
  "w>0 \<Longrightarrow> bl_to_sbin (bl_trunc w bl) = sbintrunc (w-1) (bl_to_sbin bl)"
  apply (cases "w \<le> length bl")
  apply (auto simp: bl_trunc_def bl_to_sbin_def bl2bin_drop min_def)
  done

lemma bl_trunc_len[simp]: "length (bl_trunc w bl) = min w (length bl)"
  by (auto simp: bl_trunc_def)

lemma bl_trunc_eq_Nil_conv[simp]: "bl_trunc w l = [] \<longleftrightarrow> w=0 \<or> l=[]"
  by (cases l) (auto simp: bl_trunc_def)

definition bl_zext :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where "bl_zext w bl \<equiv> replicate (w - length bl) False @ bl"

lemma bl_zext_le[simp]: "w\<le>length bl \<Longrightarrow> bl_zext w bl = bl"
  by (auto simp: bl_zext_def)

lemma bl_zext_to_bin[simp]: "bl_to_bin (bl_zext w bl) = bl_to_bin bl"
  by (auto simp: bl_zext_def bl_to_bin_rep_F)

lemma bl_zext_len[simp]: "length (bl_zext w bl) = max w (length bl)"
  by (auto simp: bl_zext_def)

lemma bl_zext_Nil_conv[simp]: "bl_zext w bl = [] \<longleftrightarrow> w=0 \<and> bl = []"
  by (auto simp: bl_zext_def)

definition bl_sext :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where "bl_sext w bl \<equiv> replicate (w - length bl) (hd bl) @ bl"


lemma bl_sext_le[simp]: "w\<le>length bl \<Longrightarrow> bl_sext w bl = bl"
  by (auto simp: bl_sext_def)

lemma bl_to_sbin_pos_conv_bin: "\<not>hd bl \<Longrightarrow> bl_to_sbin bl = bl_to_bin bl"
  by (auto simp: bl_to_sbin_alt split: list.split)

lemma bl_to_sbin_neg_conv_bin: "bl\<noteq>[] \<Longrightarrow> hd bl \<Longrightarrow> bl_to_sbin bl = bl_to_bin bl - 2^(length bl)"
  by (auto simp: bl_to_sbin_alt split: list.split)

lemma bl_sext_to_sbin[simp]: 
  assumes [simp]: "bl\<noteq>[]" 
  shows "bl_to_sbin (bl_sext w bl) = bl_to_sbin bl"
  apply (cases "w>length bl"; simp?)
proof (cases "hd bl")
  case True
  assume "length bl < w"
  with True show ?thesis 
    apply (auto simp: bl_to_sbin_neg_conv_bin bl_sext_def bl_to_bin_rep_T algebra_simps)
    by (metis diff_add_inverse less_imp_add_positive power_add)
next
  case False
  assume "length bl < w"
  with False show ?thesis by (auto simp: bl_to_sbin_pos_conv_bin bl_sext_def bl_to_bin_rep_F)
qed

lemma bl_sext_len[simp]: "length (bl_sext w bl) = max w (length bl)"
  by (auto simp: bl_sext_def)

lemma bl_sext_Nil_conv[simp]: "bl_sext w bl = [] \<longleftrightarrow> w=0 \<and> bl = []"
  by (auto simp: bl_sext_def)


subsection \<open>LLVM Integer Datatype\<close>

typedef lint = "{l::bool list. True }"
  morphisms lint_to_bits bits_to_lint
  by auto

setup_lifting type_definition_lint

(*lemma Rep_lint_neq_Nil[simp]: "lint_to_bits x \<noteq> []"
  using lint_to_bits by simp
*)  

instantiation lint :: equal
begin
  lift_definition equal_lint :: "lint \<Rightarrow> lint \<Rightarrow> bool" is "equal_class.equal" .

  instance
    apply intro_classes  
    apply transfer
    apply (rule equal_eq)
    done

end



lift_definition width :: "lint \<Rightarrow> nat" is length .
lift_definition lint_to_uint :: "lint \<Rightarrow> int" is bl_to_bin .
lift_definition lint_to_sint :: "lint \<Rightarrow> int" is bl_to_sbin .

(*lemma width_notZ[simp]: "width a \<noteq> 0" by transfer auto*)

lemma uint_lower_bound[simp]: "0\<le>lint_to_uint a"
  apply transfer using bl_to_bin_ge0 by auto

lemma uint_upper_bound[simp]: "lint_to_uint a < 2^width a"
  apply transfer by (simp add: bl_to_bin_lt2p)

lemma sint_lower_bound[simp]: "-(2^(width a - 1))\<le>lint_to_sint a"
  apply transfer by (simp add: bl_to_sbin_def sbintr_ge)

lemma sint_upper_bound[simp]: "lint_to_sint a < 2^(width a - 1)"
  apply transfer by (simp add: bl_to_sbin_def sbintr_lt)


subsubsection \<open>Overflows\<close>

definition "uovf1 f a \<equiv> f (lint_to_uint a) \<notin> uints (width a)"
definition "sovf1 f a \<equiv> f (lint_to_sint a) \<notin> sints (width a)"

definition "uovf2 f a b \<equiv> f (lint_to_uint a) (lint_to_uint b) \<notin> uints (width a)"
definition "sovf2 f a b \<equiv> f (lint_to_sint a) (lint_to_sint b) \<notin> sints (width a)"

subsubsection \<open>Operations\<close>

lift_definition lconst :: "nat \<Rightarrow> int \<Rightarrow> lint" is "\<lambda>w i. bin_to_bl w i" by simp

lemma width_lconst[simp]: "width (lconst w i) = w"
  by transfer auto

lemma uint_const[simp]: "lint_to_uint (lconst w c) = bintrunc w c"
  by transfer auto

lemma sint_const[simp]: "w\<noteq>0 \<Longrightarrow> lint_to_sint (lconst w c) = sbintrunc (w-1) c"
  by transfer (auto)

lemma bits_zero[simp]: "lint_to_bits (lconst w 0) = replicate w False"
  by transfer (auto simp: bin_to_bl_zero)

lemma bits_minus1[simp]: "lint_to_bits (lconst w (-1)) = replicate w True"
  by transfer (auto simp: bin_to_bl_minus1)

lemma lconst_eq_iff[simp]: 
  "lconst w c = lconst w' c' \<longleftrightarrow> w'=w \<and> (c' mod 2^w = c mod 2^w)"
  apply safe
  subgoal
    apply transfer
    by (metis len_bin_to_bl)
  subgoal
    apply transfer
    by (metis bin_bl_bin bintrunc_mod2p len_bin_to_bl)
  subgoal 
    apply transfer  
    by (auto simp: max_def bintrunc_mod2p bl_to_bin_inj)
  done    
  
  
  
definition "lint_abort (_::unit) \<equiv> lint_to_bits undefined"
definition "lint_abort_bool (_::unit) \<equiv> undefined::bool"

(*lemma l_abort_ne[simp]: "lint_abort () \<noteq> []" unfolding lint_abort_def by auto*)
declare [[ code abort: lint_abort lint_abort_bool]]

instantiation lint :: "{plus,minus,times,divide,modulo,uminus,signed_div}"
begin
  lift_definition plus_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 (lint_abort) (+)" by simp
  lift_definition minus_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 (lint_abort) (-)" by simp
  lift_definition times_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 (lint_abort) (*)" by simp
  lift_definition divide_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 (lint_abort) (div)" by simp
  lift_definition modulo_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 (lint_abort) (mod)" by simp
  
  lift_definition uminus_lint :: "lint \<Rightarrow> lint" is "cnv_sop1 uminus" by simp

  definition sdivrem_ovf :: "lint \<Rightarrow> lint \<Rightarrow> bool" where
    "sdivrem_ovf a b \<equiv> lint_to_sint a sdiv lint_to_sint b \<notin> sints (width a)"
  
  lift_definition sdiv_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" 
    is "\<lambda>a b. if bl_to_sbin a sdiv bl_to_sbin b \<in> sints (length a) then cnv_sop2 lint_abort (sdiv) a b else lint_abort ()"
    by simp
    
  lift_definition smod_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" 
    is "\<lambda>a b. if bl_to_sbin a sdiv bl_to_sbin b \<in> sints (length a) then cnv_sop2 lint_abort (smod) a b else lint_abort ()" 
    by simp
  
  
  instance ..
end


lemma width_plus[simp]:
  assumes "width a = width b"
  shows "width (a+b) = width b"
  using assms by transfer auto

lemma uint_plus[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a+b) = bintrunc (width b) (lint_to_uint a + lint_to_uint b)"
  using assms by transfer auto

lemma sint_plus[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  shows "lint_to_sint (a+b) = sbintrunc (width b - 1) (lint_to_sint a + lint_to_sint b)"
  using assms by transfer (auto simp: cnv_uop2_compat_correct')

lemma width_minus[simp]:
  assumes "width a = width b"
  shows "width (a-b) = width b"
  using assms by transfer auto

lemma uint_minus[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a-b) = bintrunc (width b) (lint_to_uint a - lint_to_uint b)"
  using assms
  by transfer auto

lemma sint_minus[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  shows "lint_to_sint (a-b) = sbintrunc (width b - 1) (lint_to_sint a - lint_to_sint b)"
  using assms
  by transfer (auto simp: cnv_uop2_compat_correct')

lemma width_times[simp]:
  assumes "width a = width b"
  shows "width (a*b) = width b"
  using assms by transfer auto

lemma uint_times[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a*b) = bintrunc (width b) (lint_to_uint a * lint_to_uint b)"
  using assms
  by transfer auto

lemma sint_times[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  shows "lint_to_sint (a*b) = sbintrunc (width b - 1) (lint_to_sint a * lint_to_sint b)"
  using assms
  by transfer (auto simp: cnv_uop2_compat_correct')

lemma width_divide[simp]:
  assumes "width a = width b"
  shows "width (a div b) = width b"
  using assms by transfer auto

lemma uint_divide[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a div b) = bintrunc (width b) (lint_to_uint a div lint_to_uint b)"
  using assms
  by transfer auto

lemma width_sdivide[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  assumes "\<not>sdivrem_ovf a b"
  shows "width (a sdiv b) = width b"
  using assms unfolding sdivrem_ovf_def
  by transfer auto

lemma sint_sdivide[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  assumes "\<not>sdivrem_ovf a b"
  shows "lint_to_sint (a sdiv b) = sbintrunc (width b - 1) ((lint_to_sint a) sdiv (lint_to_sint b))"
  using assms unfolding sdivrem_ovf_def
  by transfer auto


lemma width_modulo[simp]:
  assumes "width a = width b"
  shows "width (a mod b) = width b"
  using assms by transfer auto

lemma uint_modulo[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a mod b) = bintrunc (width b) (lint_to_uint a mod lint_to_uint b)"
  using assms
  by transfer auto

lemma width_srem[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  assumes "\<not>sdivrem_ovf a b"
  shows "width (a smod b) = width b"
  using assms unfolding sdivrem_ovf_def
  by transfer auto

lemma sint_remainder[simp]:
  assumes "width a = width b" "width b \<noteq> 0"
  assumes "\<not>sdivrem_ovf a b"
  shows "lint_to_sint (a smod b) = sbintrunc (width b - 1) ((lint_to_sint a) smod (lint_to_sint b))"
  using assms unfolding sdivrem_ovf_def
  by transfer auto

lemma width_uminus[simp]:
  "width (- a) = width a"
  by transfer auto

lemma sint_uminus[simp]: 
  "width a \<noteq> 0 \<Longrightarrow> lint_to_sint (- a) = sbintrunc (width a - 1) (- lint_to_sint a)"
  by transfer auto
  

instantiation lint :: "{ord}"
begin
  lift_definition less_lint :: "lint \<Rightarrow> lint \<Rightarrow> bool" is "cnv_uop2b lint_abort_bool (<)" .
  lift_definition less_eq_lint :: "lint \<Rightarrow> lint \<Rightarrow> bool" is "cnv_uop2b lint_abort_bool (\<le>)" .
  instance ..
end

lift_definition sless_lint :: "lint \<Rightarrow> lint \<Rightarrow> bool" (infix "<\<^sub>s" 50) is "cnv_sop2b lint_abort_bool (<)" .
lift_definition sless_eq_lint :: "lint \<Rightarrow> lint \<Rightarrow> bool" (infix "\<le>\<^sub>s" 50) is "cnv_sop2b lint_abort_bool (\<le>)" .

lemma uint_less[simp]: 
  assumes "width a = width b"
  shows "a < b \<longleftrightarrow> lint_to_uint a < lint_to_uint b"
  using assms by transfer auto

lemma uint_less_eq[simp]: 
  assumes "width a = width b"
  shows "a \<le> b \<longleftrightarrow> lint_to_uint a \<le> lint_to_uint b"
  using assms by transfer auto

lemma sint_less[simp]: 
  assumes "width a = width b"
  shows "a <\<^sub>s b \<longleftrightarrow> lint_to_sint a < lint_to_sint b"
  using assms by transfer auto

lemma sint_less_eq[simp]: 
  assumes "width a = width b"
  shows "a \<le>\<^sub>s b \<longleftrightarrow> lint_to_sint a \<le> lint_to_sint b"
  using assms by transfer auto

text \<open>Yields \<open>0\<^sub>1\<close> on attempt to truncate to zero\<close>
lift_definition trunc :: "nat \<Rightarrow> lint \<Rightarrow> lint" is "\<lambda>w a. if w=0 then [False] else bl_trunc w a"
  by auto

lemma width_trunc[simp]: "w\<noteq>0 \<Longrightarrow> width (trunc w a) = min w (width a)" by transfer auto

lemma uint_trunc[simp]: "w\<noteq>0 \<Longrightarrow> lint_to_uint (trunc w a) = bintrunc w (lint_to_uint a)"
  by transfer auto

lemma sint_trunc[simp]: "w\<noteq>0 \<Longrightarrow> lint_to_sint (trunc w a) = sbintrunc (w-1) (lint_to_sint a)"
  by transfer auto

lift_definition zext :: "nat \<Rightarrow> lint \<Rightarrow> lint" is "bl_zext" by simp
lift_definition sext :: "nat \<Rightarrow> lint \<Rightarrow> lint" is "bl_sext" by simp

lemma width_zext[simp]: "width (zext w a) = max w (width a)"
  by transfer auto
lemma width_sext[simp]: "width (sext w a) = max w (width a)"
  by transfer auto

lemma uint_zext[simp]: "lint_to_uint (zext w a) = lint_to_uint a"
  by transfer auto

lemma sint_sext[simp]: "width a \<noteq> 0 \<Longrightarrow> lint_to_sint (sext w a) = lint_to_sint a"
  by transfer auto


instantiation lint :: bit_operations
begin
  lift_definition bitAND_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 lint_abort (AND)" by simp
  lift_definition bitOR_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 lint_abort (OR)" by simp
  lift_definition bitXOR_lint :: "lint \<Rightarrow> lint \<Rightarrow> lint" is "cnv_uop2 lint_abort (XOR)" by simp
  lift_definition bitNOT_lint :: "lint \<Rightarrow> lint" is "cnv_uop1 (bitNOT)" by simp

  instance ..
end

lemma width_AND[simp]:
  assumes "width a = width b"
  shows "width (a AND b) = width b"
  using assms by transfer auto

lemma uint_AND[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a AND b) = lint_to_uint a AND lint_to_uint b"
  using assms apply (transfer)
  apply (auto simp: )
  by (metis bin_trunc_ao(1) trunc_bl2bin_len)

lemma width_OR[simp]:
  assumes "width a = width b"
  shows "width (a OR b) = width b"
  using assms by transfer auto

lemma uint_OR[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a OR b) = lint_to_uint a OR lint_to_uint b"
  using assms apply (transfer)
  by (metis bin_trunc_ao(2) cnv_uop2_correct trunc_bl2bin_len)

lemma width_XOR[simp]:
  assumes "width a = width b"
  shows "width (a XOR b) = width b"
  using assms by transfer auto

lemma uint_XOR[simp]:
  assumes "width a = width b"
  shows "lint_to_uint (a XOR b) = lint_to_uint a XOR lint_to_uint b"
  using assms apply (transfer)
  by (metis bin_trunc_xor' cnv_uop2_correct trunc_bl2bin_len)

lemma width_NOT[simp]:
  "width (NOT a) = width a"
  by transfer auto

lemma uint_NOT[simp]:
  shows "lint_to_uint (NOT a) = bintrunc (width a) (NOT (lint_to_uint a))"
  by transfer auto

lemma bits_NOT[simp]: "lint_to_bits (NOT a) = map Not (lint_to_bits a)"
  by transfer (auto simp: cnv_NOT_bl_conv)

lemma bits_AND[simp]: "width a = width b \<Longrightarrow> lint_to_bits (a AND b) = map2 (\<and>) (lint_to_bits a) (lint_to_bits b)"
  by transfer (auto simp: cnv_AND_bl_conv)

lemma bits_OR[simp]: "width a = width b \<Longrightarrow> lint_to_bits (a OR b) = map2 (\<or>) (lint_to_bits a) (lint_to_bits b)"
  by transfer (auto simp: cnv_OR_bl_conv)

lemma bits_XOR[simp]: "width a = width b \<Longrightarrow> lint_to_bits (a XOR b) = map2 (\<noteq>) (lint_to_bits a) (lint_to_bits b)"
  by transfer (auto simp: cnv_XOR_bl_conv)


lift_definition bitSHL :: "lint \<Rightarrow> nat \<Rightarrow> lint" is "\<lambda>bl n. cnv_uop1 (\<lambda>x. x*2^n) bl" by simp
lift_definition bitLSHR :: "lint \<Rightarrow> nat \<Rightarrow> lint" is "\<lambda>bl n. cnv_uop1 (\<lambda>x. x div 2^n) bl" by simp
lift_definition bitASHR :: "lint \<Rightarrow> nat \<Rightarrow> lint" is "\<lambda>bl n. cnv_sop1 (\<lambda>x. x div 2^n) bl" by simp

lemma width_bitSHL[simp]: "width (bitSHL a n) = width a"
  by transfer auto

lemma uint_bitSHL[simp]: "lint_to_uint (bitSHL a n) = bintrunc (width a) (2^n * lint_to_uint a)"
  by transfer (auto simp: algebra_simps)

lemma sint_bitSHL[simp]: "width a \<noteq> 0 \<Longrightarrow> lint_to_sint (bitSHL a n) = sbintrunc (width a - 1) (2^n * lint_to_sint a)"
  apply transfer 
  apply (simp add: bl_to_sbin_def sbintrunc_mod2p bintrunc_mod2p)
  apply (pull_push_mods)
  apply (auto simp: algebra_simps)
  done

lemma width_bitLSHR[simp]: "width (bitLSHR a n) = width a"
  by transfer auto

lemma uint_bitLSHR[simp]: "lint_to_uint (bitLSHR a n) = lint_to_uint a div 2^n"
  apply transfer 
  apply (auto
      simp: bintrunc_mod2p algebra_simps pos_imp_zdiv_nonneg_iff bl_to_bin_ge0
      intro!: mod_pos_pos_trivial)
  by (smt bl_to_bin_ge0 bl_to_bin_lt2p div_by_1 div_pos_pos_trivial int_div_less_self zero_less_power)

lemma width_bitASHR[simp]: "width (bitASHR a n) = width a"
  by transfer auto

lemma sint_bitASHR[simp]: "width a \<noteq> 0 \<Longrightarrow> lint_to_sint (bitASHR a n) = lint_to_sint a div 2^n"
  apply transfer
  using bl_to_sbin_in_sints
  apply (clarsimp simp: sbintrunc_eq_if_in_range sints_num)
  by (smt div_by_1 pos_imp_zdiv_nonneg_iff zdiv_mono2 zdiv_mono2_neg zero_less_power)
  
  

lemma uint_eq:
  "a = b \<longleftrightarrow> lint_to_uint a = lint_to_uint b \<and> width a = width b"
  apply (transfer)
  using bl_to_bin_inj
  by auto

lemma sint_eq:
  "a = b \<longleftrightarrow> lint_to_sint a = lint_to_sint b \<and> width a = width b"
  apply (transfer)
  apply auto 
  by (metis bl_sbin_bl)

lemma lconst_inj: "lconst w a = lconst w b \<longleftrightarrow> a mod 2^w = b mod 2^w" by auto

subsection \<open>\<open>i1\<close> as Boolean\<close>

definition "ltrue \<equiv> lconst 1 1"
definition "lfalse \<equiv> lconst 1 0"
definition "bool_to_lint b \<equiv> if b then ltrue else lfalse"
definition "lint_to_bool a \<equiv> if a = ltrue then True else if a = lfalse then False else lint_abort_bool ()"

lemma lbool_cases: "width a = 1 \<Longrightarrow> a=ltrue \<or> a=lfalse"
  unfolding ltrue_def lfalse_def 
  apply transfer
  apply auto
  by (metis (full_types) BIT_special_simps(2) bin_bl_bin bin_to_bl_aux.Z bin_to_bl_def bin_to_bl_zero bintrunc.Suc bintrunc_n_0 bl_bin_bl zero_neq_one)

lemma lint_bool_simps[simp]:
  "width ltrue = 1" 
  "width lfalse = 1" 
  "lint_to_uint ltrue = 1"
  "lint_to_uint lfalse = 0"
  "lint_to_sint ltrue = -1"
  "lint_to_sint lfalse = 0"

  "width (bool_to_lint b) = 1"
  "width a = 1 \<Longrightarrow> lint_to_bool a \<longleftrightarrow> a = ltrue"
  "lint_to_bool (bool_to_lint b) = b"
  "width a = 1 \<Longrightarrow> bool_to_lint (lint_to_bool a) = a"
  using lbool_cases
  unfolding ltrue_def lfalse_def bool_to_lint_def lint_to_bool_def
  by (auto)

section \<open>Connection to Word Datatype\<close>

definition lint_to_word :: "lint \<Rightarrow> 'a::len0 word" where "lint_to_word \<equiv> word_of_int o lint_to_uint"
definition word_to_lint :: "'a::len0 word \<Rightarrow> lint" where "word_to_lint \<equiv> lconst (len_of TYPE('a)) o uint"

lemma lint_word_inv[simp]: "lint_to_word (word_to_lint w) = w"
  by (auto simp: word_to_lint_def lint_to_word_def)

lemma word_lint_inv[simp]: "LENGTH ('a::len0) = width i \<Longrightarrow> word_to_lint (lint_to_word i :: 'a word) = i"
  apply (auto simp: word_to_lint_def lint_to_word_def)
  by (metis uint_const uint_eq uint_lower_bound uint_upper_bound width_lconst word_of_int_inverse word_ubin.norm_Rep)
  
lemma bin_to_bl_eq_iff: "bin_to_bl w x = bin_to_bl w y \<longleftrightarrow> bintrunc w x = bintrunc w y"
  by (metis bin_bl_bin bl_bin_bl size_bin_to_bl)
  
named_theorems word_to_lint_convs  
  
lemma word_to_lint_plus[word_to_lint_convs]: "word_to_lint (a+b) = word_to_lint a + word_to_lint b"
  apply (auto simp: word_to_lint_def lint_to_word_def)
  apply transfer
  apply (auto simp: cnv_uop2_def bin_to_bl_eq_iff bintrunc_mod2p mod_add_eq)
  done

lemma word_to_lint_minus[word_to_lint_convs]: "word_to_lint (a-b) = word_to_lint a - word_to_lint b"
  apply (auto simp: word_to_lint_def lint_to_word_def)
  apply transfer
  apply (auto simp: cnv_uop2_def bin_to_bl_eq_iff bintrunc_mod2p mod_diff_eq)
  done
  
lemma word_to_lint_mult[word_to_lint_convs]: "word_to_lint (a*b) = word_to_lint a * word_to_lint b"
  apply (auto simp: word_to_lint_def lint_to_word_def)
  apply transfer
  apply (auto simp: cnv_uop2_def bin_to_bl_eq_iff bintrunc_mod2p mod_mult_eq)
  done
    
lemma word_to_lint_eq[word_to_lint_convs]: "word_to_lint a = word_to_lint b \<longleftrightarrow> a=b"  
  by (auto simp: word_to_lint_def word_uint.Rep_inject)
  
lemma word_to_lint_ule[word_to_lint_convs]: "word_to_lint a \<le> word_to_lint b \<longleftrightarrow> a\<le>b"  
  by (auto simp: word_to_lint_def lint_to_word_def word_le_def)
  
lemma word_to_lint_ult[word_to_lint_convs]: "word_to_lint a < word_to_lint b \<longleftrightarrow> a<b"  
  by (auto simp: word_to_lint_def lint_to_word_def word_less_def)

lemma word_to_lint_sle[word_to_lint_convs]: "word_to_lint a \<le>\<^sub>s word_to_lint b \<longleftrightarrow> a <=s b"  
  by (auto simp: word_to_lint_def lint_to_word_def word_sle_def sint_uint)
  
lemma word_to_lint_slt[word_to_lint_convs]: "word_to_lint a <\<^sub>s word_to_lint b \<longleftrightarrow> a <s b"  
  by (auto simp: word_to_lint_def lint_to_word_def word_sless_alt sint_uint)
  

lemma word_to_lint_div[word_to_lint_convs]: "word_to_lint (a div b) = word_to_lint a div word_to_lint b"
  apply (auto simp: word_to_lint_def lint_to_word_def)
  apply transfer'
  apply (auto simp: cnv_uop2_def bin_to_bl_eq_iff bintrunc_mod2p uint_div_alt)
  done

lemma word_to_lint_mod[word_to_lint_convs]: "word_to_lint (a mod b) = word_to_lint a mod word_to_lint b"
  apply (auto simp: word_to_lint_def lint_to_word_def)
  apply transfer'
  apply (auto simp: cnv_uop2_def bin_to_bl_eq_iff bintrunc_mod2p uint_mod_alt)
  done

lemma word_to_lint_sdiv[word_to_lint_convs]: 
  fixes a b :: "'a::len word"
  assumes "sint a sdiv sint b \<in> sints LENGTH('a)"
  shows "word_to_lint (a sdiv b) = word_to_lint a sdiv word_to_lint b"
  using assms
  apply (auto simp: word_to_lint_def lint_to_word_def sints_def)
  apply transfer'
  by (metis (mono_tags, hide_lams) One_nat_def bl_sbin_bl bl_to_sbin_in_sints cnv_sop2_def 
      len_gt_0 sbin_bl_bin sdiv_word_def sint_sbintrunc' sint_uint size_bin_to_bl)

lemma word_to_lint_smod[word_to_lint_convs]: 
  fixes a b :: "'a::len word"
  assumes "sint a sdiv sint b \<in> sints LENGTH('a)"
  shows "word_to_lint (a smod b) = word_to_lint a smod word_to_lint b"
  using assms
  apply (auto simp: word_to_lint_def lint_to_word_def sints_def)
  apply transfer'
  by (metis (mono_tags) One_nat_def bl_to_sbin_in_sints cnv_sop2_def len_gt_0 sbin_bl_bin sint_uint size_bin_to_bl smod_word_def to_bl_of_bin word_uint.Rep_inverse)
        
  
lemma word_to_lint_shl[word_to_lint_convs]: "word_to_lint ((a::_::len word) << n) = bitSHL (word_to_lint a) n"
  apply (auto simp: word_to_lint_def)
  apply transfer'
  apply (auto simp: cnv_uop1_def bin_to_bl_eq_iff bintrunc_mod2p shiftl_t2n uint_word_ariths algebra_simps)
  by (simp add: mod_mult_right_eq semiring_normalization_rules(7) shiftl_int_def)
  
lemma word_to_lint_lshr[word_to_lint_convs]: "word_to_lint ((a::_::len word) >> n) = bitLSHR (word_to_lint a) n"
  apply (auto simp: word_to_lint_def)
  apply transfer'
  apply (auto simp: cnv_uop1_def bin_to_bl_eq_iff bintrunc_mod2p uint_word_ariths shiftr_div_2n algebra_simps)
  done

lemma word_to_lint_ashr[word_to_lint_convs]: "word_to_lint (a >>> n) = bitASHR (word_to_lint (a::'a::len word)) n"
  unfolding word_to_lint_def
  apply transfer'
  by (auto simp: cnv_sop1_def uint_sint sshiftr_div_2n)
  
lemma word_to_lint_ucast_down[word_to_lint_convs]: "is_down UCAST('a \<rightarrow> 'b) \<Longrightarrow> word_to_lint (UCAST('a::len\<rightarrow>'b::len) a) = trunc (LENGTH('b)) (word_to_lint a)" 
  unfolding word_to_lint_def
  apply transfer'
  apply (auto simp: cast_simps to_bl_ucast simp flip: to_bl_bin)
  by (metis bl_bin_bl bl_trunc_def diff_diff_cancel length_drop word_bl_Rep')
  
lemma word_to_lint_scast_down[word_to_lint_convs]: "is_down SCAST('a \<rightarrow> 'b) \<Longrightarrow> word_to_lint (SCAST('a::len\<rightarrow>'b::len) a) = trunc (LENGTH('b)) (word_to_lint a)" 
  unfolding word_to_lint_def
  apply transfer'
  apply (auto simp: cast_simps to_bl_scast_down simp flip: to_bl_bin)
  by (metis bl_bin_bl bl_trunc_def diff_diff_cancel length_drop word_bl_Rep')
  
(* TODO: Move *)  
lemma zext_in_range: "\<lbrakk>w'\<noteq>0; w'\<le>w; 0\<le>a; a<2^w'\<rbrakk> \<Longrightarrow> zext w (lconst w' a) = lconst w a"  
  apply transfer'
  apply (auto simp: bl_zext_def)
  by (metis bin_bl_bin bintrunc_mod2p bl_bin_bl_rep_drop diff_is_0_eq' diff_zero drop_bin2bl len_bin_to_bl mod_pos_pos_trivial)
  
  
lemma word_to_lint_ucast_up[word_to_lint_convs]: 
  "is_up UCAST('a::len\<rightarrow>'b::len) \<Longrightarrow> word_to_lint (UCAST('a\<rightarrow>'b) a) = zext LENGTH ('b) (word_to_lint a)"
  unfolding word_to_lint_def
  by (simp add: zext_in_range is_up cast_simps)
  
  
lemma word_to_lint_scast_up[word_to_lint_convs]: 
  "is_up SCAST('a::len\<rightarrow>'b::len) \<Longrightarrow> word_to_lint (SCAST('a\<rightarrow>'b) a) = sext LENGTH ('b) (word_to_lint a)"
  unfolding word_to_lint_def
  apply (simp add: is_up sint_eq uint_sint max_def)
  by (simp add: is_up sint_up_scast)
  
lemma word_to_lint_and_simp[word_to_lint_convs]: "word_to_lint (a AND b) = word_to_lint a AND word_to_lint b"  
  apply (auto simp: uint_eq word_to_lint_def)
  apply (simp add: uint_and)
  done
  
lemma word_to_lint_or_simp[word_to_lint_convs]: "word_to_lint (a OR b) = word_to_lint a OR word_to_lint b"  
  apply (auto simp: uint_eq word_to_lint_def)
  apply (simp add: uint_or)
  done
  
lemma word_to_lint_xor_simp[word_to_lint_convs]: "word_to_lint (a XOR b) = word_to_lint a XOR word_to_lint b"  
  apply (auto simp: uint_eq word_to_lint_def)
  apply (simp add: uint_xor)
  done
  
    
(* TODO: Quite arbitrary lemmas! Sort them! *)  
  
  
lemma from_bool_lint_conv: "(from_bool b :: 1 word) = lint_to_word (bool_to_lint b)"
  apply (cases b)
  apply (auto simp: from_bool_def bool_to_lint_def ltrue_def lfalse_def lint_to_word_def)
  done

lemma word_to_lint_to_uint_conv: "lint_to_uint (word_to_lint a) = uint a"  
  by (auto simp: word_to_lint_def)

lemma word_to_lint_to_sint_conv: "lint_to_sint (word_to_lint a) = sint a"  
  by (auto simp: word_to_lint_def sint_uint)
    
lemma word_to_lint_to_uint_0_iff: "(lint_to_uint (word_to_lint b) = 0) = (b = 0)"  
  by (clarsimp simp: word_to_lint_to_uint_conv uint_0_iff)

lemma word_to_lint_to_sint_0_iff: "(lint_to_sint (word_to_lint (b::_::len word)) = 0) = (b = 0)"  
  by (auto simp: word_to_lint_to_sint_conv)
  

    
lemma width_word_to_lint[simp]: "width (word_to_lint (w::'a::len0 word)) = LENGTH ('a)"
  by (auto simp: word_to_lint_def)
  
  
  
  
definition is_up' :: "('a::len0 word \<Rightarrow> 'b::len0 word) \<Rightarrow> bool"
  where "is_up' c \<longleftrightarrow> source_size c < target_size c"

definition is_down' :: "('a::len0 word \<Rightarrow> 'b::len0 word) \<Rightarrow> bool"
  where "is_down' c \<longleftrightarrow> target_size c < source_size c"
  
lemma is_down': "is_down' c \<longleftrightarrow> len_of TYPE('b) < len_of TYPE('a)"
  for c :: "'a::len0 word \<Rightarrow> 'b::len0 word"
  by (simp only: is_down'_def source_size target_size)

lemma is_up': "is_up' c \<longleftrightarrow> len_of TYPE('a) < len_of TYPE('b)"
  for c :: "'a::len0 word \<Rightarrow> 'b::len0 word"
  by (simp only: is_up'_def source_size target_size)

lemmas is_down'_imp[simp, intro] = is_down'[THEN iffD1]  
lemmas is_up'_imp[simp, intro] = is_up'[THEN iffD1]  
  
lemma is_down'_imp_down[simp, intro]: "is_down' c \<Longrightarrow> is_down c" by (auto simp: is_down is_down')
lemma is_up'_imp_up[simp, intro]: "is_up' c \<Longrightarrow> is_up c" by (auto simp: is_up is_up')
  
  
  
  
  
end
