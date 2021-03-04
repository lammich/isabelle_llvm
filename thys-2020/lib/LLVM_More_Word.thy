section \<open>Entry-Point to Word Library and additional lemmas for Isabelle-LLVM\<close>
theory LLVM_More_Word
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



end
