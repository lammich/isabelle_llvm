section \<open>Additions to Word-Lemmas\<close>
text \<open>Some additions to Word-Lemmas, without pulling in Word-Sumo thy\<close>
theory LLVM_More_Word_Lemmas
imports "Word_Lib.Word_Lemmas"
begin
  
subsection \<open>Len-2 Typeclass\<close>
text \<open>Typeclass for length at least two, as frequently required for many useful word applications,
  like signed integers, or floating point numbers. This moves side-conditions like \<open>1<LENGTH(_)\<close> into
  the type system.\<close>
    
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

subsection \<open>Additions to Semiring-Bits\<close>

context
  includes bit_operations_syntax
begin
  
  lemma word_cat_eq_shift_plus: "(word_cat (a::'a::len word) (b::'b::len word) :: 'c::len word) 
    = (UCAST ('a\<rightarrow>'c) a << LENGTH('b)) + UCAST ('b\<rightarrow>'c) b"
    unfolding word_cat_eq shiftl_def 
    by simp
    
  lemma "(word_split (w::'a::len word) :: 'b::len word \<times> 'c::len word ) 
    = (ucast ( w >> LENGTH('c) ), ucast w )"  
    by (simp add: shiftr_def word_split_def)
    
  (* TODO: More general than thm Word.word_mod_2p_is_mask *)
  lemma mod_2p_is_mask: "a mod 2^w = and a (mask w)" for a :: "_::semiring_bits"
    by (metis take_bit_eq_mask take_bit_eq_mod) 
    
  (* TODO: More general than thm Word.shiftl_t2n *)
  lemma shiftl_t2n': "w<<n = 2 ^ n * w" for w :: "_::semiring_bits"
    by (simp add: shiftl_def push_bit_eq_mult algebra_simps)
    
  (* TODO: More general than thm Word_Lemmas.word_shiftl_add_distrib *)
  lemma word_shiftl_add_distrib':
    fixes x :: "'a :: semiring_bit_operations"
    shows "(x + y) << n = (x << n) + (y << n)"
    by (simp add: shiftl_t2n' ring_distribs)
  
  lemma bit_select_cases:
    fixes n
    assumes "i'=i+1"
    obtains "and (n) (mask i') >> i = 0" | "and (n) (mask i') >> i = 1"
    apply (cases "bit n 31")
    apply (force intro: that intro: bit_eqI simp: bit_simps assms)+
    done
  
  lemma t2n_shiftl_conv:  
    "2 ^ n * w = w<<n" 
    "w * 2 ^ n = w<<n" 
    for w :: "_::semiring_bit_operations"
    by (simp_all add: shiftl_t2n' algebra_simps)
  
  lemma mask_shift_mask_simp: "b+c\<le>a \<Longrightarrow> and (and w (mask a) >> b) (mask c) = and (w>>b) (mask c)" for w :: "_::semiring_bits"
    by (simp flip: mod_2p_is_mask add: shiftr_eq_div div_exp_mod_exp_eq mod_exp_eq)
  
  lemma and_and_mask_simp[simp]: "and (and a (mask n)) (mask m) = and a (mask (min n m))" for a :: "_::semiring_bits"
    by (simp flip: mod_2p_is_mask add: power_mod_div mod_exp_eq)

    
end  

subsection \<open>Word Split and Cat\<close>
lemma word_split_0[simp]: "word_split 0 = (0,0)"  
  by (simp add: word_split_def)
  
lemma word_cat_0[simp]: "word_cat 0 0 = 0"
  by (simp add: word_cat_eq_shift_plus)

subsection \<open>Unsigned Integer of Word\<close>

definition "integer_of_word \<equiv> integer_of_nat o unat"
definition "word_of_integer \<equiv> of_nat o nat_of_integer"
  
lemma word_of_int_of_word[simp]: "word_of_integer (integer_of_word x) = x"
  unfolding integer_of_word_def word_of_integer_def
  by simp

context
  includes integer.lifting
begin  
  lemma nat_of_integer_mod_distrib:
    "x\<ge>0 \<Longrightarrow> nat_of_integer (x mod 2^n) = nat_of_integer x mod 2^n"  
    apply transfer
    by (simp add: nat_mod_distrib nat_power_eq)
    
  lemma integer_of_nat_nat_of_integer[simp]:
    "x\<ge>0 \<Longrightarrow> integer_of_nat (nat_of_integer x) = x"  
    apply transfer
    by simp

  lemma of_nat_shiftl_eq: "of_nat (a << n) = (of_nat a) << n" 
    by (simp add: push_bit_eq_mult shiftl_def)
    
    
end    
        
lemma int_of_word_of_int[simp]: "0\<le>x \<Longrightarrow> x<2^LENGTH('l) \<Longrightarrow> integer_of_word (word_of_integer x :: 'l::len word) = x"
  unfolding integer_of_word_def word_of_integer_def
  apply (auto simp: unat_of_nat integer_of_nat_eq_of_nat simp flip: nat_of_integer_mod_distrib)
  by (metis max.absorb2 nat_mod_eq' nat_of_integer_mod_distrib of_nat_less_iff of_nat_numeral of_nat_of_integer semiring_1_class.of_nat_power)
    

lemma integer_of_word_bounds[simp]:
  "0\<le>integer_of_word w" 
  "integer_of_word w < 2^LENGTH('l)"  for w :: "'l::len word"
  unfolding integer_of_word_def 
  apply (auto simp: integer_of_nat_eq_of_nat)
  apply (metis Word.of_nat_unat of_nat_0_le_iff)
  by (metis Word.of_nat_unat of_nat_less_iff of_nat_numeral semiring_1_class.of_nat_power unsigned_less)







end
