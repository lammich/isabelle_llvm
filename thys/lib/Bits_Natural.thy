(* Author: Mathias Fleury
   Minor additions by Peter Lammich
*)
theory Bits_Natural
  imports "HOL-Library.Word" Word_Lib.Aligned "Word_Lib.Word_Lib_Sumo"
begin

(* TODO: Move *)
lemma bin_trunc_xor':
  "bintrunc n x XOR bintrunc n y = bintrunc n (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

(*lemma uint_xor: "uint (x XOR y) = uint x XOR uint y"
  by (transfer, simp add: bin_trunc_xor')*)



instance nat :: semiring_bit_syntax ..

instantiation nat :: set_bit begin
  definition set_bit_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat" where
    "set_bit i n b = nat (bin_sc n b (int i))"

instance 
  apply standard
  apply (simp_all add: set_bit_nat_def)
  by (metis bin_nth_sc_gen bin_sign_sc bit_nat_iff bit_of_nat_iff_bit of_nat_0_le_iff sign_Pls_ge_0)
end  

instantiation nat :: msb
begin
  definition msb_nat :: "nat \<Rightarrow> bool" where
    "msb i = msb (int i)"

instance ..
end


(*
instantiation nat :: semiring_bit_shifts
begin

definition set_bits_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "set_bits f =
  (if \<exists>n. \<forall>n'\<ge>n. \<not> f n' then
     let n = LEAST n. \<forall>n'\<ge>n. \<not> f n'
     in nat (bl_to_bin (rev (map f [0..<n])))
   else if \<exists>n. \<forall>n'\<ge>n. f n' then
     let n = LEAST n. \<forall>n'\<ge>n. f n'
     in nat (sbintrunc n (bl_to_bin (True # rev (map f [0..<n]))))
   else 0 :: nat)"


definition not_nat :: "nat \<Rightarrow> nat" where
  "NOT i = nat (NOT (int i))"

(*
definition shiftl_nat where
  "shiftl x n = nat ((int x) * 2 ^ n)"

definition shiftr_nat where
  "shiftr x n = nat (int x div 2 ^ n)"

definition bitNOT_nat :: "nat \<Rightarrow> nat" where
  "bitNOT i = nat (bitNOT (int i))"

definition bitAND_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitAND i j = nat (bitAND (int i) (int j))"

definition bitOR_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitOR i j = nat (bitOR (int i) (int j))"

definition bitXOR_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitXOR i j = nat (bitXOR (int i) (int j))"

definition msb_nat :: "nat \<Rightarrow> bool" where
  "msb i = msb (int i)"
*)
instance . .

end
*)

lemma nat_shiftr[simp]:
  "m >> 0 = m"
  \<open>((0::nat) >> m) = 0\<close>
  \<open>(m >> Suc n) = (m div 2 >> n)\<close> for m :: nat
  by (simp_all add: shiftr_eq_drop_bit drop_bit_Suc)

lemma nat_shifl_div: \<open>m >> n = m div (2^n)\<close> for m :: nat
  by (induction n arbitrary: m) (auto simp: div_mult2_eq)

lemma nat_shiftl[simp]:
  "m << 0 = m"
  \<open>((0) << m) = 0\<close>
  \<open>(m << Suc n) = ((m * 2) << n)\<close> for m :: nat
  by (simp_all add: shiftl_eq_push_bit)

lemma nat_shiftr_div2: \<open>m >> 1 = m div 2\<close> for m :: nat
  by auto

lemma nat_shiftr_div: \<open>m << n = m * (2^n)\<close> for m :: nat
  by (induction n arbitrary: m) (auto simp: div_mult2_eq)

definition shiftl1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>shiftl1 n = n << 1\<close>

definition shiftr1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>shiftr1 n = n >> 1\<close>

(*
instantiation natural :: bit_comprehension
begin

context includes natural.lifting begin

lift_definition test_bit_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> bool\<close> is test_bit .

lift_definition lsb_natural :: \<open>natural \<Rightarrow> bool\<close> is lsb .

lift_definition set_bit_natural :: "natural \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> natural" is
  set_bit .

lift_definition set_bits_natural :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> natural\<close>
  is \<open>set_bits :: (nat \<Rightarrow> bool) \<Rightarrow> nat\<close> .

lift_definition shiftl_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> natural\<close>
  is \<open>shiftl :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition shiftr_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> natural\<close>
  is \<open>shiftr :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition bitNOT_natural :: \<open>natural \<Rightarrow> natural\<close>
  is \<open>bitNOT :: nat \<Rightarrow> nat\<close> .

lift_definition bitAND_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>bitAND :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition bitOR_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>bitOR :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition bitXOR_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>bitXOR :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition msb_natural :: \<open>natural \<Rightarrow> bool\<close>
  is \<open>msb :: nat \<Rightarrow> bool\<close> .

end

instance ..
end
*)

lemma bitXOR_1_if_mod_2: \<open> L XOR 1 = (if L mod 2 = 0 then L + 1 else L - 1)\<close> for L :: nat
  apply transfer
  apply (subst int_int_eq[symmetric])
  apply (rule bin_rl_eqI)
   apply (auto simp: xor_nat_def)
  unfolding bin_last_def xor_nat_def
       apply presburger+
  done

lemma bitAND_1_mod_2: \<open>L AND 1 = L mod 2\<close> for L :: nat by auto

lemma nat_set_bit_0: \<open>set_bit x 0 b = nat ((bin_rest (int x)) BIT b)\<close> for x :: nat
  by (auto simp: set_bit_nat_def Bit_def) 

lemma nat_test_bit0_iff: \<open>n !! 0 \<longleftrightarrow> n mod 2 = 1\<close> for n :: nat
proof -
  have 2: \<open>2 = int 2\<close>
    by auto
  have [simp]: \<open>int n mod 2 = 1 \<longleftrightarrow> n mod 2 = Suc 0\<close>
    unfolding 2 zmod_int[symmetric]
    by auto

  show ?thesis
    unfolding test_bit_eq_bit
    by (auto simp: bin_last_def zmod_int bit_nat_def odd_iff_mod_2_eq_one)
    
qed

lemma test_bit_2: \<open>m > 0 \<Longrightarrow> (2*n) !! m \<longleftrightarrow> n !! (m - 1)\<close> for n :: nat
  by (cases m)
    (auto simp: test_bit_eq_bit bit_nat_def)

lemma test_bit_Suc_2: \<open>m > 0 \<Longrightarrow> Suc (2 * n) !! m \<longleftrightarrow> (2 * n) !! m\<close> for n :: nat
  apply (cases m)
  by (auto simp: test_bit_eq_bit bit_nat_def div_mult2_eq)

lemma bin_rest_prev_eq:
  assumes [simp]: \<open>m > 0\<close>
  shows  \<open>nat ((bin_rest (int w))) !! (m - Suc (0::nat)) = w !! m\<close>
proof -
  define m' where \<open>m' = w div 2\<close>
  have w: \<open>w = 2 * m' \<or> w = Suc (2 * m')\<close>
    unfolding m'_def
    by auto
  moreover have \<open>bin_nth (int m') (m - Suc 0) = m' !! (m - Suc 0)\<close>
    by (simp add: bit_of_nat_iff_bit test_bit_eq_bit)
  ultimately show ?thesis
    by (auto simp: test_bit_2 test_bit_Suc_2)
qed

lemma bin_sc_ge0: \<open>w >= 0 ==> (0::int) \<le> bin_sc n b w\<close>
  by (induction n arbitrary: w) auto

lemma bin_to_bl_eq_nat:
  \<open>bin_to_bl (size a) (int a) = bin_to_bl (size b) (int b) ==> a=b\<close>
  by (metis Nat.size_nat_def size_bin_to_bl)

lemma nat_bin_nth_bl: "n < m \<Longrightarrow> w !! n = nth (rev (bin_to_bl m (int w))) n" for w :: nat
  by (metis bin_nth_bl bit_of_nat_iff_bit test_bit_eq_bit)

lemma bin_nth_ge_size: \<open>nat na \<le> n \<Longrightarrow> 0 \<le> na \<Longrightarrow> bin_nth na n = False\<close>
proof (induction \<open>n\<close> arbitrary: na)
  case 0
  then show ?case by auto
next
  case (Suc n na) note IH = this(1) and H = this(2-)
  have \<open>na = 1 \<or> 0 \<le> na div 2\<close>
    using H by auto
  moreover have
    \<open>na = 0 \<or> na = 1 \<or> nat (na div 2) \<le> n\<close>
    using H by auto
  ultimately show ?case
    using IH[rule_format,  of \<open>bin_rest na\<close>] H
    by (auto simp: bit_Suc)
qed

lemma test_bit_nat_outside: "n > size w \<Longrightarrow> \<not>w !! n" for w :: nat
  unfolding test_bit_eq_bit bit_nat_def
  by (metis Nat.size_nat_def div_less even_zero le_eq_less_or_eq le_less_trans n_less_equal_power_2)

lemma nat_bin_nth_bl':
  \<open>a !! n \<longleftrightarrow> (n < size a \<and> (rev (bin_to_bl (size a) (int a)) ! n))\<close>
  by (metis Nat.size_nat_def bit_nat_def div_less even_zero n_less_equal_power_2 nat_bin_nth_bl not_less_iff_gr_or_eq test_bit_eq_bit test_bit_nat_outside)

lemma nat_set_bit_test_bit: \<open>set_bit w n x !! m = (if m = n then x else w !! m)\<close> for w n :: nat
  unfolding nat_bin_nth_bl'
  apply auto
        apply (metis bin_nth_bl bin_nth_sc bin_nth_simps(3) bin_to_bl_def int_nat_eq set_bit_nat_def)
       apply (metis bin_nth_ge_size bin_nth_sc bin_sc_ge0 leI of_nat_less_0_iff set_bit_nat_def)
      apply (metis bin_nth_bl bin_nth_ge_size bin_nth_sc bin_sc_ge0 bin_to_bl_def int_nat_eq leI
      of_nat_less_0_iff set_bit_nat_def)
  apply (metis Nat.size_nat_def bin_to_bl_def nat_bin_nth_bl' set_bit_class.bit_set_bit_iff test_bit_eq_bit)
    apply (metis Nat.size_nat_def bin_nth_bl bin_nth_sc_gen bin_to_bl_def int_nat_eq nat_bin_nth_bl
      nat_bin_nth_bl' of_nat_less_0_iff of_nat_less_iff set_bit_nat_def)
   apply (metis (full_types) bin_nth_bl bin_nth_ge_size bin_nth_sc_gen bin_sc_ge0 bin_to_bl_def leI of_nat_less_0_iff set_bit_nat_def)
  by (metis bin_nth_bl bin_nth_ge_size bin_nth_sc_gen bin_sc_ge0 bin_to_bl_def int_nat_eq leI of_nat_less_0_iff set_bit_nat_def)

  
  
lemma unat_or: "unat (x OR y) = unat x OR unat y" by (rule unsigned_or_eq)

lemma unat_and: "unat (x AND y) = unat x AND unat y" by (rule unsigned_and_eq)
  
lemma unat_xor: "unat (x XOR y) = unat x XOR unat y" by (rule unsigned_xor_eq)
  
  
(* TODO: Add OR-numerals, XOR-numerals! *)  
  
lemma nat_and_numerals [simp]:
  "(numeral (Num.Bit0 x) :: nat) AND (numeral (Num.Bit0 y) :: nat) = (2 :: nat) * (numeral x AND numeral y)"
  "numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (2 :: nat) * (numeral x AND numeral y)"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (2 :: nat) * (numeral x AND numeral y)"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (2 :: nat) * (numeral x AND numeral y)+1"
  "0 AND n = 0"
  "n AND 0 = 0"
  "(1::nat) AND numeral (Num.Bit0 y) = 0"
  "(1::nat) AND numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (1::nat) = 0"
  "numeral (Num.Bit1 x) AND (1::nat) = 1"
  "(Suc 0::nat) AND numeral (Num.Bit0 y) = 0"
  "(Suc 0::nat) AND numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (Suc 0::nat) = 0"
  "numeral (Num.Bit1 x) AND (Suc 0::nat) = 1"
  "Suc 0 AND Suc 0 = 1"
  for n::nat
  by (auto simp: and_nat_def Bit_def nat_add_distrib)
  
  
  
lemma nat_and_comm: "a AND b = b AND a" for a b :: nat
  unfolding and_nat_def by (auto simp: int_and_comm)

lemma AND_upper_nat1: "a AND b \<le> a" for a b :: nat
proof -
  have "int a AND int b \<le> int a"
    by (rule AND_upper1) simp
  thus ?thesis unfolding and_nat_def by linarith
qed    

lemma AND_upper_nat2: "a AND b \<le> b" for a b :: nat
  using AND_upper_nat1[of b a] by (simp add: nat_and_comm)
  
lemmas AND_upper_nat1' [simp] = order_trans [OF AND_upper_nat1]
lemmas AND_upper_nat1'' [simp] = order_le_less_trans [OF AND_upper_nat1]
  
lemmas AND_upper_nat2' [simp] = order_trans [OF AND_upper_nat2]
lemmas AND_upper_nat2'' [simp] = order_le_less_trans [OF AND_upper_nat2]


lemma msb_shiftr_nat [simp]: "msb ((x :: nat) >> r) \<longleftrightarrow> msb x"
  by (simp add: msb_int_def msb_nat_def)

lemma bintrunc_le: \<open>a \<ge> 0 \<Longrightarrow> a < b \<Longrightarrow> bintrunc n a < b\<close>
  by (smt bintr_lt2p bintrunc_mod2p mod_pos_pos_trivial)


lemma msb_shiftr_word [simp]: "r < LENGTH('a) \<Longrightarrow> msb ((x :: 'a :: {len} word) >> r) \<longleftrightarrow> ((r = 0 \<and> msb x))"
  apply (cases r)
  apply (auto simp: bl_shiftr word_size msb_word_def 
    simp flip: sint_uint[unfolded One_nat_def] hd_bl_sign_sint)
  done

lemma msb_shiftl_word [simp]: "r < LENGTH('a)  \<Longrightarrow> x << r < 2 ^ (LENGTH('a) - Suc 0) \<Longrightarrow>
     msb ((x :: 'a :: {len} word) << r) = (r = 0 \<and> msb x)"
  using less_is_drop_replicate[of \<open>x << r\<close> \<open>(LENGTH('a) - Suc 0)\<close>]
  apply (cases r)
  apply (auto simp: bl_shiftl word_size msb_word_def 
    simp flip: sint_uint[unfolded One_nat_def] hd_bl_sign_sint)
  done

end
