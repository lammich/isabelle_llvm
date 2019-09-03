(* Author: Mathias Fleury
   Minor additions by Peter Lammich
*)
theory Bits_Natural
  imports "HOL-Word.Word"
begin

(* TODO: Move *)
lemma bin_trunc_xor':
  "bintrunc n x XOR bintrunc n y = bintrunc n (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma uint_xor: "uint (x XOR y) = uint x XOR uint y"
  by (transfer, simp add: bin_trunc_xor')



instantiation nat :: bit_comprehension
begin

definition test_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  "test_bit i j = test_bit (int i) j"

definition lsb_nat :: \<open>nat \<Rightarrow> bool\<close> where
  "lsb i = (int i :: int) !! 0"

definition set_bit_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat" where
  "set_bit i n b = nat (bin_sc n b (int i))"

definition set_bits_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "set_bits f =
  (if \<exists>n. \<forall>n'\<ge>n. \<not> f n' then
     let n = LEAST n. \<forall>n'\<ge>n. \<not> f n'
     in nat (bl_to_bin (rev (map f [0..<n])))
   else if \<exists>n. \<forall>n'\<ge>n. f n' then
     let n = LEAST n. \<forall>n'\<ge>n. f n'
     in nat (sbintrunc n (bl_to_bin (True # rev (map f [0..<n]))))
   else 0 :: nat)"

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

instance ..

end


lemma nat_shiftr[simp]:
  "m >> 0 = m"
  \<open>((0::nat) >> m) = 0\<close>
  \<open>(m >> Suc n) = (m div 2 >> n)\<close> for m :: nat
  by (auto simp: shiftr_nat_def zdiv_int zdiv_zmult2_eq[symmetric])

lemma nat_shifl_div: \<open>m >> n = m div (2^n)\<close> for m :: nat
  by (induction n arbitrary: m) (auto simp: div_mult2_eq)

lemma nat_shiftl[simp]:
  "m << 0 = m"
  \<open>((0::nat) << m) = 0\<close>
  \<open>(m << Suc n) = ((m * 2) << n)\<close> for m :: nat
  by (auto simp: shiftl_nat_def zdiv_int zdiv_zmult2_eq[symmetric])

lemma nat_shiftr_div2: \<open>m >> 1 = m div 2\<close> for m :: nat
  by auto

lemma nat_shiftr_div: \<open>m << n = m * (2^n)\<close> for m :: nat
  by (induction n arbitrary: m) (auto simp: div_mult2_eq)

definition shiftl1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>shiftl1 n = n << 1\<close>

definition shiftr1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>shiftr1 n = n >> 1\<close>

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

end

instance ..
end


lemma bitXOR_1_if_mod_2: \<open>bitXOR L 1 = (if L mod 2 = 0 then L + 1 else L - 1)\<close> for L :: nat
  apply transfer
  apply (subst int_int_eq[symmetric])
  apply (rule bin_rl_eqI)
   apply (auto simp: bitXOR_nat_def)
  unfolding bin_rest_def bin_last_def bitXOR_nat_def
       apply presburger+
  done

lemma bitAND_1_mod_2: \<open>bitAND L 1 = L mod 2\<close> for L :: nat
  apply transfer
  apply (subst int_int_eq[symmetric])
  apply (subst bitAND_nat_def)
  by (auto simp: zmod_int bin_rest_def bin_last_def bitval_bin_last[symmetric])


lemma nat_set_bit_0: \<open>set_bit x 0 b = nat ((bin_rest (int x)) BIT b)\<close> for x :: nat
  by (auto simp: set_bit_nat_def)

lemma nat_test_bit0_iff: \<open>n !! 0 \<longleftrightarrow> n mod 2 = 1\<close> for n :: nat
proof -
  have 2: \<open>2 = int 2\<close>
    by auto
  have [simp]: \<open>int n mod 2 = 1 \<longleftrightarrow> n mod 2 = Suc 0\<close>
    unfolding 2 zmod_int[symmetric]
    by auto

  show ?thesis
    unfolding test_bit_nat_def
    by (auto simp: bin_last_def zmod_int)
qed
lemma test_bit_2: \<open>m > 0 \<Longrightarrow> (2*n) !! m \<longleftrightarrow> n !! (m - 1)\<close> for n :: nat
  by (cases m)
    (auto simp: test_bit_nat_def bin_rest_def)

lemma test_bit_Suc_2: \<open>m > 0 \<Longrightarrow> Suc (2 * n) !! m \<longleftrightarrow> (2 * n) !! m\<close> for n :: nat
  by (cases m)
    (auto simp: test_bit_nat_def bin_rest_def)

lemma bin_rest_prev_eq:
  assumes [simp]: \<open>m > 0\<close>
  shows  \<open>nat ((bin_rest (int w))) !! (m - Suc (0::nat)) = w !! m\<close>
proof -
  define m' where \<open>m' = w div 2\<close>
  have w: \<open>w = 2 * m' \<or> w = Suc (2 * m')\<close>
    unfolding m'_def
    by auto
  moreover have \<open>bin_nth (int m') (m - Suc 0) = m' !! (m - Suc 0)\<close>
    unfolding test_bit_nat_def test_bit_int_def ..
  ultimately show ?thesis
    by (auto simp: bin_rest_def test_bit_2 test_bit_Suc_2)
qed

lemma bin_sc_ge0: \<open>w >= 0 ==> (0::int) \<le> bin_sc n b w\<close>
  by (induction n arbitrary: w) auto

lemma bin_to_bl_eq_nat:
  \<open>bin_to_bl (size a) (int a) = bin_to_bl (size b) (int b) ==> a=b\<close>
  by (metis Nat.size_nat_def size_bin_to_bl)

lemma nat_bin_nth_bl: "n < m \<Longrightarrow> w !! n = nth (rev (bin_to_bl m (int w))) n" for w :: nat
  apply (induct n arbitrary: m w)
  subgoal for m w
    apply clarsimp
    apply (case_tac m, clarsimp)
    using bin_nth_bl bin_to_bl_def test_bit_int_def test_bit_nat_def apply presburger
    done
  subgoal for n m w
    apply (clarsimp simp: bin_to_bl_def)
    apply (case_tac m, clarsimp)
    apply (clarsimp simp: bin_to_bl_def)
    apply (subst bin_to_bl_aux_alt)
    apply (simp add: bin_nth_bl test_bit_nat_def)
    done
  done

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
    by (auto simp: bin_rest_def)
qed

lemma test_bit_nat_outside: "n > size w \<Longrightarrow> \<not>w !! n" for w :: nat
  unfolding test_bit_nat_def
  by (auto simp: bin_nth_ge_size)

lemma nat_bin_nth_bl':
  \<open>a !! n \<longleftrightarrow> (n < size a \<and> (rev (bin_to_bl (size a) (int a)) ! n))\<close>
  by (metis (full_types) Nat.size_nat_def bin_nth_ge_size leI nat_bin_nth_bl nat_int
      of_nat_less_0_iff test_bit_int_def test_bit_nat_def)

lemma nat_set_bit_test_bit: \<open>set_bit w n x !! m = (if m = n then x else w !! m)\<close> for w n :: nat
  unfolding nat_bin_nth_bl'
  apply auto
        apply (metis bin_nth_bl bin_nth_sc bin_nth_simps(3) bin_to_bl_def int_nat_eq set_bit_nat_def)
       apply (metis bin_nth_ge_size bin_nth_sc bin_sc_ge0 leI of_nat_less_0_iff set_bit_nat_def)
      apply (metis bin_nth_bl bin_nth_ge_size bin_nth_sc bin_sc_ge0 bin_to_bl_def int_nat_eq leI
      of_nat_less_0_iff set_bit_nat_def)
     apply (metis Nat.size_nat_def bin_nth_sc_gen bin_nth_simps(3) bin_to_bl_def int_nat_eq
      nat_bin_nth_bl' set_bit_nat_def test_bit_int_def test_bit_nat_def)
    apply (metis Nat.size_nat_def bin_nth_bl bin_nth_sc_gen bin_to_bl_def int_nat_eq nat_bin_nth_bl
      nat_bin_nth_bl' of_nat_less_0_iff of_nat_less_iff set_bit_nat_def)
   apply (metis (full_types) bin_nth_bl bin_nth_ge_size bin_nth_sc_gen bin_sc_ge0 bin_to_bl_def leI of_nat_less_0_iff set_bit_nat_def)
  by (metis bin_nth_bl bin_nth_ge_size bin_nth_sc_gen bin_sc_ge0 bin_to_bl_def int_nat_eq leI of_nat_less_0_iff set_bit_nat_def)

  
  
lemma unat_or: "unat (x OR y) = unat x OR unat y"
  unfolding unat_def
  by (simp add: uint_or bitOR_nat_def)

lemma unat_and: "unat (x AND y) = unat x AND unat y"
  unfolding unat_def
  by (simp add: uint_and bitAND_nat_def)
  
lemma unat_xor: "unat (x XOR y) = unat x XOR unat y"
  unfolding unat_def
  by (simp add: uint_xor bitXOR_nat_def)
  
  
  
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
  by (auto simp: bitAND_nat_def Bit_def nat_add_distrib)
  
  
  
lemma nat_and_comm: "a AND b = b AND a" for a b :: nat
  unfolding bitAND_nat_def by (auto simp: int_and_comm)

lemma AND_upper_nat1: "a AND b \<le> a" for a b :: nat
proof -
  have "int a AND int b \<le> int a"
    by (rule AND_upper1) simp
  thus ?thesis unfolding bitAND_nat_def by linarith
qed    

lemma AND_upper_nat2: "a AND b \<le> b" for a b :: nat
  using AND_upper_nat1[of b a] by (simp add: nat_and_comm)
  
lemmas AND_upper_nat1' [simp] = order_trans [OF AND_upper_nat1]
lemmas AND_upper_nat1'' [simp] = order_le_less_trans [OF AND_upper_nat1]
  
lemmas AND_upper_nat2' [simp] = order_trans [OF AND_upper_nat2]
lemmas AND_upper_nat2'' [simp] = order_le_less_trans [OF AND_upper_nat2]
  

  
  
  
  
  
  
  
  
end
