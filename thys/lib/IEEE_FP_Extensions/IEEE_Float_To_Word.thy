section \<open>Convert Floating Point to Word\<close>
theory IEEE_Float_To_Word
imports IEEE_Fp_Add_Basic "../LLVM_More_Word_Lemmas"
begin
  

subsection \<open>Generic Definitions\<close>        
  
  lift_definition word_of_float :: "'l\<^sub>1::len itself \<Rightarrow> ('e,'f) float \<Rightarrow> 'l::len word" is
    "\<lambda>_ (s::1 word, e::'e word, f::'f word). 
      word_cat s (word_cat e f::'l\<^sub>1 word)
    " .
    
  lift_definition float_of_word :: "'l\<^sub>1::len itself \<Rightarrow> 'l::len word \<Rightarrow> ('e,'f)float" is
    "\<lambda>(_::'l\<^sub>1 itself) (x::'l word). apsnd word_split (word_split x::1 word * 'l\<^sub>1 word)" .
    
    
  locale float_conv_word =
    fixes L1 :: "'l\<^sub>1::len itself"
    fixes FoW :: "'l::len word \<Rightarrow> ('e,'f) float"
      and WoF :: "('e,'f) float \<Rightarrow> 'l word"
    assumes LEN: "LENGTH('l) = 1 + LENGTH('e) + LENGTH('f)"
    assumes LEN1: "LENGTH('l) = LENGTH('l\<^sub>1) + 1"
    
    assumes FoW_def: "FoW = float_of_word TYPE('l\<^sub>1)"
    assumes WoF_def: "WoF = word_of_float TYPE('l\<^sub>1)"
    
  begin
  
    lemma LEN1': "LENGTH('l\<^sub>1) = LENGTH('e) + LENGTH('f)"
      using LEN LEN1 by linarith
  
    lemma float_of_word_inverse[simp]: 
      "WoF (FoW a) = a"
      unfolding WoF_def FoW_def
      apply transfer
      apply (auto 
        simp: apsnd_def map_prod_def LEN1' LEN word_size
        split: prod.splits
        dest!: word_cat_split_alt[rotated]
        )
      done
      
    lemma word_of_float_inj_iff[simp]: 
      "WoF r = WoF s \<longleftrightarrow> r = s"
      unfolding WoF_def FoW_def
      apply transfer
      by (auto simp: word_cat_inj LEN LEN1')
    
    lemma word_of_float_inverse[simp]: 
      "FoW (WoF a) = a"
      using word_of_float_inj_iff float_of_word_inverse by blast
      
    lemma float_of_zero[simp]: "FoW 0 = 0"  
      unfolding FoW_def
      apply transfer'
      by (simp)
      
    lemma zero_of_float[simp]: "WoF 0 = 0"  
      unfolding WoF_def
      apply transfer'
      by (simp)
      
      
      
  end    
     
subsection \<open>Standard Float Sizes\<close>  
  
  type_synonym "float32" = "(8,23) float"
  type_synonym "float64" = "(11,52) float"

  definition fp32_of_float :: "float32 \<Rightarrow> 32 word" where "fp32_of_float \<equiv> word_of_float TYPE(31)"
  definition float_of_fp32 :: "32 word \<Rightarrow> float32" where "float_of_fp32 \<equiv> float_of_word TYPE(31)"
  
  definition fp64_of_float :: "float64 \<Rightarrow> 64 word" where "fp64_of_float \<equiv> word_of_float TYPE(63)"
  definition float_of_fp64 :: "64 word \<Rightarrow> float64" where "float_of_fp64 \<equiv> float_of_word TYPE(63)"

  interpretation FP32: float_conv_word "TYPE(31)" float_of_fp32 fp32_of_float
    apply unfold_locales
    unfolding float_of_fp32_def fp32_of_float_def
    by auto
  
  interpretation FP64: float_conv_word "TYPE(63)" float_of_fp64 fp64_of_float
    apply unfold_locales
    unfolding float_of_fp64_def fp64_of_float_def
    by auto



end
