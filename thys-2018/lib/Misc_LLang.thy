theory Misc_LLang
imports
  "Automatic_Refinement.Misc"
begin

  (* TODO: Move *)  
  lemma map_le_empty_iff[simp]: "m \<subseteq>\<^sub>m Map.empty \<longleftrightarrow> m=Map.empty"
    using map_le_antisym by fastforce  
    
  (* TODO: Move *)  
  lemma set_minus_minus_disj_conv: "A\<inter>R={} \<Longrightarrow> A - (B - R) = A - B" by auto

  (* TODO: Move *)  
  lemma ndomIff: "i\<notin>dom m \<longleftrightarrow> m i = None" by auto
  
  lemma nat_minus1_less_if_neZ[simp]: "a - Suc 0 < a \<longleftrightarrow> a\<noteq>0" by auto  


end
