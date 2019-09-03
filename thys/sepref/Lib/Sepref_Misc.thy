theory Sepref_Misc
imports 
  "../Refine_Monadic_Add"
  PO_Normalizer
  "List-Index.List_Index"
  "Refine_Imperative_HOL.Named_Theorems_Rev"
  "HOL-Eisbach.Eisbach"
begin

  hide_const (open) CONSTRAINT

  
  ML \<open>
    fun SIMPLE_METHOD_NOPARAM' tac = Scan.succeed (fn ctxt => SIMPLE_METHOD' (IF_EXGOAL (tac ctxt)))
    fun SIMPLE_METHOD_NOPARAM tac = Scan.succeed (fn ctxt => SIMPLE_METHOD (tac ctxt))
  \<close>
  
  
  lemma not_None_eq2[simp]: "None \<noteq> x \<longleftrightarrow> (\<exists>y. x = Some y)"
    by (cases x) auto
  
  (* Additions for List_Index *)  
  lemma index_of_last_distinct[simp]: 
    "distinct l \<Longrightarrow> index l (last l) = length l - 1"  
    apply (cases l rule: rev_cases)
    apply (auto simp: index_append)
    done

  lemma index_eqlen_conv[simp]: "index l x = length l \<longleftrightarrow> x\<notin>set l"
    by (auto simp: index_size_conv)


  subsection \<open>Iterated Curry and Uncurry\<close>    


  text \<open>Uncurry0\<close>  
  definition "uncurry0 c \<equiv> \<lambda>_::unit. c"
  definition curry0 :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a" where "curry0 f = f ()"
  lemma uncurry0_apply[simp]: "uncurry0 c x = c" by (simp add: uncurry0_def)

  lemma curry_uncurry0_id[simp]: "curry0 (uncurry0 f) = f" by (simp add: curry0_def)
  lemma uncurry_curry0_id[simp]: "uncurry0 (curry0 g) = g" by (auto simp: curry0_def)
  lemma param_uncurry0[param]: "(uncurry0,uncurry0) \<in> A \<rightarrow> (unit_rel\<rightarrow>A)" by auto
    
  text \<open>Abbreviations for higher-order uncurries\<close>    
  abbreviation "uncurry2 f \<equiv> uncurry (uncurry f)"
  abbreviation "curry2 f \<equiv> curry (curry f)"
  abbreviation "uncurry3 f \<equiv> uncurry (uncurry2 f)"
  abbreviation "curry3 f \<equiv> curry (curry2 f)"
  abbreviation "uncurry4 f \<equiv> uncurry (uncurry3 f)"
  abbreviation "curry4 f \<equiv> curry (curry3 f)"
  abbreviation "uncurry5 f \<equiv> uncurry (uncurry4 f)"
  abbreviation "curry5 f \<equiv> curry (curry4 f)"
  abbreviation "uncurry6 f \<equiv> uncurry (uncurry5 f)"
  abbreviation "curry6 f \<equiv> curry (curry5 f)"
  abbreviation "uncurry7 f \<equiv> uncurry (uncurry6 f)"
  abbreviation "curry7 f \<equiv> curry (curry6 f)"
  abbreviation "uncurry8 f \<equiv> uncurry (uncurry7 f)"
  abbreviation "curry8 f \<equiv> curry (curry7 f)"
  abbreviation "uncurry9 f \<equiv> uncurry (uncurry8 f)"
  abbreviation "curry9 f \<equiv> curry (curry8 f)"
  abbreviation "uncurry10 f \<equiv> uncurry (uncurry9 f)"
  abbreviation "curry10 f \<equiv> curry (curry9 f)"
  abbreviation "uncurry11 f \<equiv> uncurry (uncurry10 f)"
  abbreviation "curry11 f \<equiv> curry (curry10 f)"
  abbreviation "uncurry12 f \<equiv> uncurry (uncurry11 f)"
  abbreviation "curry12 f \<equiv> curry (curry11 f)"
  abbreviation "uncurry13 f \<equiv> uncurry (uncurry12 f)"
  abbreviation "curry13 f \<equiv> curry (curry12 f)"
  abbreviation "uncurry14 f \<equiv> uncurry (uncurry13 f)"
  abbreviation "curry14 f \<equiv> curry (curry13 f)"
  abbreviation "uncurry15 f \<equiv> uncurry (uncurry14 f)"
  abbreviation "curry15 f \<equiv> curry (curry14 f)"
  abbreviation "uncurry16 f \<equiv> uncurry (uncurry15 f)"
  abbreviation "curry16 f \<equiv> curry (curry15 f)"
  abbreviation "uncurry17 f \<equiv> uncurry (uncurry16 f)"
  abbreviation "curry17 f \<equiv> curry (curry16 f)"
  abbreviation "uncurry18 f \<equiv> uncurry (uncurry17 f)"
  abbreviation "curry18 f \<equiv> curry (curry17 f)"
  abbreviation "uncurry19 f \<equiv> uncurry (uncurry18 f)"
  abbreviation "curry19 f \<equiv> curry (curry18 f)"
  abbreviation "uncurry20 f \<equiv> uncurry (uncurry19 f)"
  abbreviation "curry20 f \<equiv> curry (curry19 f)"


  abbreviation comp4  (infixl "oooo" 55)       where "f oooo g \<equiv>       \<lambda>x. f ooo (g x)"
  abbreviation comp5  (infixl "ooooo" 55)      where "f ooooo g \<equiv>      \<lambda>x. f oooo (g x)"
  abbreviation comp6  (infixl "oooooo" 55)     where "f oooooo g \<equiv>     \<lambda>x. f ooooo (g x)"
  abbreviation comp7  (infixl "ooooooo" 55)    where "f ooooooo g \<equiv>    \<lambda>x. f oooooo (g x)"
  abbreviation comp8  (infixl "oooooooo" 55)   where "f oooooooo g \<equiv>   \<lambda>x. f ooooooo (g x)"
  abbreviation comp9  (infixl "ooooooooo" 55)  where "f ooooooooo g \<equiv>  \<lambda>x. f oooooooo (g x)"
  abbreviation comp10 (infixl "oooooooooo" 55) where "f oooooooooo g \<equiv> \<lambda>x. f ooooooooo (g x)"
  abbreviation comp11 (infixl "o\<^sub>1\<^sub>1" 55) where "f o\<^sub>1\<^sub>1 g \<equiv> \<lambda>x. f oooooooooo (g x)"
  abbreviation comp12 (infixl "o\<^sub>1\<^sub>2" 55) where "f o\<^sub>1\<^sub>2 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>1 (g x)"
  abbreviation comp13 (infixl "o\<^sub>1\<^sub>3" 55) where "f o\<^sub>1\<^sub>3 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>2 (g x)"
  abbreviation comp14 (infixl "o\<^sub>1\<^sub>4" 55) where "f o\<^sub>1\<^sub>4 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>3 (g x)"
  abbreviation comp15 (infixl "o\<^sub>1\<^sub>5" 55) where "f o\<^sub>1\<^sub>5 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>4 (g x)"
  abbreviation comp16 (infixl "o\<^sub>1\<^sub>6" 55) where "f o\<^sub>1\<^sub>6 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>5 (g x)"
  abbreviation comp17 (infixl "o\<^sub>1\<^sub>7" 55) where "f o\<^sub>1\<^sub>7 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>6 (g x)"
  abbreviation comp18 (infixl "o\<^sub>1\<^sub>8" 55) where "f o\<^sub>1\<^sub>8 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>7 (g x)"
  abbreviation comp19 (infixl "o\<^sub>1\<^sub>9" 55) where "f o\<^sub>1\<^sub>9 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>8 (g x)"
  abbreviation comp20 (infixl "o\<^sub>2\<^sub>0" 55) where "f o\<^sub>2\<^sub>0 g \<equiv> \<lambda>x. f o\<^sub>1\<^sub>9 (g x)"
  
  (* TODO: Why are the number of o off by one?*)
  notation
    comp4 (infixl "\<circ>\<circ>\<circ>" 55) and
    comp5 (infixl "\<circ>\<circ>\<circ>\<circ>" 55) and
    comp6 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
    comp7 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
    comp8 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
    comp9 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
    comp10 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
    comp11 (infixl "\<circ>\<^sub>1\<^sub>1" 55) and
    comp12 (infixl "\<circ>\<^sub>1\<^sub>2" 55) and
    comp13 (infixl "\<circ>\<^sub>1\<^sub>3" 55) and
    comp14 (infixl "\<circ>\<^sub>1\<^sub>4" 55) and
    comp15 (infixl "\<circ>\<^sub>1\<^sub>5" 55) and
    comp16 (infixl "\<circ>\<^sub>1\<^sub>6" 55) and
    comp17 (infixl "\<circ>\<^sub>1\<^sub>7" 55) and
    comp18 (infixl "\<circ>\<^sub>1\<^sub>8" 55) and
    comp19 (infixl "\<circ>\<^sub>1\<^sub>9" 55) and
    comp20 (infixl "\<circ>\<^sub>2\<^sub>0" 55)
    
    
    
    
    
  
  
  
  
  
  
    
    
  lemma fold_partial_uncurry: "uncurry (\<lambda>(ps, cf). f ps cf) = uncurry2 f" by auto

  lemma curry_shl: 
    "\<And>g f. (g \<equiv> curry f) \<equiv> (uncurry g \<equiv> f)"
    "\<And>g f. (g \<equiv> curry0 f) \<equiv> (uncurry0 g \<equiv> f)"
    by (atomize (full); auto)+
  
  lemma curry_shr: 
    "\<And>f g. (curry f \<equiv> g) \<equiv> (f \<equiv> uncurry g)"
    "\<And>f g. (curry0 f \<equiv> g) \<equiv> (f \<equiv> uncurry0 g)"
    by (atomize (full); auto)+
  
  lemmas uncurry_shl = curry_shr[symmetric]  
  lemmas uncurry_shr = curry_shl[symmetric]  
  
end
