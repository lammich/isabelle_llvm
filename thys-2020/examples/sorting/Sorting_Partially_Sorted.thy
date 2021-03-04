theory Sorting_Partially_Sorted
imports Main "HOL-Library.Multiset"
begin

  
  
context 
  fixes LT :: "'a\<Rightarrow>'a\<Rightarrow>bool"  
begin
    
  definition "slice_LT xs ys \<equiv> \<forall>x\<in>set xs. \<forall>y\<in>set ys. LT x y"  
  
  definition "is_slicing n xs ss \<equiv> xs = concat ss \<and> (\<forall>s\<in>set ss. s\<noteq>[] \<and> length s \<le> n)"
  
  definition "part_sorted_wrt n xs \<equiv> \<exists>ss. is_slicing n xs ss \<and> sorted_wrt slice_LT ss"


  lemma slice_LT_cons1: 
    "slice_LT (x#xs) ys \<longleftrightarrow> (\<forall>y\<in>set ys. LT x y) \<and> (slice_LT xs ys)" by (auto simp: slice_LT_def)
  
  lemma slice_LT_mset_eq1: "mset xs = mset xs' \<Longrightarrow> slice_LT xs ys \<longleftrightarrow> slice_LT xs' ys"
    unfolding slice_LT_def by (auto dest: mset_eq_setD)
  
  lemma slice_LT_mset_eq2: "mset ys = mset ys' \<Longrightarrow> slice_LT xs ys \<longleftrightarrow> slice_LT xs ys'"
    unfolding slice_LT_def by (auto dest: mset_eq_setD)
  
  lemma slice_LT_setcongI: "\<lbrakk>slice_LT xs ys; set xs = set xs'; set ys = set ys' \<rbrakk> \<Longrightarrow> slice_LT xs' ys'"
    unfolding slice_LT_def by auto
    
  
    
  lemma is_slicing_empty1[simp]: "is_slicing n [] ss \<longleftrightarrow> ss=[]" by (auto simp: is_slicing_def)
  lemma is_slicing_empty2[simp]: "is_slicing n xs [] \<longleftrightarrow> xs=[]" by (auto simp: is_slicing_def)
    
  lemma is_slicing_cons2: "is_slicing n xs (s#ss) \<longleftrightarrow> s\<noteq>[] \<and> length s \<le> n \<and> (\<exists>xs'. xs=s@xs' \<and> is_slicing n xs' ss)"
    by (auto simp: is_slicing_def)

  lemma part_sorted_wrt_Nil[iff]: "part_sorted_wrt n []"
    unfolding part_sorted_wrt_def is_slicing_def by (auto intro: exI[where x="[]"])
  
  lemma part_sorted_wrt_zero_iff_empty[simp]: "part_sorted_wrt 0 xs \<longleftrightarrow> xs=[]"
    unfolding part_sorted_wrt_def is_slicing_def
    by auto
  
  lemma part_sorted_wrt_mono: "n\<le>m \<Longrightarrow> part_sorted_wrt n xs \<Longrightarrow> part_sorted_wrt m xs"  
    unfolding part_sorted_wrt_def is_slicing_def
    by fastforce
    
  lemma part_sorted_wrt_init: "length xs \<le> n \<Longrightarrow> part_sorted_wrt n xs"
    apply (cases xs)  
    subgoal by simp
    subgoal
      unfolding part_sorted_wrt_def is_slicing_def
      by (auto intro: exI[where x="[xs]"])
    done
  
  lemma part_sorted_concatI:
    assumes PSX: "part_sorted_wrt n xs"
        and PSY: "part_sorted_wrt n ys" 
        and SLT: "slice_LT xs ys" 
    shows "part_sorted_wrt n (xs@ys)"  
  proof -
    from PSX obtain xss where SLIX: "is_slicing n xs xss" and SX: "sorted_wrt slice_LT xss" unfolding part_sorted_wrt_def by blast
    from PSY obtain yss where SLIY: "is_slicing n ys yss" and SY: "sorted_wrt slice_LT yss" unfolding part_sorted_wrt_def by blast
  
    from SLIX SLIY have SLICING: "is_slicing n (xs@ys) (xss@yss)"  (* TODO: make this a lemma: is_slicing_concatI *)
      unfolding is_slicing_def
      by auto
  
    have XSS_ELEMS: "set x \<subseteq> set xs" if "x\<in>set xss" for x
      using that SLIX 
      unfolding is_slicing_def
      by auto
      
    have YSS_ELEMS: "set y \<subseteq> set ys" if "y\<in>set yss" for y
      using that SLIY 
      unfolding is_slicing_def
      by auto
      
    have "local.slice_LT lx ly" if "lx \<in> set xss" "ly \<in> set yss" for lx ly
      using that XSS_ELEMS YSS_ELEMS SLT unfolding slice_LT_def by blast
      
    then have "sorted_wrt slice_LT (xss@yss)" using SX SY 
      by (auto simp: sorted_wrt_append)
    with SLICING show ?thesis unfolding part_sorted_wrt_def by auto
  qed
  
    
  lemma sorted_wrt_imp_part_sorted1: "sorted_wrt LT xs \<Longrightarrow> part_sorted_wrt 1 xs"  
    unfolding part_sorted_wrt_def
    apply (rule exI[where x="map (\<lambda>x. [x]) xs"])
    unfolding is_slicing_def 
    by (auto simp: sorted_wrt_map slice_LT_def)

  lemma sorted_wrt_imp_part_sorted: "\<lbrakk>sorted_wrt LT xs; 1\<le>n\<rbrakk> \<Longrightarrow> part_sorted_wrt n xs"  
    using part_sorted_wrt_mono[of 1 n xs] sorted_wrt_imp_part_sorted1 by simp
    
        
  lemma part_sorted_guardedI:
    assumes S: "part_sorted_wrt n xs" and B: "n\<le>i" "i<length xs"  
    shows "LT (xs!0) (xs!i)"  
  proof -  
    from S have "n\<noteq>0" \<open>i\<noteq>0\<close> using B by (cases n; auto)+
    
    
    from S obtain ss where SL: "is_slicing n xs ss" and SORTED: "sorted_wrt slice_LT ss" unfolding part_sorted_wrt_def by auto
    from SL \<open>i<length xs\<close> obtain x s ss' where SSEQ: "ss=(x#s)#ss'" and XSEQ1: "xs = x#s@concat ss'" and L: "length (x#s) \<le> n"
      apply (cases xs; simp)
      apply (cases ss; simp)
      apply (auto simp: is_slicing_cons2 Cons_eq_append_conv)
      by (metis is_slicing_def)
  
    define xi where "xi = xs!i"
    obtain xs1 xs2 where XSEQ2: "xs=xs1@xi#xs2" and "length xs1 = i"
      unfolding xi_def using id_take_nth_drop[OF \<open>i<length xs\<close>] B by simp
    
    have "xs1 \<noteq> []" using \<open>length xs1 = i\<close> \<open>i\<noteq>0\<close> by auto
      
    from XSEQ1 XSEQ2 have "x#s@concat ss' = xs1@xi#xs2" by simp
    then have "xi\<in>set (concat ss')"
      supply [simp del] = set_concat
      using \<open>xs1 \<noteq> []\<close>
      using L B \<open>length xs1 = i\<close>
      by (auto simp: append_eq_append_conv2 Cons_eq_append_conv append_eq_Cons_conv)
      
    with SSEQ SORTED have "LT x xi"  
      by (auto simp: slice_LT_cons1)
    thus ?thesis unfolding xi_def XSEQ1 by simp
  qed      

    
end  


lemma slice_LT_mono: "\<lbrakk>slice_LT R xs ys; (\<And>x y. R x y \<Longrightarrow> R' x y)\<rbrakk> \<Longrightarrow> slice_LT R' xs ys"  
  by (auto simp: slice_LT_def)
  



end
