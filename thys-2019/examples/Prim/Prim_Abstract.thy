section \<open>Prim's Algorithm\<close>
theory Prim_Abstract
imports 
  Main 
  Undirected_Graph
  "../../sepref/IICF/IICF"
  "../../sepref/IICF/Impl/IICF_Array_of_Array_List"
begin

(* TODO: Move *)
  thm nres_monad_laws
  lemma bind_res_singleton[simp]: "bind (RES {x}) f = f x"
    by (auto simp: pw_eq_iff refine_pw_simps)
    

  (* TODO: Move! *)
  definition "combf X f\<^sub>1 f\<^sub>2 x \<equiv> if x\<in>X then f\<^sub>1 x else f\<^sub>2 x"
  
  lemma combf_left[simp]: "x\<in>X \<Longrightarrow> combf X f\<^sub>1 f\<^sub>2 x = f\<^sub>1 x" by (auto simp: combf_def)
  lemma combf_right[simp]: "x\<notin>X \<Longrightarrow> combf X f\<^sub>1 f\<^sub>2 x = f\<^sub>2 x" by (auto simp: combf_def)
  
  lemma combf_empty[simp]: "combf {} f\<^sub>1 f\<^sub>2 = f\<^sub>2" by (auto simp: combf_def)
  lemma combf_insert[simp]: "combf (insert x X) f\<^sub>1 f\<^sub>2 = (combf X f\<^sub>1 f\<^sub>2)(x:=f\<^sub>1 x)"
    by (auto simp: combf_def)
  
  lemma fun_upd_idem_iff': "f = f(x:=y) \<longleftrightarrow> f x = y"
    using fun_upd_idem_iff by fastforce
    
  lemma f_upd_same_eq_iff[simp]: "f(x:=y) = f(x:=y') \<longleftrightarrow> y=y'" by (auto simp: fun_eq_iff)
  lemma ins_eq_set_memD:  "insert x S = S' \<Longrightarrow> x\<in>S'" by blast

  (* TODO: Move *)
  lemma card2_eq: "card e = 2 \<longleftrightarrow> (\<exists>u v. u\<noteq>v \<and> e={u,v})"
    by (auto simp: eval_nat_numeral card_Suc_eq)
  

text \<open>Restructuring refinement of a while loop: The concrete 
  loop does an initial iteration, which is invisible on the abstract level.

  This restructuring naturally arises in our refinement of Prim's algorithm.
\<close>
lemma WHILEIT_add_init_step:
  assumes [simp]: "cb cs" 
  assumes [refine]: "cf cs \<le> SPEC (\<lambda>c. (c, as) \<in> R)"
  assumes [simp]: "\<And>s s'. \<lbrakk>(s, s') \<in> R; I s'\<rbrakk> \<Longrightarrow> cb s = ab s'"
  assumes [simp]: "\<And>s s'. \<lbrakk>(s, s') \<in> R; cb s; ab s'; I s'\<rbrakk> \<Longrightarrow> cf s \<le> \<Down> R (af s')"
  shows "WHILET cb cf cs \<le>\<Down>R (WHILEIT I ab af as)" (is "?C \<le>\<Down>_ ?A")
proof -
  have "?C = do { s \<leftarrow> cf cs; WHILET cb cf s }"
    by (rewrite in "\<hole>=_" WHILET_unfold) simp
  also have "\<dots> \<le>\<Down>R (do { s \<leftarrow> RETURN as; WHILEIT I ab af s})" (is "_ \<le> \<Down>_ \<dots>") 
    by refine_rcg simp_all
  also have "\<dots> = ?A" by simp
  finally show ?thesis .
qed
  
  



declare [[coercion_enabled = false]]

subsection \<open>Miscellaneous\<close>

lemma least_antimono: "X\<noteq>{} \<Longrightarrow> X\<subseteq>Y \<Longrightarrow> (LEAST y::_::wellorder. y\<in>Y) \<le> (LEAST x. x\<in>X)"
  by (metis LeastI_ex Least_le equals0I rev_subsetD)

lemma map_add_apply: "(m\<^sub>1 ++ m\<^sub>2) k = (case m\<^sub>2 k of None \<Rightarrow> m\<^sub>1 k | Some x \<Rightarrow> Some x)"
  by (auto simp: map_add_def)

lemma Inf_in:
  fixes A :: "'a::{linorder,complete_lattice} set"
  assumes "finite A" "A\<noteq>{}" 
  shows "Inf A \<in> A" 
  using assms 
  proof (induction A rule: finite_induct)
    case empty
    then show ?case by simp
  next
    have [simp]: "inf a b = (if a\<le>b then a else b)" for a b :: 'a
      by (meson inf_absorb2 le_iff_inf linear)
  
    case (insert x F)
    show ?case proof cases
      assume "F={}" thus ?thesis by auto
    next
      assume "F\<noteq>{}"
      with insert.IH have "Inf F \<in> F" .
      then show ?thesis
        using le_less_linear[of x "Inf F"]
        by auto 
    
  qed
qed  
  
lemma finite_inf_linorder_ne_ex:
  fixes f :: "_ \<Rightarrow> _::{complete_lattice,linorder}"
  assumes "finite S"
  assumes "S\<noteq>{}"
  shows "\<exists>x\<in>S. (INF x:S. f x) = f x"
  using assms
  by (meson Inf_in finite_imageI imageE image_is_empty)
  
  

lemma finite_linorder_eq_INF_conv: "finite S 
  \<Longrightarrow> a = (INF x:S. f x) \<longleftrightarrow> (if S={} then a=top else \<exists>x\<in>S. a=f x \<and> (\<forall>y\<in>S. a \<le> f y))"
  for a :: "_::{complete_lattice,linorder}"
  by (auto 
    simp: INF_greatest INF_lower  
    intro: finite_inf_linorder_ne_ex antisym)
  

subsection \<open>Graph Theory for Prim\<close>  
  
  definition "is_subset_MST w g A \<equiv> \<exists>t. is_MST w g t \<and> A \<subseteq> edges t"  
  
  lemma is_subset_MST_empty[simp]: "connected g \<Longrightarrow> is_subset_MST w g {}"
    using exists_MST unfolding is_subset_MST_def by blast
  
    
subsection \<open>Generic Algorithm: Light Edges\<close>  
text \<open>We fix a start node and a weighted graph\<close>
locale Prim =
  fixes w :: "'v set \<Rightarrow> nat" and g :: "'v ugraph" and r :: 'v
begin
  text \<open>Reachable part of the graph\<close>
  definition "rg \<equiv> component_of g r"

  lemma reachable_connected[simp, intro!]: "connected rg" unfolding rg_def by auto
  lemma reachable_edges_subset: "edges rg \<subseteq> edges g" unfolding rg_def by (rule component_edges_subset)


  definition "light_edge C A u v 
    \<equiv>   A \<subseteq> C\<times>C 
      \<and> u\<in>C \<and> v\<notin>C \<and> (u,v)\<in>edges rg 
      \<and> (\<forall>(u',v')\<in>edges rg \<inter> C\<times>-C. w {u,v} \<le> w {u',v'})"  
    
  lemma light_edge_is_safe:
    fixes A :: "('v\<times>'v) set" and S :: "'v set"
    assumes subset_MST: "is_subset_MST w rg A"
    assumes light_edge: "light_edge S A u v"
    shows "is_subset_MST w rg ({(v,u)} \<union> A)"
  proof -
    have  respects_cut: "A \<subseteq> S\<times>S"
      and crossing_edge: "u\<in>S" "v\<notin>S" "(u,v)\<in>edges rg"
      and min_edge: "\<forall>(u',v')\<in>edges rg \<inter> S\<times>-S. w {u,v} \<le> w {u',v'}"
      using light_edge unfolding light_edge_def by auto
  
    from subset_MST obtain T where T: "is_MST w rg T" "A \<subseteq> edges T" unfolding is_subset_MST_def by auto
    hence "tree T" "edges T \<subseteq> edges rg" "nodes T = nodes rg" by(simp_all add: is_MST_def is_spanning_tree_def)
    hence "connected T" by(simp_all add: tree_def)
    show ?thesis
    proof cases
      assume "(u,v) \<in> edges T"
      thus ?thesis unfolding is_subset_MST_def using T by (auto simp: edges_sym')
    next
      assume "(u,v) \<notin> edges T" hence "(v,u)\<notin>edges T" by (auto simp: edges_sym')
      from \<open>(u,v)\<in>edges rg\<close> obtain p where p: "path T u p v" "simple p"
        by (metis connectedD \<open>connected T\<close> \<open>nodes T = nodes rg\<close> nodesI rtrancl_edges_iff_path simplify_pathE)
        
      have [simp]: "u\<noteq>v" using crossing_edge by blast
        
      from find_crossing_edge_on_path[OF p(1), where P="\<lambda>x. x\<notin>S"] crossing_edge(1,2)
      obtain x y p1 p2 where xy: "(x,y) \<in> set p" "x \<in> S" "y \<notin> S"
        and ux: "path (restrict_edges T (-{(x,y),(y,x)})) u p1 x" 
        and yv: "path (restrict_edges T (-{(x,y),(y,x)})) y p2 v"
        using path_change[OF crossing_edge(1,2) p] by blast
      have "(x,y) \<in> edges T" 
        by (meson contra_subsetD p(1) path_edges xy(1))

      let ?E' = "edges T - {(x,y),(y,x)}"
        
      from split_tree[OF \<open>tree T\<close> \<open>(x,y)\<in>edges T\<close>]
        obtain T1 T2 where T12: 
          "tree T1" "tree T2" 
          and "nodes T1 \<inter> nodes T2 = {}" 
          and "nodes T = nodes T1 \<union> nodes T2"
          and "edges T1 \<union> edges T2 = ?E'"
          and "nodes T1 = { u . (x,u)\<in>?E'\<^sup>*}"
          and "nodes T2 = { u . (y,u)\<in>?E'\<^sup>*}"
          and "x\<in>nodes T1" "y\<in>nodes T2" .
      
      let ?T' = "ins_edge (u,v) (graph_join T1 T2)"    

      have "is_spanning_tree rg ?T'" proof -
        
        have E'_sym: "sym (?E'\<^sup>*)" 
          by (meson edgesT_diff_sng_inv_eq sym_conv_converse_eq sym_rtrancl)
        
        have "u\<in>nodes T1" 
          unfolding \<open>nodes T1 = _\<close>
          using path_rtrancl_edgesD[OF ux] by (auto dest: symD[OF E'_sym])
          
        have "v\<in>nodes T2" 
          unfolding \<open>nodes T2 = _\<close>
          using path_rtrancl_edgesD[OF yv] by auto
                
        have "tree ?T'" by (rule join_trees) fact+
  
        show "is_spanning_tree rg ?T'"
          unfolding is_spanning_tree_def
          using \<open>nodes T = nodes rg\<close> \<open>nodes T = nodes T1 \<union> nodes T2\<close>[symmetric] \<open>tree ?T'\<close> \<open>u\<noteq>v\<close>
          using \<open>edges T \<subseteq> edges rg\<close> \<open>edges T1 \<union> edges T2 = ?E'\<close>
          apply simp
          by (metis Diff_subset crossing_edge(3) edges_sym' insert_absorb nodesI(2) subset_trans)
      qed
      moreover 
        
      have "weight w ?T' \<le> weight w T'" if "is_spanning_tree rg T'" for T'
      proof -
        have ww: "w {u,v} \<le> w{x,y}" 
          using min_edge \<open>(x,y)\<in>edges T\<close> \<open>edges T \<subseteq> edges rg\<close> \<open>x\<in>S\<close> \<open>y\<notin>S\<close>
          by blast
          
        have "weight w ?T' = weight w T - w {x,y} + w{u,v}"
          using \<open>(u, v) \<notin> edges T\<close> \<open>(x, y) \<in> edges T\<close> \<open>edges T1 \<union> edges T2 = edges T - {(x, y), (y, x)}\<close> \<open>u \<noteq> v\<close>
          by (smt Diff_eq Diff_subset add.commute contra_subsetD edges_join edges_restrict_edges minus_inv_sym_aux sup.idem weight_cong weight_del_edge weight_ins_edge)
        also have "\<dots> \<le> weight w T" 
          using weight_ge_edge[OF \<open>(x,y)\<in>edges T\<close>, of w] ww by auto
        also have "weight w T \<le> weight w T'" using T(1) \<open>is_spanning_tree rg T'\<close>
          unfolding is_MST_def by simp
        finally show ?thesis . 
      qed
      ultimately have "is_MST w rg ?T'" using is_MST_def by blast
      have "{(u,v),(v,u)} \<union> A \<subseteq> edges ?T'" using T(2) respects_cut xy(3) \<open>edges T1 \<union> edges T2 = ?E'\<close>
        by (auto)
      with \<open>is_MST w rg ?T'\<close> show ?thesis unfolding is_subset_MST_def by force
    qed
  qed        
end    
   
subsection \<open>Abstract Prim: Growing a Tree\<close>
context Prim begin 
  text \<open>The current nodes\<close> 
  definition "S A \<equiv> {r} \<union> fst`A"
  
  text \<open>Refined invariant: Adds connectedness of \<open>A\<close>\<close>
  definition "prim_invar1 A \<equiv> is_subset_MST w rg A \<and> (\<forall>(u,v)\<in>A. (v,r)\<in>A\<^sup>*)"
  
  text \<open>Measure: Number of nodes not in tree\<close>
  definition "T_measure1 A = card (nodes rg - S A)"
end

text \<open>We use a locale that fixes a state and assumes the invariant\<close>
locale Prim_Invar1_loc = 
  Prim w g r for w g and r :: 'v +
  fixes A :: "('v\<times>'v) set"
  assumes invar1: "prim_invar1 A"
begin  
  lemma subset_MST: "is_subset_MST w rg A" using invar1 unfolding prim_invar1_def by auto
  lemma A_connected: "(u,v)\<in>A \<Longrightarrow> (v,r)\<in>A\<^sup>*" using invar1 unfolding prim_invar1_def by auto

  lemma S_alt_def: "S A = {r} \<union> fst`A \<union> snd`A" 
    apply auto
    apply (auto simp: S_def rev_image_eqI)
    by (metis A_connected Domain_fst Not_Domain_rtrancl)
 
  lemma finite_rem_nodes[simp,intro!]: "finite (nodes rg - S A)" by auto
  
  lemma respects_cut: "A \<subseteq> S A \<times> S A"
    unfolding S_alt_def
    by (smt Range.RangeI Range_snd Un_iff fst_conv image_subset_iff mem_Sigma_iff subrelI sup_ge2)

  lemma A_edges: "A \<subseteq> edges g"  
    using subset_MST
    by (meson is_MST_def is_spanning_tree_def is_subset_MST_def reachable_edges_subset subset_eq)

  lemma S_reachable: "S A \<subseteq> nodes rg"  
    unfolding S_def
    by (smt DomainE Un_insert_left fst_eq_Domain insert_subset is_MST_def is_spanning_tree_def is_subset_MST_def nodesI(1) nodes_of_component reachable_nodes_refl rg_def subset_MST subset_iff sup_bot.left_neutral)
    
  lemma S_edge_reachable: "\<lbrakk>u\<in>S A; (u,v)\<in>edges g \<rbrakk> \<Longrightarrow> (u,v)\<in>edges rg"  
    using S_reachable unfolding rg_def
    using reachable_nodes_step'(2) by fastforce
      
  lemma edges_S_rg_edges: "edges g \<inter> S A\<times>-S A = edges rg \<inter> S A\<times>-S A"
    using S_edge_reachable reachable_edges_subset by auto
        
  lemma T_measure1_less: "T_measure1 A < card (nodes rg)"
    unfolding T_measure1_def S_def
    by (metis Diff_subset S_def S_reachable Un_insert_left le_supE nodes_finite psubsetI psubset_card_mono singletonI subset_Diff_insert)


  lemma finite_A[simp, intro!]: "finite A"
    using A_edges finite_subset by auto
  
  lemma finite_S[simp, intro!]: "finite (S A)" 
    using S_reachable rev_finite_subset by blast
  
  (* TODO: Used? *)
  lemma S_A_consistent[simp, intro!]: "nodes_edges_consistent (S A) (A\<union>A\<inverse>)"
    unfolding nodes_edges_consistent_def
    apply (intro conjI)
    subgoal by simp
    subgoal using A_edges irrefl_def by fastforce
    subgoal by (simp add: sym_Un_converse)
    using respects_cut by auto
    
      
end

context Prim begin

  lemma invar1_initial: "prim_invar1 {}"
    apply (auto simp: is_subset_MST_def prim_invar1_def)
    by (simp add: Prim.reachable_connected exists_MST)

  lemma maintain_invar1:
    assumes invar: "prim_invar1 A"
    assumes light_edge: "light_edge (S A) A u v"
    shows "prim_invar1 ({(v,u)}\<union>A) 
         \<and> T_measure1 ({(v,u)}\<union>A) < T_measure1 A" (is "?G1 \<and> ?G2")
  proof

    from invar interpret Prim_Invar1_loc w g r A by unfold_locales

    from light_edge have "u\<in>S A" "v\<notin>S A" by (simp_all add: light_edge_def)
        
    show ?G1
      unfolding prim_invar1_def
    proof (intro conjI)
      show "is_subset_MST w rg ({(v, u)} \<union> A)"
        by (rule light_edge_is_safe[OF subset_MST light_edge])
        
    next
      show "\<forall>(ua, va)\<in>{(v, u)} \<union> A. (va, r) \<in> ({(v, u)} \<union> A)\<^sup>*"
        apply safe
        using A_connected      
        apply (auto simp: rtrancl_insert)
        apply (metis DomainE S_def converse_rtrancl_into_rtrancl \<open>u\<in>S A\<close> fst_eq_Domain insertE insert_is_Un rtrancl_eq_or_trancl)
        by (metis DomainE Domain_fst S_def converse_rtrancl_into_rtrancl \<open>u\<in>S A\<close> insertE insert_is_Un rtrancl.rtrancl_refl)
    qed
    then interpret N: Prim_Invar1_loc w g r "{(v,u)}\<union>A" by unfold_locales
    
    have "S A \<subset> S ({(v,u)}\<union>A)" using \<open>v\<notin>S A\<close>
      unfolding S_def by auto
    then show "?G2" unfolding T_measure1_def
      using S_reachable N.S_reachable
      by (auto intro!: psubset_card_mono)
  
  qed  

  lemma invar1_finish:
    assumes INV: "prim_invar1 A"
    assumes FIN: "edges g \<inter> S A\<times>-S A = {}"
    shows "is_MST w rg (graph {r} A)"
  proof -
    from INV interpret Prim_Invar1_loc w g r A by unfold_locales

    from subset_MST obtain t where MST: "is_MST w rg t" and "A \<subseteq> edges t"
      unfolding is_subset_MST_def by auto
    
    have "S A = nodes t"
    proof safe
      fix u
      show "u\<in>S A \<Longrightarrow> u\<in>nodes t" using MST
        unfolding is_MST_def is_spanning_tree_def
        using S_reachable by auto
    next
      fix u
      assume "u\<in>nodes t"
      hence "u\<in>nodes rg"
        using MST is_MST_def is_spanning_tree_def by force
      hence 1: "(u,r)\<in>(edges rg)\<^sup>*" by (simp add: connectedD rg_def)
      have "r\<in>S A" by (simp add: S_def)
      show "u\<in>S A" proof (rule ccontr)
        assume "u\<notin>S A"
        from find_crossing_edge_rtrancl[where P="\<lambda>u. u\<in>S A", OF 1 \<open>u\<notin>S A\<close> \<open>r\<in>S A\<close>] 
          FIN reachable_edges_subset 
        show False
          by (smt ComplI IntI contra_subsetD edges_sym' emptyE mem_Sigma_iff)
          
      qed
    qed
    also have "nodes t = nodes rg" 
      using MST unfolding is_MST_def is_spanning_tree_def
      by auto
    finally have S_eq: "S A = nodes rg" .
    
    define t' where "t' = graph {r} A"
    
    have [simp]: "nodes t' = S A" and Et': "edges t' = (A\<union>A\<inverse>)" unfolding t'_def 
      using A_edges
      by (auto simp: graph_accs S_alt_def)
    
    hence "edges t' \<subseteq> edges t"
      by (smt UnE \<open>A \<subseteq> edges t\<close> converseD edges_sym' subrelI subset_eq)
    
    have "is_spanning_tree rg t'"
    proof -
      have "connected t'"  
        apply rule
        apply (auto simp: Et' S_def)
        apply (simp add: A_connected converse_rtrancl_into_rtrancl in_rtrancl_UnI rtrancl_converse)+
        apply (meson A_connected in_rtrancl_UnI r_into_rtrancl rtrancl_converseI rtrancl_trans)+
        done
    
      moreover have "cycle_free t'"
        by (meson MST \<open>edges t' \<subseteq> edges t\<close> cycle_free_antimono is_MST_def 
                  is_spanning_tree_def tree_def)      
      moreover have "edges t' \<subseteq> edges rg"
        by (meson MST \<open>edges t' \<subseteq> edges t\<close> dual_order.trans is_MST_def is_spanning_tree_def)
      ultimately show ?thesis
        unfolding is_spanning_tree_def tree_def
        by (auto simp: S_eq)
    qed                              
    then show ?thesis
      using MST weight_mono[OF \<open>edges t' \<subseteq> edges t\<close>]
      unfolding t'_def is_MST_def 
      using dual_order.trans by blast
  qed    

  
  definition "prim1 \<equiv> do {
    let A={};
    A \<leftarrow> WHILEIT prim_invar1 (\<lambda>A. edges g \<inter> S A\<times>-S A \<noteq> {}) (\<lambda>A. do {
      (u,v) \<leftarrow> SPEC (\<lambda>(u,v). light_edge (S A) A u v);
      RETURN (insert (v,u) A)
    }) A;
    RETURN A
  }"
  
  lemma prim1_correct: "prim1 \<le> SPEC (\<lambda>A. is_MST w rg (graph {r} A))"
    unfolding prim1_def
    apply (refine_vcg WHILEIT_rule[where R="measure T_measure1"])
    using maintain_invar1
    by (clarsimp_all simp: invar1_initial invar1_finish)
  
        
end

subsection \<open>Prim: Using a Priority Queue\<close>
text \<open>We define a new locale. Note that we could also reuse @{locale Prim}, however,
  this would complicate referencing the constants later in the theories from 
  which we generate the paper.
\<close>
locale Prim2 = Prim w g r for w :: "'v set \<Rightarrow> nat" and g :: "'v ugraph" and r :: 'v
begin  
  text \<open>Abstraction to edge set\<close>
  
  definition "A Q \<pi> \<equiv> {(u,v). \<pi> u = Some v \<and> Q u = \<infinity>}"
  
  text \<open>Initialization\<close>
  definition initQ :: "'v \<Rightarrow> enat"  where "initQ \<equiv> (\<lambda>_. \<infinity>)(r := 0)"
  definition init\<pi> :: "'v \<Rightarrow> 'v option" where "init\<pi> \<equiv> Map.empty"  


  text \<open>Step\<close>  
  definition "upd_cond Q \<pi> u v \<equiv> 
      (v,u) \<in> edges g 
    \<and> v\<noteq>r  
    \<and> enat (w {v,u}) < Q v
    \<and> (Q v = \<infinity> \<longrightarrow> \<pi> v = None)
    "
    
  lemma upd_cond_alt: "upd_cond Q \<pi> u v' \<longleftrightarrow> 
    (v',u) \<in> edges g \<and> v'\<notin>S (A Q \<pi>) \<and> enat (w {v',u}) < Q v'" 
    unfolding upd_cond_def S_def A_def
    by (auto simp: fst_eq_Domain)
    
    
  text \<open>State after inner loop\<close>  
  definition "Qinter Q \<pi> u v' = (if upd_cond Q \<pi> u v' then enat (w {v',u}) else Q v')"

  text \<open>State after one step\<close>  
  definition "Q' Q \<pi> u \<equiv> (Qinter Q \<pi> u)(u:=\<infinity>)"
  definition "\<pi>' Q \<pi> u v' = (if upd_cond Q \<pi> u v' then Some u else \<pi> v')"

  definition "prim_invar2_init Q \<pi> \<equiv> Q=initQ \<and> \<pi>=init\<pi>"
  
  definition "prim_invar2_ctd Q \<pi> \<equiv> let A = A Q \<pi>; S = S A in
    prim_invar1 A \<^cancel>\<open>TODO: Remove this, once refinement is sorted out! \<close>
  \<and> \<pi> r = None \<and> Q r = \<infinity>  
  \<and> (\<forall>(u,v)\<in>edges rg \<inter> (-S)\<times>S. Q u \<noteq> \<infinity>)
  \<and> (\<forall>u. Q u \<noteq> \<infinity> \<longrightarrow> \<pi> u \<noteq> None)
  \<and> (\<forall>u v. \<pi> u = Some v \<longrightarrow> v\<in>S \<and> (u,v)\<in>edges rg)
  \<and> (\<forall>u v d. Q u = enat d \<and> \<pi> u = Some v \<longrightarrow> d=w {u,v} \<and> (\<forall>v'\<in>S. (u,v')\<in>edges rg \<longrightarrow> d \<le> w {u,v'}))  
  "
  
  lemma prim_invar2_ctd_alt_aux1: "\<lbrakk>Q u \<noteq> \<infinity>; u\<noteq>r\<rbrakk> \<Longrightarrow> u\<notin>S (A Q \<pi>)"
    unfolding S_def A_def
    by auto
  
  lemma prim_invar2_ctd_alt: "prim_invar2_ctd Q \<pi> \<longleftrightarrow> (
    let A = A Q \<pi>; S = S A; cE=edges rg \<inter> (-S)\<times>S in
      prim_invar1 A
    \<and> \<pi> r = None \<and> Q r = \<infinity>  
    \<and> (\<forall>(u,v)\<in>cE. Q u \<noteq> \<infinity>)
    \<and> (\<forall>u v. \<pi> u = Some v \<longrightarrow> v\<in>S \<and> (u,v)\<in>edges rg)
    \<and> (\<forall>u d. Q u = enat d \<longrightarrow> (\<exists>v. \<pi> u = Some v \<and> d=w {u,v} \<and> (\<forall>v'. (u,v')\<in>cE \<longrightarrow> d \<le> w {u,v'})))
  )"
    unfolding prim_invar2_ctd_def Let_def
    using prim_invar2_ctd_alt_aux1[of Q _ \<pi>]
    apply (auto 0 3)
    by (metis (no_types,lifting) option.simps(3))
    
  
  definition "prim_invar2 Q \<pi> \<equiv> prim_invar2_init Q \<pi> \<or> prim_invar2_ctd Q \<pi>"
    
  definition "T_measure2 Q \<pi> \<equiv> if Q r = \<infinity> then T_measure1 (A Q \<pi>) else card (nodes rg)"
  
  
  lemma Q'_init_eq: "Q' initQ init\<pi> r = (\<lambda>u. if (u,r)\<in>edges rg then enat (w {u,r}) else \<infinity>)"
    apply (rule ext) 
    using reachable_edges_subset
    apply (auto simp: Q'_def Qinter_def upd_cond_def initQ_def init\<pi>_def)
    by (simp add: Prim.rg_def edges_sym' reachable_nodes_step'(2))

  lemma \<pi>'_init_eq: "\<pi>' initQ init\<pi> r = (\<lambda>u. if (u,r)\<in>edges rg then Some r else None)"  
    apply (rule ext) 
    using reachable_edges_subset
    apply (auto simp: \<pi>'_def upd_cond_def initQ_def init\<pi>_def)
    by (simp add: Prim.rg_def edges_sym' reachable_nodes_step'(2))
  
  lemma A_init_eq: "A initQ init\<pi> = {}"  
    unfolding A_def init\<pi>_def 
    by auto

  lemma S_empty: "S {} = {r}" unfolding S_def by (auto simp: A_init_eq)
        
  lemma maintain_invar2_first_step: 
    assumes INV: "prim_invar2_init Q \<pi>"
    assumes UNS: "Q u = enat d"
    shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
      and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
  proof -
    from INV have [simp]: "Q=initQ" "\<pi>=init\<pi>"
      unfolding prim_invar2_init_def by auto
    from UNS have [simp]: "u=r" by (auto simp: initQ_def split: if_splits) 
      
      
    note Q'_init_eq \<pi>'_init_eq A_init_eq 
      
    have [simp]: "(A (Q' initQ init\<pi> r) (\<pi>' initQ init\<pi> r)) = {}"
      apply (auto simp: Q'_init_eq \<pi>'_init_eq)
      apply (auto simp: A_def split: if_splits)
      done
    
    show ?G1
      apply (auto simp: prim_invar2_ctd_def Let_def invar1_initial)
      apply (simp_all add: Q'_init_eq \<pi>'_init_eq S_empty split: if_splits)
      done
      
    have [simp]: "Q' initQ init\<pi> r r = \<infinity>"  
      by (auto simp: Q'_init_eq)
      
    have [simp]: "initQ r = 0" by (simp add: initQ_def) 
      
    show ?G2  
      unfolding T_measure2_def 
      apply simp
      apply (simp add: T_measure1_def S_empty)
      by (metis card_Diff1_less nodes_finite nodes_of_component reachable_nodes_refl rg_def)
    
  qed    
    
  lemma maintain_invar2_first_step_presentation: 
    assumes INV: "prim_invar2_init Q \<pi>"
    assumes UNS: "Q u = enat d"
    shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)
         \<and> T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>"
    using maintain_invar2_first_step assms by blast
  
    
end

(*<*)
(*
  This locale is only used to present the invariant in the paper.
*)
locale Prim_Invar2_ctd_Presentation_Loc =
  fixes w g and r :: 'v and Q \<pi> A S rg cE
  assumes I: "Prim2.prim_invar2_ctd w g r Q \<pi>"
  defines local_A_def: "A \<equiv> Prim2.A Q \<pi>"
  defines local_S_def: "S \<equiv> Prim.S r A"
  defines local_rg_def: "rg \<equiv> Prim.rg g r"
  defines local_cE_def: "cE \<equiv> edges rg \<inter> (-S)\<times>S"
begin  
    
  lemma 
        invar1: "Prim.prim_invar1 w g r A" (is ?G1)
    and root_contained: "\<pi> r = None \<and> Q r = \<infinity>" (is ?G2)
    and Q_defined: "\<forall>(u,v)\<in>cE. Q u \<noteq> \<infinity>" (is ?G3)
    and \<pi>_edges: "\<forall>u v. \<pi> u = Some v \<longrightarrow> v\<in>S \<and> (u,v)\<in>edges rg" (is ?G4)
    and Q_min: "\<forall>u d. Q u = enat d \<longrightarrow> (\<exists>v. \<pi> u = Some v \<and> d=w {u,v} \<and> (\<forall>v'. (u,v')\<in>cE \<longrightarrow> d \<le> w {u,v'}))" (is ?G5)
  proof -
    interpret Prim2 w g r .
    
    show ?G1 ?G2 ?G3 ?G4 ?G5
      using I
      unfolding local_A_def local_S_def local_rg_def local_cE_def prim_invar2_ctd_alt Let_def
      by simp_all
  qed    
end

lemma (in Prim2) Prim_Invar2_ctd_Presentation_Loc_eq:
  "Prim_Invar2_ctd_Presentation_Loc w g r Q \<pi> \<longleftrightarrow> prim_invar2_ctd Q \<pi>"
  unfolding Prim_Invar2_ctd_Presentation_Loc_def ..

(*>*)

text \<open>Again, we define a locale to fix a state and assume the invariant\<close> 
locale Prim_Invar2_ctd_loc =   
  Prim2 w g r for w g and r :: 'v +
  fixes Q \<pi>
  assumes invar2: "prim_invar2_ctd Q \<pi>"
begin

  sublocale Prim_Invar1_loc w g r "A Q \<pi>"
    using invar2 unfolding prim_invar2_ctd_def
    apply unfold_locales by (auto simp: Let_def)

  lemma \<pi>_root: "\<pi> r = None"
    and Q_root: "Q r = \<infinity>" 
    and Q_defined: "\<lbrakk> (u,v)\<in>edges rg; u\<notin>S (A Q \<pi>); v\<in>S (A Q \<pi>) \<rbrakk> \<Longrightarrow> Q u \<noteq> \<infinity>"
    and \<pi>_defined: "\<lbrakk> Q u \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> \<pi> u \<noteq> None"
    and frontier: "\<pi> u = Some v \<Longrightarrow> v\<in>S (A Q \<pi>)"
    and edges: "\<pi> u = Some v \<Longrightarrow> (u,v)\<in>edges rg"
    and Q_\<pi>_consistent: "\<lbrakk> Q u = enat d; \<pi> u = Some v \<rbrakk> \<Longrightarrow> d = w {u,v}" 
    and Q_min: "Q u = enat d \<Longrightarrow> (\<forall>v'\<in>S (A Q \<pi>). (u,v')\<in>edges rg \<longrightarrow> d \<le> w {u,v'})"
    using invar2 unfolding prim_invar2_ctd_def
    apply (auto simp: Let_def)
    done

  lemma \<pi>_def_on_S: "u\<in>S (A Q \<pi>) \<Longrightarrow> u\<noteq>r \<Longrightarrow> \<pi> u \<noteq> None"
    unfolding S_def
    unfolding A_def
    by auto 
    
  lemma \<pi>_def_on_edges_to_S: "v\<in>S (A Q \<pi>) \<Longrightarrow> u\<noteq>r \<Longrightarrow> (u,v)\<in>edges rg \<Longrightarrow> \<pi> u \<noteq> None"
    apply (cases "u\<in>S (A Q \<pi>)")
    subgoal using \<pi>_def_on_S by auto
    subgoal by (simp add: Q_defined \<pi>_defined)
    done
    
  text \<open>Refinement of loop condition\<close>  
  lemma Q_empty_iff_no_crossing_edges: 
    "(Q = (\<lambda>_. \<infinity>)) \<longleftrightarrow> (edges g \<inter> S (A Q \<pi>) \<times> - S (A Q \<pi>) = {})" (is "?LHS = ?RHS") 
  proof 
    assume ?LHS thus ?RHS by auto (metis (full_types) Q_defined S_edge_reachable edges_sym')
  next
    assume "?RHS" thus ?LHS
    proof (rule_tac ccontr; clarsimp simp: fun_eq_iff)
      fix u d
      assume UNS: "Q u = enat d"
      let ?A = "A Q \<pi>"
      let ?S = "S ?A"
    
      from UNS obtain v where 
        S1[simp]: "\<pi> u = Some v" "d = w {u,v}"
        using \<pi>_defined Q_\<pi>_consistent 
        by blast
              
      have [simp]: "u\<noteq>r" using \<pi>_root using S1 by (auto simp del: S1)
      
      have "v\<in>?S" using frontier[of u v] by auto
      moreover have "u\<notin>?S" unfolding S_def unfolding A_def using UNS by auto
      moreover 
      note edges[OF S1(1), THEN edges_sym'] 
      hence "(v,u)\<in>edges g" using reachable_edges_subset by blast 
      moreover assume "edges g \<inter> ?S \<times> - ?S = {}"
      ultimately show False by blast
    qed
  qed
    
    
  lemma Q_min_is_light:  
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    obtains v where "\<pi> u = Some v" "light_edge (S (A Q \<pi>)) (A Q \<pi>) v u"
  proof -
    let ?A = "A Q \<pi>"
    let ?S = "S ?A"
  
    from UNS obtain v where 
      S1[simp]: "\<pi> u = Some v" "d = w {u,v}"
      using \<pi>_defined Q_\<pi>_consistent 
      by blast
            
    (*TODO: DUP with reasoning in thm Q_empty_iff_no_crossing_edges *)  
      
    have "v\<in>?S" using frontier[of u v] by auto
      
    have [simp]: "u\<noteq>r" using \<pi>_root using S1 by (auto simp del: S1)
    
    have "u\<notin>?S" unfolding S_def unfolding A_def using UNS by auto
    
    have "(v,u)\<in>edges rg" using edges[OF S1(1)]
      by (meson edges_sym' rev_subsetD)
    
    have M: "\<forall>(u', v')\<in>edges rg \<inter> ?S \<times> - ?S. w {v, u} \<le> w {u', v'}"
    proof safe
      fix a b
      assume "(a,b)\<in>edges rg" "a\<in>?S" "b\<notin>?S"
      hence "(b,a)\<in>edges rg" by (simp add: edges_sym')
    
      from Q_defined[OF \<open>(b,a)\<in>edges rg\<close> \<open>b\<notin>?S\<close> \<open>a\<in>?S\<close>] obtain d' where 1: "Q b = enat d'" by blast 
      with \<pi>_defined obtain a' where "\<pi> b = Some a'" by auto
      from MIN 1 have "d\<le>d'" by (metis enat_ord_simps(1))
      also from Q_min[OF 1] \<open>(b,a)\<in>edges rg\<close> \<open>a\<in>?S\<close> have "d'\<le>w {b,a}" by blast  
      finally show "w {v,u} \<le> w {a,b}" by (simp add: insert_commute)
    qed  

    have LE: "light_edge ?S ?A v u" using invar1 \<open>v\<in>?S\<close> \<open>u\<notin>?S\<close> \<open>(v,u)\<in>edges rg\<close> M
      unfolding light_edge_def
      using respects_cut by blast
    
    thus ?thesis using that by auto
  qed

  lemma Q_min_light_edge':
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    shows "\<exists>v. light_edge (S (A Q \<pi>)) (A Q \<pi>) v u \<and> A (Q' Q \<pi> u) (\<pi>' Q \<pi> u) = {(u, v)} \<union> A Q \<pi>"
  proof -    
    let ?A = "A Q \<pi>"
    let ?S = "S ?A"
  
    from Q_min_is_light[OF UNS MIN] obtain v where [simp]: "\<pi> u = Some v" and LE: "light_edge ?S ?A v u" .
    
    let ?Q' = "Q' Q \<pi> u"
    let ?\<pi>' = "\<pi>' Q \<pi> u"
    let ?A' = "A ?Q' ?\<pi>'"
    
    have NA: "?A' = {(u,v)} \<union> ?A"
      unfolding A_def  
      unfolding Q'_def \<pi>'_def upd_cond_def Qinter_def
      by (auto split: if_splits)
    
    with LE show ?thesis by blast
  qed
          
  lemma maintain_invar_ctd: 
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
      and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
  proof -
    let ?A = "A Q \<pi>"
    let ?S = "S ?A"
  
    from Q_min_is_light[OF UNS MIN] obtain v where [simp]: "\<pi> u = Some v" and LE: "light_edge ?S ?A v u" .

    let ?Q' = "Q' Q \<pi> u"
    let ?\<pi>' = "\<pi>' Q \<pi> u"
    let ?A' = "A ?Q' ?\<pi>'"
    let ?S' = "S ?A'"
    
    have NA: "?A' = {(u,v)} \<union> ?A"
      unfolding A_def  
      unfolding Q'_def \<pi>'_def upd_cond_def Qinter_def
      by (auto split: if_splits)
    
    from maintain_invar1[OF invar1 LE]
    have "prim_invar1 ?A'" "T_measure1 ?A' < T_measure1 ?A" 
      by (auto simp: NA) 
    then interpret N: Prim_Invar1_loc w g r ?A' by unfold_locales
                
    have [simp]: "?S' = insert u ?S"
      thm S_alt_def
      unfolding S_def 
      unfolding Q'_def Qinter_def \<pi>'_def upd_cond_def
      unfolding A_def
      by (auto split: if_splits simp: image_iff)
      
    show ?G1
      unfolding prim_invar2_ctd_def Let_def  
      apply safe
      apply fact
      subgoal 
        unfolding \<pi>'_def upd_cond_def
        by (auto simp: \<pi>_root)
      subgoal 
        by (simp add: Prim2.Q'_def Prim2.Qinter_def Prim2.upd_cond_def Q_root)
      subgoal for a b
        apply simp
        apply auto
        subgoal
          apply (auto simp add: Q'_def Qinter_def upd_cond_def)
          apply (auto simp: S_alt_def A_def)
          subgoal using not_infinity_eq by fastforce
          subgoal using reachable_edges_subset by blast
          subgoal by (simp add: Prim.S_def)
          subgoal by (metis (no_types) A_def Q_defined edges frontier)
          done
        subgoal
          apply (auto simp: S_def A_def Q'_def Qinter_def upd_cond_def)
          subgoal
          proof -
            assume a1: "(a, r) \<in> edges rg"
            assume "a \<notin> fst ` {(u, v). \<pi> u = Some v \<and> Q u = \<infinity>}"
            then have "a \<notin> fst ` A Q \<pi>"
              by (simp add: A_def)
            then show ?thesis
              using a1 by (metis (no_types) S_def Q_defined Un_insert_left edges_irrefl' insert_iff not_infinity_eq sup_bot.left_neutral)
          qed 
          by (smt Domain.intros Q_defined \<pi>_def_on_edges_to_S case_prod_conv edges enat.exhaust frontier fst_eq_Domain mem_Collect_eq option.exhaust) 
        done
      subgoal 
        by (metis Q'_def Qinter_def \<pi>'_def \<pi>_defined enat.distinct(2) fun_upd_apply not_None_eq)
        
      subgoal
        by (metis \<open>S (A (Q' Q \<pi> u) (\<pi>' Q \<pi> u)) = insert u (S (A Q \<pi>))\<close> \<pi>'_def frontier insertCI option.inject)
      subgoal
        by (metis N.S_edge_reachable upd_cond_def \<open>S (A (Q' Q \<pi> u) (\<pi>' Q \<pi> u)) = insert u (S (A Q \<pi>))\<close> \<pi>'_def edges edges_sym' insertI1 option.inject)
      subgoal
        by (smt Q'_def \<pi>'_def Prim_Invar2_ctd_loc.Q_\<pi>_consistent Prim_Invar2_ctd_loc_axioms Qinter_def fun_upd_apply insert_absorb not_enat_eq option.inject the_enat.simps)
      subgoal for v' d'
        apply auto unfolding Q'_def Qinter_def upd_cond_def
        using Q_min
        apply (auto split: if_splits simp: Q_root)
        subgoal using reachable_edges_subset by auto
        subgoal by (simp add: le_less less_le_trans)
        subgoal using \<pi>_def_on_edges_to_S by auto
        done 
      done       
    then interpret N: Prim_Invar2_ctd_loc w g r ?Q' ?\<pi>' by unfold_locales

    show ?G2  
      unfolding T_measure2_def
      apply (auto simp: Q_root N.Q_root) by fact
      
  qed      

end

  
context Prim2 begin


  lemma maintain_invar2_ctd: 
    assumes INV: "prim_invar2_ctd Q \<pi>"
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
      and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
  proof -
    interpret Prim_Invar2_ctd_loc w g r Q \<pi> using INV by unfold_locales
    from maintain_invar_ctd[OF UNS MIN] show ?G1 ?G2 by auto
  qed

  lemma Q_min_is_light_presentation:  
    assumes INV: "prim_invar2_ctd Q \<pi>"
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    obtains v where "\<pi> u = Some v" "light_edge (S (A Q \<pi>)) (A Q \<pi>) v u"
  proof -
    interpret Prim_Invar2_ctd_loc w g r Q \<pi> using INV by unfold_locales
    from Q_min_is_light[OF UNS MIN] show ?thesis using that .
  qed
  
  lemma maintain_invar2_ctd_presentation: 
    assumes INV: "prim_invar2_ctd Q \<pi>"
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    shows "prim_invar2_ctd (Q' Q \<pi> u) (\<pi>' Q \<pi> u)
         \<and> T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>"
    using maintain_invar2_ctd assms by blast
  
  lemma not_invar2_ctd_init: 
    "prim_invar2_init Q \<pi> \<Longrightarrow> \<not>prim_invar2_ctd Q \<pi>"
    unfolding prim_invar2_init_def prim_invar2_ctd_def initQ_def Let_def 
    by (auto)
  
  lemma invar2_init_init: "prim_invar2_init initQ init\<pi>"
    unfolding prim_invar2_init_def by auto
    
  lemma invar2_init: "prim_invar2 initQ init\<pi>"
    unfolding prim_invar2_def using invar2_init_init by auto

  lemma maintain_invar2: 
    assumes A: "prim_invar2 Q \<pi>"  
    assumes UNS: "Q u = enat d"
    assumes MIN: "\<forall>v. enat d \<le> Q v"
    shows "prim_invar2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u)" (is ?G1)
      and "T_measure2 (Q' Q \<pi> u) (\<pi>' Q \<pi> u) < T_measure2 Q \<pi>" (is ?G2)
    using A unfolding prim_invar2_def
    using maintain_invar2_first_step[of Q,OF _ UNS]
    using maintain_invar2_ctd[OF _ UNS MIN]
    using not_invar2_ctd_init
    apply blast+
    done

  lemma invar2_ctd_finish:  
    assumes INV: "prim_invar2_ctd Q \<pi>"  
    assumes FIN: "Q = (\<lambda>_. \<infinity>)"
    shows "is_MST w rg (graph {r} {(u, v). \<pi> u = Some v})"
  proof -  
    from INV interpret Prim_Invar2_ctd_loc w g r Q \<pi> by unfold_locales
  
    let ?A = "A Q \<pi>" let ?S="S ?A"
    
    have FC: "edges g \<inter> ?S \<times> - ?S = {}" 
    proof (safe; simp)
      fix a b
      assume "(a,b)\<in>edges g" "a\<in>?S" "b\<notin>?S"
      with Q_defined[OF edges_sym'] S_edge_reachable have "Q b \<noteq> \<infinity>" 
        by blast
      with FIN show False by auto
    qed
    
    have Aeq: "?A = {(u, v). \<pi> u = Some v}"
      unfolding A_def using FIN by auto
    
    from invar1_finish[OF invar1 FC, unfolded Aeq] show ?thesis .
  qed
    
    
  lemma invar2_finish:  
    assumes INV: "prim_invar2 Q \<pi>"  
    assumes FIN: "Q = (\<lambda>_. \<infinity>)"
    shows "is_MST w rg (graph {r} {(u, v). \<pi> u = Some v})"
  proof -  
    from INV have "prim_invar2_ctd Q \<pi>"
      unfolding prim_invar2_def prim_invar2_init_def initQ_def
      by (auto simp: fun_eq_iff FIN split: if_splits)
    with FIN invar2_ctd_finish show ?thesis by blast  
  qed

  
  definition "min_Q_spec Q \<equiv> do {ASSERT (Q \<noteq> (\<lambda>_. \<infinity>)); SPEC (\<lambda>u. \<exists>d. Q u = enat d \<and> (\<forall>v. enat d \<le> Q v))}"
  definition "upd_Q\<pi>_spec u Q \<pi> \<equiv> (=) (Qinter Q \<pi> u, \<pi>' Q \<pi> u)"
  
  definition "prim2 \<equiv> WHILET 
    (\<lambda>(Q,\<pi>). Q \<noteq> (\<lambda>_. \<infinity>)) 
    (\<lambda>(Q,\<pi>). do { 
      u \<leftarrow> min_Q_spec Q; 
      (Q,\<pi>) \<leftarrow> SPEC (upd_Q\<pi>_spec u Q \<pi>);
      let Q = Q(u:=\<infinity>);
      RETURN (Q,\<pi>) 
    })
    (initQ,init\<pi>)
    "
  
  definition "p21_rel \<equiv> br (uncurry A) (uncurry prim_invar2_ctd)"
  
  lemma initQ_enat_iff[simp]: "initQ x = enat d \<longleftrightarrow> x=r \<and> d=0"
    by (auto simp: initQ_def zero_enat_def)
    
  lemma A_one_step_after_init: "A (Q' initQ init\<pi> r) (\<pi>' initQ init\<pi> r) = {}"  
    unfolding A_def initQ_def init\<pi>_def \<pi>'_def Q'_def Qinter_def upd_cond_def
    by auto
    
  
  lemma prim2_refine: "prim2 \<le>\<Down>p21_rel prim1"
  proof -
    have [simp]: "initQ \<noteq> (\<lambda>_. \<infinity>)" by (auto simp: initQ_def fun_eq_iff zero_enat_def)
  
    show ?thesis
      unfolding prim2_def prim1_def min_Q_spec_def upd_Q\<pi>_spec_def
      apply (simp add: Q'_def[symmetric])
      apply (rule WHILEIT_add_init_step)
      subgoal by (auto simp add: initQ_def fun_eq_iff zero_enat_def)
      subgoal 
        apply refine_vcg 
        apply (auto simp: p21_rel_def in_br_conv A_one_step_after_init
          invar2_init_init maintain_invar2_first_step(1)) 
        done  
      subgoal for s s'
        apply (cases s; simp)
        apply (clarsimp simp: p21_rel_def in_br_conv)
        apply (blast dest: Prim_Invar2_ctd_loc.Q_empty_iff_no_crossing_edges[OF Prim_Invar2_ctd_loc.intro])
        done
      subgoal
        apply (clarsimp simp: p21_rel_def in_br_conv pw_le_iff refine_pw_simps)
        by (metis Prim_Invar2_ctd_loc.Q_min_light_edge' Prim_Invar2_ctd_loc.intro insert_is_Un maintain_invar2_ctd(1))
      done
  qed    
  
  
  
    
end


subsection \<open>Refinement of Inner Foreach Loop\<close>

definition "mop_wgraph_adjs g w u \<equiv> SPEC (\<lambda>adjs. set adjs = {(v,d). (u,v)\<in>edges g \<and> w {u,v} = d})"


context Prim2 begin


  definition "upd_Q\<pi>_loop u Q \<pi> \<equiv> do {
    adjs \<leftarrow> mop_wgraph_adjs g w u;
    nfoldli adjs (\<lambda>_. True) (\<lambda>(v,d) (Q,\<pi>). do { 
      if v=r then RETURN (Q,\<pi>)
      else case (Q v, \<pi> v) of
        (\<infinity>,None) \<Rightarrow> RETURN (Q(v:=enat d), \<pi>(v\<mapsto>u))
      | (enat d',_) \<Rightarrow> if d<d' then RETURN (Q(v:=enat d), \<pi>(v\<mapsto>u)) else RETURN (Q,\<pi>)
      | (\<infinity>,Some _) \<Rightarrow> RETURN (Q,\<pi>)
    }) (Q,\<pi>)
  }"
  
    
  lemma Qinter_root[simp]: "Qinter Q \<pi> u r = Q r" by (auto simp: Qinter_def upd_cond_def)
  lemma \<pi>'_root[simp]: "\<pi>' Q \<pi> u r = \<pi> r" by (auto simp: \<pi>'_def upd_cond_def)
    
        
  lemma upd_Q\<pi>_loop_refine_auxp[refine_vcg]: "upd_Q\<pi>_loop u Q \<pi> \<le> SPEC (upd_Q\<pi>_spec u Q \<pi>)"
    unfolding upd_Q\<pi>_loop_def mop_wgraph_adjs_def
    apply (refine_vcg nfoldli_rule[where 
      I="(\<lambda>xs ys (Qh,\<pi>h). 
        Qh = combf (fst`set xs) (Qinter Q \<pi> u) Q    
      \<and> \<pi>h = combf (fst`set xs) (\<pi>' Q \<pi> u) \<pi>)
      "])
    apply (clarsimp_all simp: fun_upd_idem_iff' combf_def split del: if_split)
    subgoal by (auto)
    subgoal by (auto)
    subgoal for l1 l2 v d
      by (auto
        split!: enat.splits option.splits if_splits
        dest!: ins_eq_set_memD 
        simp: fun_upd_idem_iff' img_fst
        simp: Qinter_def \<pi>'_def upd_cond_def insert_commute 
        intro: edges_sym'
      )
    subgoal for l  
      by (auto simp: upd_Q\<pi>_spec_def Qinter_def \<pi>'_def fun_eq_iff combf_def upd_cond_def intro: edges_sym') 
    done

  definition "prim3 \<equiv> WHILET 
    (\<lambda>(Q,\<pi>). Q \<noteq> (\<lambda>_. \<infinity>)) 
    (\<lambda>(Q,\<pi>). do { 
      u \<leftarrow> min_Q_spec Q; 
      (Q,\<pi>) \<leftarrow> upd_Q\<pi>_loop u Q \<pi>;
      let Q = Q(u:=\<infinity>);
      RETURN (Q,\<pi>) 
    })
    (initQ,init\<pi>)
    "
    
  lemma prim3_refine: "prim3 \<le>\<Down>Id prim2"  
    unfolding prim3_def prim2_def
    apply (refine_vcg)
    apply refine_dref_type
    apply auto
    done

    
  definition "Qpm_rel \<equiv> Id \<rightarrow> br (\<lambda>None\<Rightarrow>\<infinity> | Some d \<Rightarrow> enat d) (\<lambda>_. True)"  

  find_theorems FOREACH nfoldli
  find_theorems LIST_FOREACH
  

  definition "upd_Q\<pi>_loop2 u Q \<pi> \<equiv> doN {
    adjs \<leftarrow> mop_wgraph_adjs g w u;
    nfoldli adjs (\<lambda>_. True) (\<lambda>(v,d) (Q,\<pi>). doN { 
      if v=r then RETURN (Q,\<pi>)
      else case (Q v, \<pi> v) of
        (None,None) \<Rightarrow> RETURN (Q(v\<mapsto>d), \<pi>(v\<mapsto>u))
      | (Some d',_) \<Rightarrow> if d<d' then RETURN (Q(v\<mapsto>d), \<pi>(v\<mapsto>u)) else RETURN (Q,\<pi>)
      | (None,Some _) \<Rightarrow> RETURN (Q,\<pi>)
    }) (Q,\<pi>)
  }"

  lemma Qpm_upd_refine: "(Qi,Q)\<in>Qpm_rel \<Longrightarrow> (Qi(x\<mapsto>d), Q(x:=enat d))\<in>Qpm_rel"
    apply (clarsimp simp: Qpm_rel_def in_br_conv split: option.split)
    subgoal for x
      apply (drule fun_relD[OF _ IdI[of x]])
      apply (auto simp: in_br_conv)
      done
    done
    
  lemma Qpm_None: "(Qi,Q)\<in>Qpm_rel \<Longrightarrow> Qi x = None \<longleftrightarrow> Q x = \<infinity>"  
    by (auto simp: Qpm_rel_def in_br_conv dest: fun_relD[OF _ IdI[of x]] split: option.splits)
  
  lemma Qpm_Some: "(Qi,Q)\<in>Qpm_rel \<Longrightarrow> Qi x = Some d \<longleftrightarrow> Q x = enat d"  
    by (auto simp: Qpm_rel_def in_br_conv dest: fun_relD[OF _ IdI[of x]] split: option.splits)

  lemma Qpm_empty: "(Map.empty, Q) \<in> Qpm_rel \<Longrightarrow> Q=(\<lambda>_. \<infinity>)"  
    apply (clarsimp simp: fun_eq_iff Qpm_rel_def)
    subgoal for x
      by (auto simp: in_br_conv dest: fun_relD[OF _ IdI[of x]] split: option.splits)
    done      
    
    
  lemma upd_Q\<pi>_loop2_refine[refine]: "\<lbrakk>(ui,u)\<in>Id; (Qi,Q)\<in>Qpm_rel; (\<pi>i,\<pi>)\<in>Id\<rbrakk> 
    \<Longrightarrow> upd_Q\<pi>_loop2 ui Qi \<pi>i \<le> \<Down>(Qpm_rel\<times>\<^sub>rId) (upd_Q\<pi>_loop u Q \<pi>)"
    unfolding upd_Q\<pi>_loop2_def upd_Q\<pi>_loop_def
    apply simp
    apply refine_rcg
    apply refine_dref_type
    by (auto 
      split: enat.splits if_splits option.splits
      simp: Qpm_None Qpm_Some
      intro: Qpm_upd_refine)


  definition "prim4 \<equiv> doN {
    let Q = op_map_update r 0 op_map_empty;
    WHILET 
      (\<lambda>(Q,\<pi>). \<not>op_map_is_empty Q) 
      (\<lambda>(Q,\<pi>). doN { 
        (u,_) \<leftarrow> mop_pm_peek_min id Q;
        (Q,\<pi>) \<leftarrow> upd_Q\<pi>_loop2 u Q \<pi>;
        Q \<leftarrow> mop_map_delete u Q;
        RETURN (Q,\<pi>) 
      })
      (Q,op_map_empty)
    }
    "

  lemma peek_min_refine: "(Qi,Q)\<in>Qpm_rel 
    \<Longrightarrow> mop_pm_peek_min id Qi \<le> \<Down> (br fst (\<lambda>_. True)) (min_Q_spec Q)"
    apply (auto simp: min_Q_spec_def pw_le_iff refine_pw_simps in_br_conv Qpm_empty Qpm_Some)
    by (metis enat_ile enat_ord_simps(1) linear)
    
  lemma Qpm_delete_refine: "\<lbrakk> (Qi,Q)\<in>Qpm_rel; (ki,k)\<in>Id \<rbrakk> \<Longrightarrow> mop_map_delete ki Qi
       \<le> SPEC (\<lambda>Qi'. (Qi', Q(k := \<infinity>))
                    \<in> Qpm_rel)"  
    apply (clarsimp simp: Qpm_rel_def in_br_conv split: option.split)
    subgoal for x
      apply (drule fun_relD[OF _ IdI[of x]])
      by (auto simp: in_br_conv)
    done
    
  lemma Qpm_init_refine: "([r \<mapsto> 0], initQ) \<in> Qpm_rel"  
    by (auto simp: Qpm_rel_def in_br_conv initQ_def zero_enat_def)
    
  lemma Qpm_is_empty_refine: "(Qi, Q) \<in> Qpm_rel 
    \<Longrightarrow> (Map.empty = Qi) = (Q = (\<lambda>_. \<infinity>))"  
    apply (clarsimp simp: Qpm_rel_def fun_eq_iff; safe)
    subgoal for x by (auto dest!: fun_relD[OF _ IdI[of x]] simp: in_br_conv)
    subgoal for x by (auto dest!: fun_relD[OF _ IdI[of x]] simp: in_br_conv split: option.splits)
    done
    
  lemma prim4_refine: "prim4 \<le> \<Down>(Qpm_rel\<times>\<^sub>rId) prim3"  
    unfolding prim4_def prim3_def
    apply (refine_rcg peek_min_refine Qpm_delete_refine)
    by (auto simp: Qpm_init_refine init\<pi>_def Qpm_is_empty_refine in_br_conv)
    
    
    
    
        
end

(* TODO: Move *)
subsection \<open>Doubleton Set to Pair\<close>
definition "epair e = (if card e = 2 then Some (SOME (u,v). e={u,v}) else None)"

lemma epair_eqD: "epair e = Some (x,y) \<Longrightarrow> (x\<noteq>y \<and> e={x,y})"
  apply (cases "card e = 2")
  unfolding epair_def
  apply simp_all
  apply (clarsimp simp: card_Suc_eq eval_nat_numeral doubleton_eq_iff)
  by (smt case_prodD case_prodI someI)
  
lemma epair_not_sng[simp]: "epair e \<noteq> Some (x,x)"  
  by (auto dest: epair_eqD)

lemma epair_None[simp]: "epair {a,b} = None \<longleftrightarrow> a=b" 
  unfolding epair_def by (auto simp: card2_eq) 

lemma epair_cases:
  obtains (edge) u v where "e={u,v}" "u\<noteq>v" "epair e = Some (u,v)"
        | (no_edge) "card e \<noteq> 2" "epair e = None"
  by (metis card2_eq epair_None epair_eqD not_Some_eq2)


type_synonym ('v,'w) wugraph1 = "'v \<Rightarrow> ('v\<rightharpoonup>'w)"

definition wu1_invar :: "('v,'w) wugraph1 \<Rightarrow> bool" 
  where "wu1_invar g1 \<equiv> 
      (\<forall>u. g1 u u = None) 
    \<and> (\<forall>u v w. g1 u v = Some w \<longrightarrow> g1 v u = Some w)
    \<and> finite { (u,v). g1 u v \<noteq> None }"
definition wu1_\<alpha>E :: "('v,'w) wugraph1 \<Rightarrow> ('v\<times>'v) set" where "wu1_\<alpha>E g1 \<equiv> { (u,v). g1 u v \<noteq> None }"
definition wu1_\<alpha>g :: "('v,'w) wugraph1 \<Rightarrow> 'v ugraph" where "wu1_\<alpha>g g1 \<equiv> graph {} (wu1_\<alpha>E g1)"

definition wu1_\<alpha>w :: "('v,'w::zero) wugraph1 \<Rightarrow> 'v set \<Rightarrow> 'w" where 
  "wu1_\<alpha>w g1 e \<equiv> case epair e of Some (u,v) \<Rightarrow> the_default 0 (g1 u v) | None \<Rightarrow> 0"

lemma wu1_invar_alt: "wu1_invar g1 \<equiv> 
      (\<forall>u. g1 u u = None) 
    \<and> (\<forall>u v w. g1 u v = Some w \<longrightarrow> g1 v u = Some w)
    \<and> finite (wu1_\<alpha>E g1)"  
  unfolding wu1_invar_def wu1_\<alpha>E_def by simp
  
definition wu1_empty :: "('v,'w) wugraph1" where "wu1_empty \<equiv> \<lambda>_ _. None"
definition wu1_ins_edge :: "'v\<times>'v \<Rightarrow> 'w \<Rightarrow> ('v,'w) wugraph1 \<Rightarrow> ('v,'w) wugraph1 nres"
  where "wu1_ins_edge \<equiv> \<lambda>(u,v) w g. doN {
    ASSERT (v \<notin> dom (g u));
    gu \<leftarrow> mop_map_update v w (g u);
    let g = g(u:=gu);
    ASSERT (u \<notin> dom (g v));
    gv \<leftarrow> mop_map_update u w (g v);
    let g = g(v:=gv);
    RETURN g
  }"
definition wu1_adjs :: "'v \<Rightarrow> ('v,'w) wugraph1 \<Rightarrow> ('v\<times>'w) list nres" 
  where "wu1_adjs u g1 \<equiv> SPEC (\<lambda>xs. distinct xs \<and> set xs = {(v,w). g1 u v = Some w})"
  

lemma wu1_empty_refine[simp]:
  "wu1_invar wu1_empty"  
  "wu1_\<alpha>g wu1_empty = graph_empty"
  "wu1_\<alpha>w wu1_empty = (\<lambda>_. 0)"
  by (auto 
    simp: wu1_invar_def wu1_empty_def wu1_\<alpha>g_def wu1_\<alpha>E_def wu1_\<alpha>w_def[abs_def]
    simp: fun_eq_iff split: option.splits
    )
  
lemma wu1_irrefl[simp]: "wu1_invar g \<Longrightarrow> g u u = None" by (auto simp: wu1_invar_def)
lemma wu1_sym: "wu1_invar g \<Longrightarrow> g u v = g v u" 
  apply (cases "g u v"; cases "g v u"; simp)
  unfolding wu1_invar_def
  apply (metis option.simps(3))
  apply (metis option.simps(3))
  apply (metis option.simps(1))
  done

lemma wu1_finite[simp, intro]: "wu1_invar g \<Longrightarrow> finite (wu1_\<alpha>E g)"
  unfolding wu1_invar_alt by auto
  
lemma wu1_edges_aux: "wu1_invar g \<Longrightarrow> edges (graph {} (wu1_\<alpha>E g)) = wu1_\<alpha>E g"
  apply (simp add: edges_graph)
  apply (auto simp: wu1_\<alpha>E_def wu1_sym)
  done
  
lemma wu1_edges_aux2: "wu1_invar g \<Longrightarrow> edges (wu1_\<alpha>g g) = wu1_\<alpha>E g"
  unfolding wu1_\<alpha>g_def by (simp add: wu1_edges_aux)

  
lemma wu1_\<alpha>E_ins_aux:
  assumes "wu1_invar g" "(u,v)\<notin>edges (wu1_\<alpha>g g)" "u\<noteq>v"
  shows "wu1_\<alpha>E (g(u := g u(v \<mapsto> w), v := g v(u \<mapsto> w))) = {(u,v),(v,u)} \<union> wu1_\<alpha>E g"  
  using assms
  unfolding wu1_\<alpha>g_def
  apply (simp add: wu1_edges_aux)
  unfolding wu1_\<alpha>E_def
  by (auto split!: if_splits)
  
  
lemma wu1_ins_edge_refine[simp]:
  assumes "wu1_invar g" "(u,v)\<notin>edges (wu1_\<alpha>g g)" "u\<noteq>v"
  shows "wu1_ins_edge (u,v) w g \<le> SPEC (\<lambda>g'. 
      wu1_invar g'
    \<and> wu1_\<alpha>g g' = ins_edge (u,v) (wu1_\<alpha>g g)
    \<and> wu1_\<alpha>w g' = (wu1_\<alpha>w g)({u,v}:=w)
  )"
  unfolding wu1_ins_edge_def
  apply (refine_vcg)
  apply (simp_all add: \<open>u\<noteq>v\<close>[symmetric] split: if_splits)
  apply (all \<open>(elim conjE)?;(hypsubst)?\<close>)
  
  subgoal 
    using assms(2)
    apply (auto simp: \<open>wu1_invar g\<close> wu1_edges_aux2)
    by (auto simp: wu1_\<alpha>E_def)
  subgoal 
    using assms(1) assms(3) wu1_sym by fastforce
  subgoal
    using \<open>u\<noteq>v\<close>
    unfolding wu1_invar_alt wu1_ins_edge_def
    by (auto simp: \<open>wu1_invar g\<close> wu1_sym wu1_\<alpha>E_ins_aux[OF assms(1-3)])
  subgoal
    unfolding wu1_\<alpha>g_def wu1_ins_edge_def
    apply (simp add: wu1_\<alpha>E_ins_aux[OF assms(1-3)])
    apply (rewrite graph_eq_iff; simp add: nodes_graph edges_graph edges_ins_edge \<open>wu1_invar g\<close>)
    by auto
  subgoal
    unfolding wu1_\<alpha>w_def wu1_ins_edge_def
    apply (rule ext)
    subgoal for e by (cases e rule: epair_cases) auto
    done
  done  

  
lemma wu1_adjs_refine:  
  assumes "wu1_invar g"
  shows "wu1_adjs u g \<le> mop_wgraph_adjs (wu1_\<alpha>g g) (wu1_\<alpha>w g) u"
  apply (simp add: wu1_edges_aux2[OF assms] wu1_adjs_def mop_wgraph_adjs_def)
  apply (auto simp: wu1_\<alpha>w_def wu1_\<alpha>E_def)
  apply (auto 
    split: option.split 
    simp: doubleton_eq_iff wu1_irrefl[OF assms] wu1_sym[OF assms]
    dest!: epair_eqD)
  done
  
(*      
lemma wu1_adjs_refine[simp]:  
  assumes "wu1_invar g"
  shows "wu1_adjs u g = {(v,wu1_\<alpha>w g {u,v}) | v. (u,v)\<in>edges (wu1_\<alpha>g g)}"
  apply (simp add: wu1_edges_aux2[OF assms] wu1_adjs_def)
  apply (auto simp: wu1_\<alpha>w_def wu1_\<alpha>E_def)
  apply (auto 
    split: option.split 
    simp: doubleton_eq_iff wu1_irrefl[OF assms] wu1_sym[OF assms]
    dest!: epair_eqD)
  done
*)  

type_synonym 'w wugraph2 = "(nat\<times>'w) list list"

definition wu2_invar :: "'w wugraph2 \<Rightarrow> bool" 
  where "wu2_invar xss \<equiv> 
    let N=length xss in 
      \<forall>xs\<in>set xss. distinct (map fst xs) \<and> fst`set xs \<subseteq> {0..<N}"

definition wu2_\<alpha> :: "'w wugraph2 \<Rightarrow> (nat,'w) wugraph1"
  where "wu2_\<alpha> xss \<equiv> \<lambda>u. if u<length xss then map_of (xss!u) else Map.empty"

definition wu2_empty :: "nat \<Rightarrow> 'w wugraph2" where "wu2_empty N \<equiv> replicate N []"
definition wu2_ins_edge :: "nat \<times> nat \<Rightarrow> 'w \<Rightarrow> 'w wugraph2 \<Rightarrow> 'w wugraph2 nres" where
  "wu2_ins_edge \<equiv> \<lambda>(u,v) w xss. doN {
    ASSERT (u<length xss \<and> length (xss!u) < length xss);
    xss \<leftarrow> mop_list_list_push_back xss u (v,w);
    ASSERT (v<length xss \<and> length (xss!v) < length xss);
    xss \<leftarrow> mop_list_list_push_back xss v (u,w);
    RETURN xss
  }"

definition wu2_adjs :: "nat \<Rightarrow> 'w wugraph2 \<Rightarrow> (nat\<times>'w) list nres" where
  "wu2_adjs u xss \<equiv> doN { ASSERT (u<length xss); RETURN (xss!u) }"
  
lemma wu2_empty_refine[simp]:
  "wu2_invar (wu2_empty N)"  
  "wu2_\<alpha> (wu2_empty N) = wu1_empty"
  unfolding wu2_invar_def wu2_empty_def wu2_\<alpha>_def wu1_empty_def
  by auto

(* TODO: Move *)  
lemma distinct_bounded_list_add_bound:
  assumes D: "distinct xs"  
  assumes SS: "set xs \<subseteq> {0..<N}"
  assumes NI: "x<N" "x\<notin>set xs"
  shows "length xs < N"
proof -
  from SS NI have "set xs \<subseteq> {0..<N} - {x}" by auto
  from card_mono[OF _ this] have "card (set xs) < N" using NI by auto
  with distinct_card[OF D] show ?thesis by simp
qed    
  
lemma wu2_ins_edge_bound_aux:
  assumes "wu2_invar xss" "u<length xss" "v<length xss" "wu2_\<alpha> xss u v = None"  
  shows "length (xss!u) < length xss"
proof -
  have "length (map fst (xss!u)) < length xss"
    apply (rule distinct_bounded_list_add_bound[OF _ _ \<open>v<length xss\<close>])
    using assms
    unfolding wu2_invar_def wu2_\<alpha>_def
    by auto
  thus ?thesis by auto
qed
  
lemma wu2_ins_edge_refine: 
  "\<lbrakk>(xss,g)\<in>br wu2_\<alpha> wu2_invar; u<length xss; v<length xss\<rbrakk> \<Longrightarrow> wu2_ins_edge (u,v) w xss \<le>\<Down>(br wu2_\<alpha> wu2_invar) (wu1_ins_edge (u,v) w g)"
  unfolding wu2_ins_edge_def wu1_ins_edge_def
  apply (auto simp: pw_le_iff refine_pw_simps in_br_conv intro: wu2_ins_edge_bound_aux)
  apply (auto 
    elim!: in_set_upd_cases 
    simp: map_add_find_left wu2_invar_def wu2_\<alpha>_def fun_eq_iff 
    split!: if_splits)
  subgoal
    by (meson atLeastLessThan_iff img_fst nth_mem subsetD)
  subgoal
    by (meson atLeastLessThan_iff img_fst nth_mem subsetD) 
  subgoal
    using atLeastLessThan_iff by blast
  done  
  
  
lemma wu2_adjs_refine:
  "\<lbrakk>(xss,g)\<in>br wu2_\<alpha> wu2_invar; u<length xss\<rbrakk> \<Longrightarrow> wu2_adjs u xss \<le> wu1_adjs u g"
  unfolding wu2_adjs_def wu1_adjs_def
  apply refine_vcg
  apply (clarsimp_all simp: pw_le_iff refine_pw_simps in_br_conv)
  apply (auto simp: wu2_invar_def wu1_adjs_def wu2_\<alpha>_def)
  using distinct_mapI nth_mem by blast
  
definition wu2_adjs_len :: "nat \<Rightarrow> 'w wugraph2 \<Rightarrow> nat nres" where
  "wu2_adjs_len u xss \<equiv> mop_list_list_llen xss u"
  
definition wu2_adjs_nth :: "nat \<Rightarrow> nat \<Rightarrow> 'w wugraph2 \<Rightarrow> (nat\<times>'w) nres" where
  "wu2_adjs_nth u i xss \<equiv> mop_list_list_idx xss u i"


definition "wu_rel N \<equiv> {(g2,(g,w)). let g1 = (wu2_\<alpha> g2) in g = wu1_\<alpha>g g1 \<and> w = wu1_\<alpha>w g1 \<and> wu1_invar g1 \<and> wu2_invar g2 \<and> length g2=N }"

lemma wu_empty_refine: "(wu2_empty N, (graph_empty, \<lambda>_. 0)) \<in> wu_rel N"
  apply (auto simp: wu_rel_def)
  by (simp add: wu2_empty_def)

lemma wu_ins_edge_refine: 
  assumes "(ui,u)\<in>Id" "(vi,v)\<in>Id" "(di,d)\<in>Id" "u<N" "v<N" "(g2,(g,w))\<in>wu_rel N"
  assumes "(u,v)\<notin>edges g" "u\<noteq>v"
  shows "wu2_ins_edge (ui,vi) di g2 \<le> \<Down>(wu_rel N) (RETURN (ins_edge (u,v) g, w({u,v}:=d)))"
  using assms
  using wu2_ins_edge_refine[of "g2" "wu2_\<alpha> g2" u v d] 
  using wu1_ins_edge_refine[of "wu2_\<alpha> g2" u v d]
  apply (auto simp: wu_rel_def pw_le_iff refine_pw_simps Let_def in_br_conv)
  apply (auto simp: wu2_ins_edge_def refine_pw_simps)
  done

  
lemma 
  assumes REL: "(g2,(g,w))\<in>wu_rel N"
  assumes PRE2: "u<N"
  shows "
  doN { num_adjs \<leftarrow> wu2_adjs_len u g2; nfoldli [0..<num_adjs] c (\<lambda>i s. doN { vd \<leftarrow> wu2_adjs_nth u i g2; f vd s }) s}
  \<le>
  doN { xs \<leftarrow> mop_wgraph_adjs g w u; nfoldli xs c f s }"  
  (is "?LHS \<le> ?RHS")
proof -
  from REL have [simp]: "g=wu1_\<alpha>g (wu2_\<alpha> g2)" "w=wu1_\<alpha>w (wu2_\<alpha> g2)" "N=length g2"
    by (auto simp: wu_rel_def Let_def)
  from wu1_adjs_refine[of "wu2_\<alpha> g2" u]
    and wu2_adjs_refine[of g2 "wu2_\<alpha> g2" u]
  have "RETURN (g2!u) \<le> mop_wgraph_adjs (wu1_\<alpha>g (wu2_\<alpha> g2)) (wu1_\<alpha>w (wu2_\<alpha> g2)) u"
    using REL PRE2
    by (auto 
      simp: in_br_conv wu2_adjs_len_def wu2_adjs_def 
      simp: wu_rel_def Let_def
      simp: pw_le_iff refine_pw_simps
      )
  hence "nfoldli [0..<length (g2!u)] c (\<lambda>i s. do {
                                    _ \<leftarrow> ASSERT (i < length (g2!u));
                                    let x = g2!u!i;
                                    f x s
                                  }) s \<le> ?RHS" (is "?INT1 \<le> _")
    apply (rewrite in "_ \<le> \<hole>" nfoldli_by_idx)
    by (auto simp: pw_le_iff refine_pw_simps)
  moreover have "?LHS \<le> ?INT1" using PRE2
    by (auto simp: wu2_adjs_len_def wu2_adjs_nth_def)
  ultimately show ?thesis by simp
qed
  
    
  
    
lemma 
  assumes EQ: "g = wu1_\<alpha>g (wu2_\<alpha> g2)" "w=wu1_\<alpha>w (wu2_\<alpha> g2)"
  assumes I: "wu1_invar (wu2_\<alpha> g2)" "wu2_invar g2"
  assumes PRE2: "u<length g2"
  shows "
  doN { num_adjs \<leftarrow> wu2_adjs_len u g2; nfoldli [0..<num_adjs] c (\<lambda>i s. doN { vd \<leftarrow> wu2_adjs_nth u i g2; f vd s }) s}
  \<le>
  doN { xs \<leftarrow> mop_wgraph_adjs g w u; nfoldli xs c f s }"  
  (is "?LHS \<le> ?RHS")
  proof -
    from wu1_adjs_refine[OF I(1), of u] wu2_adjs_refine[of g2 "wu2_\<alpha> g2", OF _ PRE2] I(2)
    have "RETURN (g2!u) \<le> mop_wgraph_adjs (wu1_\<alpha>g (wu2_\<alpha> g2)) (wu1_\<alpha>w (wu2_\<alpha> g2)) u"
      by (auto simp: in_br_conv wu2_adjs_len_def wu2_adjs_def pw_le_iff refine_pw_simps)
    hence "nfoldli [0..<length (g2!u)] c (\<lambda>i s. do {
                                      _ \<leftarrow> ASSERT (i < length (g2!u));
                                      let x = g2!u!i;
                                      f x s
                                    }) s \<le> ?RHS" (is "?INT1 \<le> _")
      apply (rewrite in "_ \<le> \<hole>" nfoldli_by_idx)
      by (auto simp: EQ pw_le_iff refine_pw_simps)
    moreover have "?LHS \<le> ?INT1"                                          
      by (auto simp: wu2_adjs_len_def PRE2 wu2_adjs_nth_def)
    ultimately show ?thesis by simp
  qed

  thm wu1_adjs_refine[OF I(1), of u] wu2_adjs_refine[of g2 "wu2_\<alpha> g2", OF _ PRE2] I(2)
    
  
  apply (rule bind_refine'[where R=Id and R'="{(l,xs). length xs = l}", simplified])
  subgoal
    using wu1_adjs_refine[OF I(1), of u] wu2_adjs_refine[of g2 "wu2_\<alpha> g2", OF _ PRE2] I(2)
    by (auto simp: in_br_conv wu2_adjs_len_def wu2_adjs_def pw_le_iff refine_pw_simps)
  subgoal for num_adjs adjs  
    thm nfoldli_mono
    apply clarsimp
    apply (rule nfoldli_mono)
    apply (clarsimp simp: wu2_adjs_nth_def PRE2 wu2_adjs_len_def)
    
    
    using wu2_adjs_refine[of g2 "wu2_\<alpha> g2", OF _ PRE2] I(2)
    apply (auto simp: pw_le_iff refine_pw_simps)
    
  done
  
  
    thm conc_trans
    find_theorems "\<Down>_" name: mono
  
  
    apply (auto simp: wu2_adjs_len_def)
  
  
  
  thm bind_refine[where R=Id, simplified]
  apply (rule bind_mono)
  
  thm wu1_adjs_refine[OF I(1)]
  
  
  oops
  xxx: Build prototype setoid rewriter!
  
  
  unfolding wu2_adjs_len_def
  
  find_theorems wu1_adjs
  find_theorems mop_wgraph_adjs
  
  
find_theorems nfoldli "[_..<_]"

thm nfoldli_by_idx  
  
  
oops  
    
xxx: Refine iteration over adjacent nodes by for-loop!
  
  
context 
  fixes VL :: "'vl::len2 itself"
  fixes WL :: "'wl::len2 itself"
begin  

  private abbreviation (input) "V_assn \<equiv> snat_assn' TYPE('vl)"
  private abbreviation (input) "W_assn \<equiv> snat_assn' TYPE('wl)"
  private abbreviation (input) "wu3_assn \<equiv> aal_assn' TYPE('vl) TYPE('vl) (V_assn \<times>\<^sub>a W_assn)"
  
  sepref_definition wu3_empty is "RETURN o wu2_empty" 
    :: "[\<lambda>_. 4<LENGTH('vl)]\<^sub>a (snat_assn' TYPE('vl))\<^sup>k \<rightarrow> wu3_assn"
    unfolding wu2_empty_def
    apply (rewrite aal_fold_custom_empty)
    by sepref
    
  sepref_definition wu3_ins_edge is "uncurry2 wu2_ins_edge" 
    :: "(V_assn \<times>\<^sub>a V_assn)\<^sup>k *\<^sub>a W_assn\<^sup>k *\<^sub>a wu3_assn\<^sup>d \<rightarrow>\<^sub>a wu3_assn"
    unfolding wu2_ins_edge_def
    supply [dest!] = rdomp_aal_assnD
    by sepref
    
  sepref_definition wu3_adjs_len is "uncurry wu2_adjs_len"  
    :: "V_assn\<^sup>k *\<^sub>a wu3_assn\<^sup>k \<rightarrow>\<^sub>a V_assn"
    unfolding wu2_adjs_len_def
    by sepref
    
  sepref_definition wu3_adjs_nth is "uncurry2 wu2_adjs_nth"  
    :: "V_assn\<^sup>k *\<^sub>a V_assn\<^sup>k *\<^sub>a wu3_assn\<^sup>k \<rightarrow>\<^sub>a V_assn\<times>\<^sub>aW_assn"
    unfolding wu2_adjs_nth_def
    by sepref
    
    
    find_theorems rdomp
    
    oops
    xxx: rdomp predicates, to infer length bounds on main list and sublists!
      We have done similar things for array-list already? Reuse!?
    
    oops
    xxx: Argument that there cannot be to many entries!
    
    
    
    
oops  
xxx, ctd here:
  Refine down to LLVM!
  Refine iteration by for-loop!
  
  
  

definition wu1_\<alpha>V :: "('w) wugraph1 \<Rightarrow> nat set"
  where "wu1_\<alpha>V xss \<equiv> fst`\<Union>(set`set xss)"

definition wu1_\<alpha>E :: "('w) wugraph1 \<Rightarrow> (nat\<times>nat) set" 
  where "wu1_\<alpha>E xss \<equiv> { (i,j). \<exists>w. i<length xss \<and> (j,w)\<in>set (xss!i) }"

definition "wu1_\<alpha>g xss \<equiv> graph (wu1_\<alpha>V xss) (wu1_\<alpha>E xss)"

definition wu1_\<alpha>w :: "'w::zero wugraph1 \<Rightarrow> nat\<times>nat \<Rightarrow> 'w" where "wu1_\<alpha>w xss \<equiv> \<lambda>(u,v). 
  if u<length xss then 
    the_default 0 (map_of (xss!u) v)
  else 0"

definition wu1_invar :: "'w::zero wugraph1 \<Rightarrow> bool" 
  where "wu1_invar xss \<equiv> let N=length xss in
    (\<forall>xs\<in>set xss. fst`set xs \<subseteq> {0..<N} \<and> distinct (map fst xs))
    (\<forall>u<length N. c\<notin>)"
  

definition wu1_empty :: "nat \<Rightarrow> _ wugraph1" where
  "wu1_empty N \<equiv> replicate N []"
        
(* TODO: Move *)  
lemma graph_eq_empty_iff[simp]: 
  "finite V \<Longrightarrow> finite E \<Longrightarrow> 
    (graph V E = graph_empty \<longleftrightarrow> V={} \<and> E={})
  \<and> (graph_empty = graph V E \<longleftrightarrow> V={} \<and> E={})"
  using graph_accs(1) by fastforce
  
lemma finite_wu1[simp,intro!]:
  "finite (wu1_\<alpha>V xss)" 
  "finite (wu1_\<alpha>E xss)"  
  unfolding wu1_\<alpha>V_def wu1_\<alpha>E_def
  subgoal by auto []
  apply (rule finite_subset[where B="{0..<length xss} \<times> fst`\<Union>(set`set xss)"])
    subgoal by force
    subgoal by simp
  done
  
  
lemma wu1_\<alpha>E_empty[simp]: "wu1_\<alpha>E (replicate N []) = {}"
  unfolding wu1_\<alpha>E_def by auto
  
lemma wu1_empty[simp]:
  "wu1_invar (wu1_empty N)"  
  "wu1_\<alpha>g (wu1_empty N) = graph_empty"
  "wu1_\<alpha>w (wu1_empty N) = (\<lambda>_. 0)"
  by (auto simp: wu1_empty_def wu1_invar_def wu1_\<alpha>g_def wu1_\<alpha>V_def wu1_\<alpha>w_def)
  
term ins_edge  
  
definition wu1_ins_edge :: "nat\<times>nat \<Rightarrow> 'w \<Rightarrow> 'w wugraph1 \<Rightarrow> 'w wugraph1 nres" where
  "wu1_ins_edge \<equiv> \<lambda>(u,v) w xss. 
    ASSERT (u<length xss \<and> v<length xss \<and> v\<notin>fst`set (xss!u))
    \<then> RETURN (xss[u:=(v,w)#xss!u])"
  
lemma 
  assumes INV: "wu1_invar xss"
  assumes PRE: "u<length xss" "v<length xss" "(u,v)\<notin>edges (wu1_\<alpha>g xss)" "u\<noteq>v"
  shows "wu1_ins_edge (u,v) w xss 
    \<le> SPEC (\<lambda>xss'. 
        wu1_invar xss' 
      \<and> wu1_\<alpha>g xss' = ins_edge (u,v) (wu1_\<alpha>g xss)
      \<and> wu1_\<alpha>w xss' = (wu1_\<alpha>w xss)((u,v):=w)
      )"  
  unfolding wu1_ins_edge_def    
  apply refine_vcg
  apply (clarsimp_all simp: assms)
  subgoal using PRE
    apply (simp add: wu1_\<alpha>g_def edges_graph)
    apply (auto simp: wu1_\<alpha>E_def)
    done
  subgoal using INV PRE  
    apply (auto simp: wu1_invar_def)
    subgoal
      by (smt atLeastLessThan_iff fst_conv img_fst in_set_upd_cases list.set_cases list_tail_coinc nth_mem subsetD)
    subgoal
      by (metis (no_types, lifting) distinct.simps(2) fst_conv image_set in_set_upd_eq list.simps(9) nth_mem)
    done
  subgoal
    apply (subst graph_eq_iff; clarsimp)
    apply (auto simp: wu1_\<alpha>g_def)
    xxx: Add irrefl to invariant, this gives better simp-lemmas!
    
    
    find_theorems "edges (graph _ _)"
  
  
   sorry
  subgoal  sorry
  subgoal  sorry
  subgoal  sorry


end
