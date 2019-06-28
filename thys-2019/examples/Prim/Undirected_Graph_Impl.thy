theory Undirected_Graph_Impl
imports 
  Undirected_Graph 
  "../../sepref/IICF/IICF"
  "../../sepref/IICF/Impl/IICF_Array_of_Array_List"
begin


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
  
  
  (* TODO: Move *)
  lemma card2_eq: "card e = 2 \<longleftrightarrow> (\<exists>u v. u\<noteq>v \<and> e={u,v})"
    by (auto simp: eval_nat_numeral card_Suc_eq)
  
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

  
  
  
definition "mop_wgraph_adjs g w u \<equiv> SPEC (\<lambda>adjs. set adjs = {(v,d). (u,v)\<in>edges g \<and> w {u,v} = d})"
  

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
  
definition wu2_max :: "'w wugraph2 \<Rightarrow> nat" where [simp]: "wu2_max xss \<equiv> length xss"
  
lemma wu2_empty_refine[simp]:
  "wu2_invar (wu2_empty N)"  
  "wu2_\<alpha> (wu2_empty N) = wu1_empty"
  unfolding wu2_invar_def wu2_empty_def wu2_\<alpha>_def wu1_empty_def
  by auto

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
  "wu2_adjs_nth u i xss \<equiv> ASSERT (wu2_invar xss) \<then> mop_list_list_idx xss u i"


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

  
lemma iterate_adjs_refine_aux:
  assumes REL: "(g2,(g,w))\<in>wu_rel N"
  assumes PRE2: "u<N"
  shows "
  doN { num_adjs \<leftarrow> wu2_adjs_len u g2; nfoldli [0..<num_adjs] c (\<lambda>i s. doN { vd \<leftarrow> wu2_adjs_nth u i g2; f vd s }) s}
  \<le>
  doN { xs \<leftarrow> mop_wgraph_adjs g w u; nfoldli xs c f s }"  
  (is "?LHS \<le> ?RHS")
proof -
  from REL have [simp]: "g=wu1_\<alpha>g (wu2_\<alpha> g2)" "w=wu1_\<alpha>w (wu2_\<alpha> g2)" "N=length g2" "wu2_invar g2"
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

thm nfoldli_refine[of l l Id for l, simplified]

lemma iterate_adjs_refine:
  assumes REL: "(g2,(g,w))\<in>wu_rel N"
  assumes PRE2: "u<N"
  assumes REL2: "(si,s)\<in>R" "(ci,c)\<in>R \<rightarrow> bool_rel" 
      and RELF: "\<And>u si s. \<lbrakk> (si,s)\<in>R; c s \<rbrakk> \<Longrightarrow> fi u si \<le>\<Down>R (f u s)"
  shows "
  doN { num_adjs \<leftarrow> wu2_adjs_len u g2; nfoldli [0..<num_adjs] ci (\<lambda>i s. doN { vd \<leftarrow> wu2_adjs_nth u i g2; fi vd s }) si}
  \<le>\<Down>R (
  doN { xs \<leftarrow> mop_wgraph_adjs g w u; nfoldli xs c f s })"  
proof -
  note R = nfoldli_refine[of l l Id for l, simplified, OF REL2, of fi f]

  show ?thesis
    apply (rule order_trans[OF _ bind_refine[OF Id_refine], rotated])
    apply simp
    apply (rule R)
    subgoal using RELF by blast
    subgoal by (rule iterate_adjs_refine_aux[OF REL PRE2])
    done
    
qed    
  
type_synonym ('vl,'wl) wu3 = "('vl,'vl word \<times> 'wl word,'vl) array_array_list"


definition "wu_constrain_len_rel N \<equiv> b_rel Id (\<lambda>xss. length xss=N)"
  
lemma wu2_empty_clen_refine: "(wu2_empty, wu2_empty)\<in>nat_rel \<rightarrow>\<^sub>f\<^sub>d wu_constrain_len_rel"
  apply rule
  by (auto simp: wu_constrain_len_rel_def wu2_empty_def)

lemma wu2_ins_edge_clen_refine: 
  "(wu2_ins_edge, wu2_ins_edge) \<in> nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id \<rightarrow> wu_constrain_len_rel N \<rightarrow> \<langle>wu_constrain_len_rel N\<rangle>nres_rel"  
  unfolding wu2_ins_edge_def wu_constrain_len_rel_def
  by (auto simp: pw_nres_rel_iff refine_pw_simps)

lemma wu2_adjs_len_clen_refine: "(wu2_adjs_len, wu2_adjs_len) \<in> nat_rel \<rightarrow> wu_constrain_len_rel N \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
  unfolding wu_constrain_len_rel_def
  by (auto intro!: nres_relI)

lemma wu2_adjs_nth_clen_refine: "(wu2_adjs_nth,wu2_adjs_nth) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> wu_constrain_len_rel N \<rightarrow> \<langle>nat_rel \<times>\<^sub>r Id\<rangle>nres_rel"
  unfolding wu_constrain_len_rel_def
  by (auto intro!: nres_relI)

lemma wu2_max_clen_refine: "(wu2_max, wu2_max)\<in>wu_constrain_len_rel N \<rightarrow> nat_rel"  
  unfolding wu_constrain_len_rel_def
  by (auto intro!: nres_relI)
      
  
context 
  fixes VL :: "'vl::len2 itself"
  fixes WL :: "'wl::len2 itself"
begin  

  private abbreviation (input) "V_assn \<equiv> snat_assn' TYPE('vl)"
  private abbreviation (input) "W_assn \<equiv> snat_assn' TYPE('wl)"
  definition wu3_assn :: "_ \<Rightarrow> ('vl,'wl) wu3 \<Rightarrow> assn"
    where "wu3_assn \<equiv> aal_assn' TYPE('vl) TYPE('vl) (V_assn \<times>\<^sub>a W_assn)"
  
  definition "wu_assn N = hr_comp local.wu3_assn (wu_constrain_len_rel N)"
    
  sepref_register wu2_empty wu2_ins_edge wu2_adjs_len wu2_adjs_nth
  

  context 
    notes [fcomp_norm_unfold] = wu_assn_def[symmetric]
  begin
    
    sepref_definition wu3_empty [llvm_code,llvm_inline] is "RETURN o wu2_empty" 
      :: "[\<lambda>_. 4<LENGTH('vl)]\<^sub>a (snat_assn' TYPE('vl))\<^sup>k \<rightarrow> wu3_assn"
      unfolding wu2_empty_def wu3_assn_def
      apply (rewrite aal_fold_custom_empty)
      by sepref
      
    lemmas [sepref_fr_rules] = wu3_empty.refine[FCOMP wu2_empty_clen_refine]
      
    
    sepref_definition wu3_ins_edge [llvm_code,llvm_inline] is "uncurry2 wu2_ins_edge" 
      :: "(V_assn \<times>\<^sub>a V_assn)\<^sup>k *\<^sub>a W_assn\<^sup>k *\<^sub>a wu3_assn\<^sup>d \<rightarrow>\<^sub>a wu3_assn"
      unfolding wu2_ins_edge_def wu3_assn_def
      supply [dest!] = rdomp_aal_assnD
      by sepref
      
    lemmas [sepref_fr_rules] = wu3_ins_edge.refine[FCOMP wu2_ins_edge_clen_refine]  
  
    sepref_definition wu3_max [llvm_code,llvm_inline] is "RETURN o wu2_max" :: "wu3_assn\<^sup>k \<rightarrow>\<^sub>a V_assn"
      unfolding wu2_max_def wu3_assn_def
      apply (rewrite op_list_list_len_def[symmetric]) (* TODO: list_list is a proper subtype of list. So share operations! *)
      by sepref
    lemmas [sepref_fr_rules] = wu3_max.refine[FCOMP wu2_max_clen_refine]
        
    sepref_definition wu3_adjs_len [llvm_code,llvm_inline] is "uncurry wu2_adjs_len"  
      :: "V_assn\<^sup>k *\<^sub>a wu3_assn\<^sup>k \<rightarrow>\<^sub>a V_assn"
      unfolding wu2_adjs_len_def wu3_assn_def
      by sepref
    lemmas [sepref_fr_rules] = wu3_adjs_len.refine[FCOMP wu2_adjs_len_clen_refine]  
      
    sepref_definition wu3_adjs_nth [llvm_code,llvm_inline] is "uncurry2 wu2_adjs_nth"  
      :: "V_assn\<^sup>k *\<^sub>a V_assn\<^sup>k *\<^sub>a wu3_assn\<^sup>k \<rightarrow>\<^sub>a V_assn\<times>\<^sub>aW_assn"
      unfolding wu2_adjs_nth_def wu3_assn_def
      by sepref
    lemmas [sepref_fr_rules] = wu3_adjs_nth.refine[FCOMP wu2_adjs_nth_clen_refine]  
  end
end    

abbreviation wu_assn' :: "'vl::len2 itself \<Rightarrow> 'wl::len2 itself \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('vl,'wl) wu3 \<Rightarrow> assn"
  where "wu_assn' _ _ \<equiv> wu_assn"


end
