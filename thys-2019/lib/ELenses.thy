theory ELenses
imports Lenses
begin

  (* TODO: We could use (\<lambda>_::unit. undefined) to realize a 'default' lifting operation
    from plain lenses to elenses.

    For lifting optionals to elenses, we could use a default type class.

    Then, we could define coercions to do the lifting automatically!
  *)

  definition "lift f m \<equiv> case m of None \<Rightarrow> Inl f | Some x \<Rightarrow> Inr x"
  definition "lower m \<equiv> case m of Inl _ \<Rightarrow> None | Inr x \<Rightarrow> Some x"

  definition "pre m \<equiv> case m of Inl e \<Rightarrow> Some e | _ \<Rightarrow> None"

  lemma pre_simps[simp]: "pre (Inr x) = None" "pre (Inl l) = Some l"
    by (auto simp: pre_def split: sum.splits)

  lemma pre_eq_conv[simp]:
    "pre m = None \<longleftrightarrow> (\<exists>r. m = Inr r)"
    "pre m = Some l \<longleftrightarrow> (m = Inl l)"
    by (auto simp: pre_def split: sum.splits)



  lemma lift_simps[simp]:
    "lift f (None) = Inl f"
    "lift f (Some x) = Inr x"
    by (auto simp: lift_def)

  lemma lift_invert[simp]:
    "lift f m = Inr x \<longleftrightarrow> m=Some x"
    "lift f m = Inl f' \<longleftrightarrow> f'=f \<and> m=None"
    unfolding lift_def
    by (auto split: option.splits)

  lemma lower_simps[simp]:
    "lower (Inl f) = None"
    "lower (Inr x) = Some x"
    by (auto simp: lower_def)

  lemma lower_invert[simp]:
    "lower m = None \<longleftrightarrow> (\<exists>f. m = Inl f)"
    "lower m = Some x \<longleftrightarrow> m = Inr x"
    by (auto simp: lower_def split: sum.splits)

  lemma lower_lift_id[simp]: "lower (lift f m) = m"
    by (auto simp: lower_def lift_def split: option.split)




  datatype ('a,'b,'e) elens = ELENS (eget: "'a \<Rightarrow> 'e + 'b") (eput: "'b \<Rightarrow> 'a \<Rightarrow> 'e+'a")


  lemma sum_eqI[intro?]:
    assumes "\<And>l. s = Inl l \<longleftrightarrow> s'=Inl l"
    assumes "\<And>r. s = Inr r \<longleftrightarrow> s'=Inr r"
    shows "s=s'"
    apply (cases s; cases s'; simp)
    using assms by auto

  lemma elens_eqI[intro?]:
    assumes "\<And>s x. eget L s = Inr x \<longleftrightarrow> eget L' s = Inr x"
    assumes "\<And>s x. eget L s = Inl x \<longleftrightarrow> eget L' s = Inl x"
    assumes "\<And>x s s'. eput L x s = Inr s' \<longleftrightarrow> eput L' x s = Inr s'"
    assumes "\<And>x s f. eput L x s = Inl f \<longleftrightarrow> eput L' x s = Inl f"
    shows "L = L'"
    apply (cases L; cases L'; simp)
    apply (intro conjI ext sum_eqI)
    using assms by simp_all


  definition "lift_get f g s \<equiv> lift f (g s)"
  definition "lift_put f p x s \<equiv> lift f (p x s)"
  definition "lift_lens f L \<equiv> ELENS (lift_get f (get L)) (lift_put f (put L))"

  definition "lower_get g s \<equiv> lower (g s)"
  definition "lower_put p x s \<equiv> lower (p x s)"
  definition "lower_lens L \<equiv> LENS (lower_get (eget L)) (lower_put (eput L))"

  lemma lower_lift_gp_id[simp]:
    "lower_get (lift_get f g) = g"
    "lower_put (lift_put f p) = p"
    by (auto
      del: ext intro!: ext
      simp: lower_get_def lift_get_def lower_put_def lift_put_def)

  lemma lower_lift_lens_id[simp]:
    "lower_lens (lift_lens f L) = L"
    by (cases L) (auto simp: lower_lens_def lift_lens_def)


  abbreviation "eget' L \<equiv> get' (lower_lens L)"
  abbreviation "eput' L \<equiv> put' (lower_lens L)"

  definition "epre_get L s \<equiv> pre (eget L s)"
  definition "epre_put L x s \<equiv> pre (eput L x s)"

  (*
  abbreviation "epre_get L \<equiv> pre_get (lower_lens L)"
  abbreviation "epre_put L \<equiv> pre_put (lower_lens L)"
  abbreviation "epre_put_single_point L \<equiv> pre_put_single_point (lower_lens L)"
  *)

  abbreviation "elens L \<equiv> lens (lower_lens L)"
  definition "ehlens L \<equiv> hlens (lower_lens L) \<and> (\<forall>x s f. eput L x s = Inl f \<longleftrightarrow> eget L s = Inl f)"

  lemma ehlens_imp_hlens[simp]: "ehlens L \<Longrightarrow> hlens (lower_lens L)"
    by (auto simp: ehlens_def)

  lemma ehlens_put_Inl_conv[simp]: "ehlens L \<Longrightarrow> eput L x s = Inl f \<longleftrightarrow> eget L s = Inl f"
    by (auto simp: ehlens_def)

  (* TODO: Is reducing to optionals actually the best way? *)
  lemma lower_epre_get[simp]: "epre_get L s = None \<Longrightarrow> pre_get (lower_lens L) s"
    by (auto simp: epre_get_def lower_lens_def lower_get_def)

  lemma lower_epre_put[simp]: "epre_put L x s = None \<Longrightarrow> pre_put_single_point (lower_lens L) x s"
    by (auto simp: epre_put_def lower_lens_def lower_put_def pre_put_single_point_def)

  lemma lower_epre_put'[simp]: "elens L \<Longrightarrow> epre_put L x s = None \<Longrightarrow> pre_put (lower_lens L) s"
    by (meson lower_epre_put pre_put_single_point)

  lemma eget_rewrite1[simp]: "epre_get L s = None \<Longrightarrow> eget L s = Inr (eget' L s)"
    apply (auto simp: epre_get_def)
    by (simp add: lower_get_def lower_lens_def)

  lemma eget_rewrite2[simp]: "eget L s = Inr x \<longleftrightarrow> epre_get L s = None \<and> x = eget' L s"
    by (auto simp: epre_get_def lower_get_def lower_lens_def)

  lemma eget_nopre_conv[simp]: "eget L s = Inl e \<longleftrightarrow> epre_get L s = Some e"
    unfolding epre_get_def
    by (auto)

  lemma eput_rewrite1[simp]: "epre_put L x s = None \<Longrightarrow> eput L x s = Inr (eput' L x s)"
    apply (auto simp: epre_put_def)
    by (simp add: lower_put_def lower_lens_def)

  lemma eput_rewrite2[simp]: "eput L x s = Inr s' \<longleftrightarrow> epre_put L x s = None \<and> s' = eput' L x s"
    by (auto simp: epre_put_def lower_put_def lower_lens_def)

  lemma eput_nopre_conv[simp]: "eput L x s = Inl e \<longleftrightarrow> epre_put L x s = Some e"
    unfolding epre_put_def
    by (auto simp: )

  lemma epre_get_imp_pre_put[simp]:
    "elens L \<Longrightarrow> epre_get L s = None \<Longrightarrow> epre_put L x s = None"
    unfolding epre_get_def epre_put_def
    apply (auto)
    by (smt LENS_downstage(2) epre_get_def epre_put_def lens.pre_get_imp_putI lift_simps(1) lower_epre_get lower_lens_def lower_lift_id lower_put_def option.exhaust pre_eq_conv(2))

  lemma epre_get_lift_conv[simp]:
    "epre_get (lift_lens e L) s = None \<longleftrightarrow> pre_get L s"
    "epre_get (lift_lens e L) s = Some e' \<longleftrightarrow> e'=e \<and> \<not>pre_get L s"
    by (auto simp: epre_get_def lift_lens_def lift_get_def pre_get_def)

  lemma epre_put_lift_conv[simp]:
    "epre_put (lift_lens e L) x s = None \<longleftrightarrow> pre_put_single_point L x s"
    "epre_put (lift_lens e L) x s = Some e' \<longleftrightarrow> e'=e \<and> \<not>pre_put_single_point L x s"
    by (auto simp: epre_put_def lift_lens_def lift_put_def pre_put_single_point_def)

  lemma ehlens_lift[simp]: "ehlens (lift_lens f L) \<longleftrightarrow> hlens L"
    unfolding ehlens_def
    apply auto
    done

  lemma ehlens_pre_put_conv[simp]: "ehlens L \<Longrightarrow> epre_put L x s = epre_get L s"
    unfolding ehlens_def
    apply auto
    by (metis option.exhaust)



  lemmas [simp] = epre_get_def[symmetric]
  lemma epre_get_ELENS[simp]: "epre_get (ELENS g p) s = pre (g s)"
    by (auto simp: epre_get_def)

  lemmas [simp] = epre_put_def[symmetric]
  lemma epre_put_ELENS[simp]: "epre_put (ELENS g p) x s = pre (p x s)"
    by (auto simp: epre_put_def)






  definition ebcomp :: "('a, 'b, 'f) elens \<Rightarrow> ('b, 'c, 'f) elens \<Rightarrow> ('a, 'c, 'f) elens"
    (infixl "\<bullet>" 80)
    where "ebcomp L1 L2 \<equiv> ELENS
      (\<lambda>s. case eget L1 s of Inl r \<Rightarrow> Inl r | Inr s \<Rightarrow> eget L2 s)
      (\<lambda>x s. case eget L1 s of Inl r \<Rightarrow> Inl r | Inr s' \<Rightarrow>
             (case eput L2 x s' of Inl r \<Rightarrow> Inl r | Inr s' \<Rightarrow> eput L1 s' s))
    "

  lemma ebcomp_assoc[simp]: "L1\<bullet>(L2\<bullet>L3) = L1\<bullet>L2\<bullet>L3"
    apply (cases L1; cases L2; cases L3; simp)
    unfolding ebcomp_def
    apply (auto split: sum.splits del: ext intro!: ext)
    done

  lemma ebcomp_lower[simp]: "lower_lens (L1 \<bullet> L2) = lower_lens L1 \<bullet>\<^sub>L lower_lens L2"
    apply (cases L1; cases L2; simp)
    unfolding ebcomp_def lower_lens_def comp\<^sub>L_def lower_get_def lower_put_def
    apply (auto split: sum.splits Option.bind_splits del: ext intro!: ext)
    done

  lemma ebcomp_elens[simp]: "elens L1 \<Longrightarrow> elens L2 \<Longrightarrow> elens (L1 \<bullet> L2)"
    by (simp)



  lemma ebcomp_pre_get[simp]: "epre_get (L1 \<bullet> L2) s = (case epre_get L1 s of
      None \<Rightarrow> epre_get L2 (eget' L1 s)
    | Some e \<Rightarrow> Some e)"
    by (auto simp: ebcomp_def split: option.splits sum.splits)

  lemma ebcomp_pre_put[simp]: "elens L1 \<Longrightarrow> epre_put (L1 \<bullet> L2) x s = (case epre_get L1 s of
      None \<Rightarrow> epre_put L2 x (eget' L1 s)
    | Some e \<Rightarrow> Some e)"
    by (auto simp: ebcomp_def split: option.splits sum.splits)

  lemma ebcomp_get'[simp]: "\<lbrakk>elens L1; elens L2; epre_get L1 s = None; epre_get L2 (eget' L1 s) = None\<rbrakk>
    \<Longrightarrow> eget' (L1 \<bullet> L2) s = eget' L2 (eget' L1 s)"
    by (auto)

  lemma ebcomp_put'[simp]: "\<lbrakk>elens L1; elens L2; epre_get L1 s = None; epre_put L2 x (eget' L1 s) = None\<rbrakk>
    \<Longrightarrow> eput' (L1 \<bullet> L2) x s =  eput' L1 (eput' L2 x (eget' L1 s)) s"
    by (auto)

  definition "eid\<^sub>L \<equiv> ELENS (Inr) (\<lambda>x _. Inr x)"

  lemma lift_id\<^sub>L[simp]: "lift_lens f id\<^sub>L = eid\<^sub>L"
    unfolding lift_lens_def eid\<^sub>L_def lift_get_def lift_put_def
    by (auto del: ext intro!: ext)

  lemma lower_eid\<^sub>L[simp]: "lower_lens eid\<^sub>L = id\<^sub>L"
    unfolding lower_lens_def id\<^sub>L_def eid\<^sub>L_def lower_get_def lower_put_def
    by (auto del: ext intro!: ext)

  lemma eget_eid\<^sub>L_Inl_conv[simp]: "eget eid\<^sub>L s \<noteq> Inl f"
    by (auto simp: eid\<^sub>L_def)

  lemma eput_eid\<^sub>L_Inl_conv[simp]: "eput eid\<^sub>L x s \<noteq> Inl f"
    by (auto simp: eid\<^sub>L_def)

  lemma eid\<^sub>L_pre[simp]: "epre_get eid\<^sub>L s = None" "epre_put eid\<^sub>L x s = None"
    by (auto simp: eid\<^sub>L_def)

  lemma eid_left_neutral[simp]:
    assumes [simp]: "elens L"
    shows
    "eid\<^sub>L \<bullet> L = L"
    by (rule elens_eqI; auto split: option.splits)

  lemma eid_right_neutral[simp]:
    assumes [simp]: "ehlens L"
    shows
    "L \<bullet> eid\<^sub>L = L"
    by (rule elens_eqI; auto split: option.splits)



hide_const (open) lift lower pre

end
