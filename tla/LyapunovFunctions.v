Require Import TLA.TLA.
Require Import TLA.Stability.
Require Import TLA.ProofRules.
Require Import TLA.Morphisms.
Require Import TLA.BasicProofRules.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Reals.Rdefinitions.
Require Import Rbasic_fun.
Require Import Ranalysis1.

Open Scope HP_scope.

Notation "x <> y" := (Imp (Comp x y Eq) FALSE) : HP_scope.

Definition Term_to_fun (t:Term) (x:Var) (s:state): R -> R :=
  fun r =>
    eval_term t (fun y => if String.string_dec x y
                          then r else R0) s.

Definition Term_continuous (t:Term) (x:Var)
  : Prop :=
  forall s, Ranalysis1.continuity (Term_to_fun t x s).

Lemma deriv_term_continuous :
  forall t t' x,
    deriv_term t = Some t' ->
    Term_continuous t x.
Proof.
  intros.
  pose proof term_deriv as Hderiv.
  unfold Term_continuous, Term_to_fun.
  intros.
  apply derivable_continuous.
  specialize
    (Hderiv (fun r y => if String.string_dec x y then r else 0%R)
            t t' R0).
  match type of Hderiv with
  | forall (_:?H), _ => assert H as Hderivable
  end.
  { intros. destruct (String.string_dec x x0).
    - apply derivable_id.
    - apply derivable_const. }
  specialize (Hderiv Hderivable s H).
  destruct Hderiv. assumption.
Qed.

Lemma lower_PropF :
  forall P P' G C,
    G |-- P ->
    (P |-- PropF P') ->
    (P' -> G |-- C) ->
    G |-- C.
Proof.
  breakAbstraction. eauto.
Qed.

Lemma lift_PropF :
  forall P P' G C,
    (PropF P' |-- P) ->
    P' ->
    G //\\ P |-- C ->
    G |-- C.
Proof.
  breakAbstraction. eauto.
Qed.

Lemma continuous_strengthen :
  forall G H cp,
    is_st_formula H ->
    G |-- Continuous cp ->
    G |-- H ->
    H //\\ Continuous cp |-- next H ->
    G |-- Continuous (fun st' => cp st' //\\ H).
Proof.
  breakAbstraction. intros.
  specialize (H1 _ H4).
  destruct H1 as [r [f [? [Hsol ?]]]].
  exists r. exists f.
  repeat split; try tauto.
  unfold is_solution, solves_diffeqs in *.
  simpl in *. destruct Hsol as [pf Hsol].
  exists pf. intros. split.
  - auto.
  - destruct H6. destruct H6.
    { specialize (H3 (Stream.Cons (Stream.hd tr)
                                  (Stream.forever (f z)))).
      rewrite next_formula_tl in H3; auto. simpl in *.
      apply H3. split.
      + eapply st_formula_hd; eauto.
      + exists z. exists f.
        repeat split.
        * solve_linear.
        * exists pf. intros. apply Hsol; solve_linear.
        * tauto. }
    { subst. eapply st_formula_hd; eauto. simpl.
      intuition congruence. }
Qed.

Lemma Ropp_eq_0 :
  forall r,
    (r = -r ->
     r = 0)%R.
Proof.
  solve_linear.
Qed.

Lemma lyapunov_fun_stability :
  forall (x:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula),
    is_st_term V = true ->
    deriv_term V = Some V' ->
    (forall st', is_st_formula (cp st')) ->
    x! = x |-- next_term V = V ->
    G |-- [](Continuous cp \\// x! = x) ->
      |-- Forall st', cp st' -->> V' st' <= 0 ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- LyapunovStable x.
Proof.
  unfold LyapunovStable.
  intros x V V' cp G HstV Hderiv Hcp HVx
         Hcont HV' HVpos HVeq.
  assert (forall st1 st2 st3 st4,
                       st1 x = st2 x ->
                       eval_term V st1 st3 =
                       eval_term V st2 st4) as HVx_hd.
            { intros. specialize (HVx (Stream.Cons st1 (Stream.forever st2))).
              simpl in *. erewrite next_term_tl in HVx; auto.
              rewrite HVx; [ | congruence ]. apply st_term_hd; auto. }
  tlaAssert (Exists x0 : R, x = x0 //\\
                          []V <= Term_to_fun V x (fun _ => R0) x0).
  { apply Exists_with_st with (t:=x). intro x0.
    charge_intros. charge_split; [ charge_assumption | ].
    rewrite Hcont. eapply discr_indX.
    - tlaIntuition.
    - charge_assumption.
    - unfold Term_to_fun. breakAbstraction. intros.
      specialize
        (HVx (Stream.Cons
                (Stream.hd tr)
                (Stream.Cons (fun y => if String.string_dec x y
                                       then x0 else R0) tr))).
      simpl in *.
      rewrite eval_next_term with (s3:=fun _ => R0) in HVx; auto.
      unfold Var, Value in *. rewrite HVx.
      + right. apply st_term_hd; auto.
      + destruct (String.string_dec x x); intuition congruence.
    - rewrite Lemmas.land_lor_distr_R. apply lorL.
      + eapply diff_ind with (Hyps:=TRUE).
        { tlaIntuition. }
        { tlaIntuition. }
        { charge_assumption. }
        { assumption. }
        { charge_tauto. }
        { charge_assumption. }
        { restoreAbstraction. charge_tauto. }
        { simpl deriv_formula. rewrite Hderiv.
          restoreAbstraction. auto. }
      + rewrite HVx. solve_linear. }
  charge_intros. rewrite landA. rewrite landexistsDL.
  rewrite landC. rewrite landexistsDL.
  apply lexistsL. intro xi.
  apply lower_PropF with (P:=x0 > 0) (P':=(x0 > 0)%R);
    [ charge_tauto | solve_linear | intro ].
  tlaAssert ([](Continuous
               (fun st' =>
                  cp st'
                     //\\ V <= Term_to_fun V x (fun _ => R0) xi)
                     \\// x! = x)).
  { rewrite Hcont. repeat rewrite landA.
    tlaRevert. apply forget_prem. charge_intros.
    rewrite landC. repeat rewrite landA.
    rewrite Always_and. tlaRevert. apply forget_prem.
    apply always_imp. charge_intros. rewrite land_lor_distr_R.
    apply lorL.
    - apply lorR1. apply continuous_strengthen.
      + tlaIntuition.
      + charge_assumption.
      + charge_assumption.
      + eapply diff_ind with (Hyps:=TRUE).
        { tlaIntuition. }
        { tlaIntuition. }
        { charge_assumption. }
        { assumption. }
        { charge_tauto. }
        { charge_assumption. }
        { restoreAbstraction. charge_tauto. }
        { simpl deriv_formula. rewrite Hderiv.
          restoreAbstraction. auto. }
    - charge_tauto. }
  
  charge_intros.
  pose proof (deriv_term_continuous _ _ x Hderiv (fun _ => R0))
    as HcontV.
  unfold Term_continuous, Term_to_fun, continuity, continuity_pt,
    continue_in, limit1_in, limit_in, R_met, Rfunctions.R_dist
    in HcontV.
  simpl in *. restoreAbstraction.
  specialize
    (HcontV R0 (Rmin
                  (Term_to_fun V x (fun _ => R0) x0)
                  (Term_to_fun V x (fun _ => R0) (-x0)%R))).
  match type of HcontV with
  | ?H -> _ => assert H as HcontV_prem
  end.
  { unfold Rmin. destruct_ite.
    { specialize
        (HVpos
           (Stream.Cons (fun v =>
                           if String.string_dec x v
                           then x0 else R0)
                        (Stream.forever (fun _ => R0)))).
      simpl in *.
      destruct (String.string_dec x x); try congruence.
      apply HVpos; solve_linear. }
    { specialize
        (HVpos
           (Stream.Cons (fun v =>
                           if String.string_dec x v
                           then (-x0)%R else R0)
                        (Stream.forever (fun _ => R0)))).
      simpl in *.
      destruct (String.string_dec x x); try congruence.
      apply HVpos; solve_linear. } }
  specialize (HcontV HcontV_prem). clear HcontV_prem.
  destruct HcontV as [d HcontV].
  apply lift_PropF with (P:=d > 0) (P':=(d > 0)%R);
    [ solve_linear | intuition | ].
  apply (lexistsR d). charge_split; [ charge_assumption | ].
  charge_intros.
  apply lower_PropF with (P:=Abs xi < d) (P':=(Rabs xi < d)%R);
    [ breakAbstraction; intuition; subst; auto |
      solve_linear; unfold Rabs, Rmax in *;
      destruct (Rcase_abs xi); destruct (RIneq.Rle_dec xi (0 - xi)); solve_linear |
      intro ].
  do 3 tlaRevert. apply forget_prem. charge_intros.
  eapply discr_indX.
  - tlaIntuition.
  - charge_assumption.
  - destruct (RIneq.Rlt_dec x0 d).
    + destruct HcontV as [? HcontV].
      specialize (HcontV x0).
      unfold D_x, no_cond in *.
      rewrite Rabs_pos_eq in HcontV; [ | solve_linear ].
      specialize_arith_hyp HcontV.
      unfold Term_to_fun, Rmin in *.
      apply Rabs_def2 in HcontV.
      revert HcontV. destruct_ite; intros;
      specialize
        (HVeq
           (Stream.Cons (fun y =>
                           if String.string_dec x y
                           then R0 else R0)
                        (Stream.forever (fun _ => R0))));
      simpl in *;
      unfold Var, Value in *; rewrite HVeq in HcontV;
      solve_linear;
      destruct (String.string_dec x x); reflexivity.
    + solve_linear.
  - clear - HstV HcontV HVeq HVpos HVx_hd H0 H. reason_action_tac.
    destruct H1 as [[Hcont | Hdiscr] Hpre].
    + destruct Hcont as [r [f [Hr [Hsol [Hf_pre Hf_post]]]]].
      cut (~(Rmax (post x) (0 - post x) >= x0)%R);
        [ solve_linear | ].
      intro. unfold is_solution, solves_diffeqs in *.
      destruct Hsol as [pf Hsol]. simpl in *.
      assert (forall x, continuity (fun r => f r x))
        as Hf_cont by (intros; apply derivable_continuous; auto).
      assert (exists z, 0 <= z <= r
                        /\ (eq (f z x) x0 \/ eq (f z x) (-x0)))%R as HIVT.
      { destruct H1.
        { pose proof (Rsqrt_def.IVT (fun r => Rabs (f r x) - x0) 0%R r)%R as IVT.
          assert (continuity (fun r => Rabs (f r x) - x0))%R.
          { apply continuity_minus.
            { apply continuity_comp with (f2:=Rabs); auto.
              apply Ranalysis4.Rcontinuity_abs. }
            { apply continuity_const. unfold constant. reflexivity. } }
          simpl in *.
          assert (Rabs (f 0 x) - x0 < 0)%R.
          { rewrite Hf_pre.
            revert Hpre. rewrite RIneq.Rminus_0_l.
            unfold Rmax. destruct_ite; intros.
            { destruct r0.
              { rewrite Rabs_left; solve_linear. }
              { assert (eq (pre x) R0).
                apply Ropp_eq_0; auto.
                rewrite H4. rewrite Rabs_R0. solve_linear. } }
            { rewrite Rabs_right; solve_linear. } }
          assert (0 < Rabs (f r x) - x0)%R.
          { rewrite Hf_post.
            revert H1. rewrite RIneq.Rminus_0_l.
            unfold Rmax. destruct_ite; intros.
            { destruct r0.
              { rewrite Rabs_left; solve_linear. }
              { assert (eq (post x) R0).
                apply Ropp_eq_0; auto.
                rewrite H5. rewrite Rabs_R0. solve_linear. } }
            { rewrite Rabs_right; solve_linear. } }
        specialize_arith_hyp IVT. destruct IVT as [z IVT].
          exists z. split; [ tauto | ].
          destruct (RIneq.Rge_dec (f z x) R0).
          { left. rewrite Rabs_right in IVT; solve_linear. }
          { right. rewrite Rabs_left in IVT; solve_linear.
            apply RIneq.Rplus_opp_r_uniq. solve_linear. } }
        { exists r. split; [ solve_linear | ].
          revert H1. unfold Rmax. rewrite Hf_post.
          destruct_ite; intros.
          { right. rewrite RIneq.Rminus_0_l in *.
            apply RIneq.Rplus_opp_r_uniq. solve_linear. }
          { solve_linear. } } }
      unfold Term_to_fun in *. destruct HIVT as [z [Hz HIVT]].
      specialize (Hsol _ Hz). destruct Hsol as [Hsol_cp HsolV].
      destruct HcontV as [Hd HcontV].
      destruct (RIneq.Req_dec xi R0).
      * subst xi.
        specialize (HVpos (Stream.forever (f z))).
        specialize
          (HVeq (Stream.Cons (fun y : Var => if String.string_dec x y then 0 else 0)
                             (Stream.forever (fun _ : Var => 0)))%R).
        simpl in *. destruct (String.string_dec x x); try congruence.
        specialize_arith_hyp HVeq.
        assert (f z x <> R0).
        { clear - H HIVT. destruct HIVT as [HIVT | HIVT]; rewrite HIVT in *.
          - intro Hneq; rewrite Hneq in *; solve_linear.
          - apply RIneq.Ropp_neq_0_compat.
            intro Hneq; rewrite Hneq in *; solve_linear. }
        specialize_arith_hyp HVpos. unfold Var, Value in *.
        rewrite HVeq in *. solve_linear.
      * specialize (HcontV xi). rewrite RIneq.Rminus_0_r in HcontV.
        unfold D_x, no_cond in *. specialize_arith_hyp HcontV.
        destruct HIVT as [HIVT | HIVT].
        { assert (eq (eval_term V (f z) (f z))
                     (eval_term V
                                (fun y => if String.string_dec x y then x0 else R0)
                                (fun _ => R0))) as HVz.
          { apply HVx_hd. destruct_ite; congruence. }
          rewrite HVz in HsolV.
          assert (eq (eval_term V (fun y : Var => if String.string_dec x y then R0 else R0)
                                (fun _ : Var => R0)) R0) as HV0.
          { specialize (HVeq (Stream.Cons (fun y : Var => if String.string_dec x y then 0%R else 0%R)
                                           (Stream.forever (fun _ : Var => 0%R)))).
            simpl in *. apply HVeq; auto. destruct_ite; reflexivity. }
          rewrite HV0 in HcontV. rewrite RIneq.Rminus_0_r in HcontV.
          rewrite Rabs_pos_eq in HcontV.
          { pose proof (RIneq.Rlt_le_trans _ _ _ HcontV (Rmin_l _ _)).
            solve_linear. }
          { specialize (HVpos (Stream.Cons (fun y : Var => if String.string_dec x y then xi else 0%R)
                                           (Stream.forever (fun _ : Var => 0%R)))).
            simpl in *. destruct (String.string_dec x x); try congruence.
            solve_linear. } }
        { assert (eq (eval_term V (f z) (f z))
                     (eval_term V
                                (fun y => if String.string_dec x y then (-x0)%R else R0)
                                (fun _ => R0))) as HVz.
          { apply HVx_hd. destruct_ite; congruence. }
          rewrite HVz in HsolV.
          assert (eq (eval_term V (fun y : Var => if String.string_dec x y then R0 else R0)
                                (fun _ : Var => R0)) R0) as HV0.
          { specialize (HVeq (Stream.Cons (fun y : Var => if String.string_dec x y then 0%R else 0%R)
                                           (Stream.forever (fun _ : Var => 0%R)))).
            simpl in *. apply HVeq; auto. destruct_ite; reflexivity. }
          rewrite HV0 in HcontV. rewrite RIneq.Rminus_0_r in HcontV.
          rewrite Rabs_pos_eq in HcontV.
          { pose proof (RIneq.Rlt_le_trans _ _ _ HcontV (Rmin_r _ _)).
            solve_linear. }
          { specialize (HVpos (Stream.Cons (fun y : Var => if String.string_dec x y then xi else 0%R)
                                           (Stream.forever (fun _ : Var => 0%R)))).
            simpl in *. destruct (String.string_dec x x); try congruence.
            solve_linear. } }
    + congruence.
Qed.

Lemma lyapunov_fun_asymptotic_stability :
  forall (x:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula),
    deriv_term V = Some V' ->
    G |-- [](Continuous cp \\// x! = x) ->
      |-- Forall st', cp st' -->> x <> 0 -->> V' st' < 0 ->
      |-- Forall st', cp st' -->> x = 0 -->> V' st' = 0 ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- AsymptoticallyStable x.
Admitted.

Lemma lyapunov_fun_exponential_stability :
  forall (x t:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula) (a:R),
    (a > 0)%R ->
    deriv_term V = Some V' ->
    (forall st', is_st_formula (cp st')) ->
    (forall st', |-- cp st' -->> st' t = 1) ->
    G |-- [](Continuous cp \\// (x! = x //\\ t! = t)) ->
      |-- Forall st', cp st' -->> V' st' < --a*V ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- ExponentiallyStable a x t.
Admitted.