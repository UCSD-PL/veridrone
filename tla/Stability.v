Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import TLA.Morphisms.
Require Import TLA.BasicProofRules.
Require Import ChargeTactics.Lemmas.


Open Scope HP_scope.

Notation "x <> y" := (Imp (Comp x y Eq) FALSE) : HP_scope.

Definition Abs (x : Term) : Term :=
  MAX(x,--x).

Definition Term_continuous_at (t:Term) (x:Var) (r:R)
  : Formula :=
  Forall e : R, e > 0 -->>
  Exists d : R, d > 0 //\\
  Exists tr : R, (x = r -->> t = tr) //\\
    (Abs (x - r) < d -->> Abs (t - tr) < e).

Lemma deriv_term_continuous :
  forall t t' x,
    deriv_term t = Some t' ->
    forall r, |-- Term_continuous_at t x r.
Admitted.

Lemma Exists_with_st : forall G P (t : Term),
    (forall x : R, G |-- t = x -->> P x) ->
    G |-- Exists x : R, P x.
Proof.
  breakAbstraction.
  intros.
  specialize (H _ tr H0 eq_refl).
  eexists. eauto.
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
    G |-- Forall a : R, a > 0 -->>
          Exists b : R, b > 0 //\\
            (Abs x < b -->> []Abs x < a).
Proof.
  intros x V V' cp G HstV Hderiv Hcp HVx
         Hcont HV' HVpos HVeq.
  tlaAssert (Exists V0 : R, V = V0 //\\ []V <= V0).
  { apply Exists_with_st with (t:=V). intro V0.
    charge_intros. charge_split; [ charge_assumption | ].
    rewrite Hcont. eapply discr_indX.
     tlaIntuition.
    - charge_assumption.
    - solve_linear.
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
  apply forget_prem. charge_intros. rewrite landexistsDL.
  apply lexistsL. intro V0.
  assert ((exists Vp : R, |-- x = x0 -->> V = Vp) /\
          (exists Vn : R, |-- x = --x0 -->> V = Vn)).
  { admit. }
  destruct H as [[Vp HVp] [Vn HVn]].
  pose proof (deriv_term_continuous _ _ x Hderiv 0%R)
    as HcontV.
  unfold Term_continuous_at in HcontV.
  match type of HcontV with
  | |-- ?G => tlaAssert G;
             [ charge_tauto |
               clear HcontV; charge_intros ]
  end.
  rewrite landC. rewrite landforallDL.
  apply (lforallL (Rbasic_fun.Rmin Vp Vn)).
  apply limplL.
  { unfold Rbasic_fun.Rmin. destruct_ite.
    { reason_action_tac.
      specialize (HVpos (Stream.forever
                           (fun v =>
                              if String.string_dec x v
                              then x0 else R0))).
      specialize (HVp (Stream.forever
                         (fun v =>
                            if String.string_dec x v
                            then x0 else R0))).
      simpl in *.
      destruct (String.string_dec x x); try congruence.
      specialize_arith_hyp HVpos.
      specialize_arith_hyp HVp. solve_linear. }
    { reason_action_tac.
      specialize (HVpos (Stream.forever
                           (fun v =>
                              if String.string_dec x v
                              then (-x0)%R else R0))).
      specialize (HVn (Stream.forever
                         (fun v =>
                            if String.string_dec x v
                            then (-x0)%R else R0))).
      simpl in *.
      destruct (String.string_dec x x); try congruence.
      specialize_arith_hyp HVpos.
      specialize_arith_hyp HVn. solve_linear. } }
  rewrite landexistsDL. apply lexistsL. intro d.
  apply (lexistsR d). charge_split; [ charge_assumption | ].
  charge_intros.
  eapply discr_indX.
  - tlaIntuition.
  - charge_tauto.
(*
  apply (lforallL x0).
  apply limplL; [ charge_tauto | ].
  rewrite landexistsDL.
  apply lexistsL. intro d.
  apply (lexistsR d). charge_split.
  - charge_assumption.
  - charge_intros. rewrite Hcont.
    repeat rewrite landA. repeat rewrite landexistsDL.
    rewrite landC. rewrite landexistsDL.
    apply lexistsL. intro V0.
    eapply discr_indX.
    + tlaIntuition.
    + charge_assumption.
    + 
    + rewrite Lemmas.land_lor_distr_R. apply lorL.
      * tlaAssert (Exists v

eapply diff_ind with (Hyps:=TRUE).
        { tlaIntuition. }
        { tlaIntuition. }
        { charge_assumption. }
        { assumption. }
        { charge_tauto. }
        { charge_assumption. }
        { restoreAbstraction. charge_tauto. }
        { 
      * reason_action_tac. destruct H.
        rewrite H0. auto.
*)
Admitted.

Lemma lyapunov_fun_asymptotic_stability :
  forall (x:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula),
    deriv_term V = Some V' ->
    G |-- [](Continuous cp \\// x! = x) ->
      |-- Forall st', cp st' -->> x <> 0 -->> V' st' < 0 ->
      |-- Forall st', cp st' -->> x = 0 -->> V' st' = 0 ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- Forall e : R, <>[]Abs x < e.
Admitted.

Lemma lyapunov_fun_exponential_stability :
  forall (x t:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula) (a:R),
    (a > 0)%R ->
    deriv_term V = Some V' ->
    (forall st', |-- cp st' -->> st' t = 1) ->
    G |-- [](Continuous cp \\// (x! = x //\\ t! = t)) ->
      |-- Forall st', cp st' -->> V' st' < --a*V ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- Exists x0 : R, x = x0 //\\
          Exists M : R, M > 0 //\\
            []Abs x <= M * Abs x0 * exp(--(a/2) * t).
Admitted.