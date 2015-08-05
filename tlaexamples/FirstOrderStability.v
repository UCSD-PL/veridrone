Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import Examples.DiffEqSolutions.
Require Import Coq.Lists.List.

Open Scope HP_scope.
Open Scope string_scope.

Module Type Params.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

End Params.

Module Stability (Import P : Params).

  Definition Abs (x : Term) : Term :=
    MAX(x,--x).

  Definition ExponentiallyStable : Formula :=
    Exists y0 : R, "y" = y0 //\\
    Exists a : R, a > 0 //\\
    Exists b : R, b > 0 //\\
      []Abs "y" <= a * Abs y0 * exp(--b * "t").

  Definition World : Evolution :=
    fun st' =>
      st' "y" = "v" //\\ st' "t" = 1 //\\
      st' "v" = 0 //\\ st' "T" = 0.

  Definition Ctrl (v : Term) : Formula :=
    v = --"y"/d.

  Definition Next : Formula :=
    (Continuous World //\\ "t"! - "T"! < d) \\//
    (Ctrl "v"! //\\ "T"! = "t" //\\
     Unchanged ("t"::"y"::nil)).

  Definition Init : Formula :=
    "t" = 0 //\\ "T" = "t" //\\ Ctrl "v".

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition AbstractNext : Formula :=
    "y"! = "y"*(d + "T"! - "t"!)/(d + "T"! - "t") //\\
    "t"! >= "t".

  Lemma abstraction :
    Spec |-- Init //\\ []AbstractNext.
  Proof.
    tlaAssert ([]"v" = --"y"/(d + "T" - "t")).
    - eapply discr_indX.
      + tlaIntuition.
      + charge_assumption.
      + solve_linear. rewrite H0. rewrite H. rewrite H3.
        rewrite_real_zeros. solve_linear.
      + unfold Next. rewrite Lemmas.land_lor_distr_R.
        apply lorL.
        * zero_deriv_tac "v".
          zero_deriv_tac "T".
          assert (evolution_entails World sgl_int)
            by (red; red; solve_linear).
          rewrite H. clear H. rewrite solve_sgl.
          reason_action_tac. intuition.
          rewrite H1 in *. rewrite H2 in *. rewrite H3 in *.
          rewrite H0 in *. clear H1 H2 H3 H0.
          admit. (* z3 accepts this one *)
        * solve_linear. rewrite H1. rewrite H2. rewrite H3.
          rewrite H. admit. (* z3 accepts this one *)
    - charge_intros. charge_split; [ charge_assumption | ].
      unfold Spec. rewrite landA. rewrite Always_and.
      always_imp_tac. charge_intros.
      unfold Next. rewrite Lemmas.land_lor_distr_R.
      apply lorL.
      + zero_deriv_tac "T".
        assert (evolution_entails World sgl_int)
            by (red; red; solve_linear).
        rewrite H. clear H. rewrite solve_sgl.
        solve_linear.
        rewrite H1 in *. rewrite H2.
        admit. (* z3 solves this one *)
      + solve_linear. rewrite H1. rewrite H2. rewrite H3.
        pose proof d_gt_0. admit. (* z3 solves this *)
  Qed.

  Theorem exp_stability :
    |-- Spec -->> ExponentiallyStable.
  Proof.
    charge_intros. rewrite abstraction.
    apply Exists_with_st with (t:="y").
    intro y0. charge_intros.
    charge_split; [ solve_linear | ].
    apply lexistsR with (x:=1%R).
    charge_split; [ solve_linear | ].
    apply lexistsR with (x:=(1/d)%R).
    charge_split;
      [ pose proof d_gt_0; solve_linear;
        assert (/d > 0)%R by solve_linear;
        solve_linear | ].
    eapply discr_indX.
    - tlaIntuition.
    - charge_assumption.
    - breakAbstraction. intuition.
      rewrite H0. repeat rewrite_real_zeros.
      rewrite Rtrigo_def.exp_0. subst.
      solve_linear.
    - reason_action_tac. intuition.
      rewrite H. clear H.
  Admitted.

End Stability.