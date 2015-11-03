Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.BasicProofRules.
Require Import TLA.Stability.
Require Import TLA.LyapunovFunctions.
Require Import TLA.ArithFacts.
Require Import Coq.Lists.List.
Require Import Examples.DiffEqSolutions.

Open Scope HP_scope.
Open Scope string_scope.

Module Type Params.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

End Params.

Module Stability (Import P : Params).

  Definition Abs (x : Term) : Term :=
    MAX(x,--x).

  Definition World : Evolution :=
    fun st' =>
      st' "y" = "v" //\\ st' "t" = 1 //\\
      st' "v" = 0 //\\ st' "T" = 0 //\\ "t" - "T" < d.

  Definition Ctrl (v : Term) : Formula :=
    v = --"y"/d.

  Definition Next : Formula :=
    Continuous World \\//
   (Ctrl "v"! //\\ "T"! = "t" //\\
    Unchanged ("t"::"y"::nil)).

  Definition Init : Formula :=
    "t" = 0 //\\ "T" = "t" //\\ Ctrl "v".

  Definition Spec : Formula :=
    Init //\\ []Next.

  Definition AbstractWorld : Evolution :=
    fun st' =>
      st' "y" = --"y"/(d + "T" - "t") //\\  st' "t" = 1 //\\
      st' "T" = 0 //\\ "t" - "T" < d.

  Definition AbstractNext : Formula :=
    Continuous AbstractWorld \\// "T"! = "t" //\\
    Unchanged ("t"::"y"::nil).

  Definition velocity_formula : Formula :=
    "v" = --"y"/(d + "T" - "t").

  Lemma world_abstraction_ind :
    velocity_formula //\\ Continuous World |--
    next velocity_formula.
  Proof.
    zero_deriv_tac "v".
    zero_deriv_tac "T".
    tlaAssert ("t"! - "T"! < d).
    { rewrite ContinuousProofRules.Continuous_st_formula
      with (F:="t"-"T" < d).
      - simpl next. restoreAbstraction. charge_assumption.
      - tlaIntuition.
      - tlaIntuition.
      - solve_linear. }
    assert (evolution_entails World sgl_int)
      by (red; red; solve_linear).
    rewrite H. clear H. rewrite solve_sgl.
    reason_action_tac. intuition.
    rewrite H1 in *. rewrite H2 in *. rewrite H3 in *.
    rewrite H in *. clear H1 H2 H H3.
    z3_solve; admit.
  Qed.

  Lemma abstraction :
    Spec |-- Init //\\ []AbstractNext.
  Proof.
    tlaAssert ([]velocity_formula).
    - eapply discr_indX.
      + tlaIntuition.
      + charge_assumption.
      + solve_linear. rewrite H0. rewrite H. rewrite H3.
        rewrite_real_zeros. solve_linear.
      + unfold Next. rewrite Lemmas.land_lor_distr_R.
        apply lorL.
        * apply world_abstraction_ind.
        * solve_linear. rewrite H1. rewrite H2. rewrite H3.
          rewrite H. z3_solve; admit.
    - charge_intros.
      charge_split.
      + charge_tauto.
      + tlaRevert. tlaRevert. apply Lemmas.forget_prem.
        charge_intros. rewrite Always_and.
        tlaRevert. apply Always_imp. charge_intros.
        unfold Next. rewrite Lemmas.land_lor_distr_R.
        apply lorL.
        * apply lorR1.
          eapply Lemmas.lcut.
          apply continuous_strengthen with (H:=velocity_formula).
          { tlaIntuition. }
          { charge_assumption. }
          { charge_assumption. }
          { apply world_abstraction_ind. }
          { apply Lemmas.forget_prem.
            charge_intros. apply Proper_Continuous_entails.
            red. red. red. solve_linear. }
        * apply lorR2.
          charge_tauto.
  Qed.

  Theorem lyapunov_stability :
    |-- Spec -->> LyapunovStable "y".
  Proof.
    charge_intros.
    apply Lemmas.lcut with (R:=Init //\\ []AbstractNext).
    { apply abstraction. }
    apply Lemmas.forget_prem. charge_intros.
    apply lyapunov_fun_stability
    with (V:="y"*"y") (V':=fun st' => st' "y"*"y" + "y"*st' "y")
                      (cp:=AbstractWorld).
    - reflexivity.
    - reflexivity.
    - tlaIntuition.
    - breakAbstraction. intros. congruence.
    - tlaRevert. apply Lemmas.forget_prem.
      apply Always_imp. charge_intros.
      apply lorL.
      + charge_tauto.
      + apply lorR2. simpl Unchanged. restoreAbstraction.
        charge_assumption.
    - breakAbstraction. intros. z3_solve; admit.
    - breakAbstraction. intros.
      apply RIneq.Rlt_gt.
      apply RIneq.Rlt_0_sqr.
      assumption.
    - solve_linear.
  Qed.

End Stability.