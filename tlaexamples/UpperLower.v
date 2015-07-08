Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.EnabledLemmas.
Require Import Examples.System.
Require Import Examples.UpperLowerSecond.
Require Import Examples.UpperLowerFirst.
Require Import ChargeTactics.Lemmas.
Require Import BasicProofRules.

Module Type UpperLowerParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.
  Parameter ubv : R.
  Axiom ubv_gt_amin_d : (ubv >= -amin*d)%R.
  Parameter ub_ubv :
    (ubv*d - ubv*ubv*(/2)*(/amin) <= ub)%R.
End UpperLowerParams.

Module UpperLower (P : UpperLowerParams).

  Module Y <: UpperLowerSecondParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv.
    Definition ub_ubv := P.ub_ubv.
  End Y.

  Module V <: UpperLowerFirstParams.
    Definition ub := P.ubv.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End V.

  Module Position := UpperLowerSecond Y.
  Module Vel := UpperLowerFirst V.

  Definition SpecR :=
    SysCompose Vel.SpecR Position.SpecR.

  Lemma safety :
    |-- PartialSysD SpecR -->>
        [](Vel.Safe //\\ Position.Safe).
  Proof.
    apply PartialCompose.
    - apply Vel.UpperLower_safe.
    - rewrite landtrueL. unfold Vel.Safe.
      rewrite <- Always_and.
      charge_apply Position.UpperLower_safe.
      repeat rewrite Always_and. tlaRevert.
      apply always_imp. solve_linear.
  Qed.

  Definition Constraint :=
    P.amin <= "a" <= --P.amin.

  Lemma Prog_constrained_enabled :
    |-- Enabled (SpecR.(Prog) //\\ next Constraint).
  Proof.
    simpl. restoreAbstraction.
    enable_ex_st.
    pose proof P.amin_lt_0. pose proof P.d_gt_0.
    pose proof P.ubv_gt_amin_d.
    unfold Vel.V.ub, Vel.V.d, V.ub, V.d.
    unfold Position.Params.amin.
    unfold Y.amin.
    destruct (RIneq.Rgt_dec (st "y") R0);
    destruct (RIneq.Rgt_dec (st "v") R0).
    { exists P.amin.
      smart_repeat_eexists. solve_linear. }
    { smart_repeat_eexists. solve_linear. }
    { smart_repeat_eexists. solve_linear. }
    { exists (-P.amin)%R.
      smart_repeat_eexists. solve_linear. }
  Qed.

  Lemma Prog_enabled :
    |-- Enabled SpecR.(Prog).
  Proof.
    etransitivity.
    { apply Prog_constrained_enabled. }
    { rewrite Enabled_and. charge_assumption. }
  Qed.

  Lemma UpperLower_enabled :
    |-- Enabled (Discr SpecR.(Prog) SpecR.(maxTime)).
  Proof.
    unfold Discr.
    rewrite <- disjoint_state_enabled.
    { charge_split.
      { apply Prog_enabled. }
      { enable_ex_st. smart_repeat_eexists. solve_linear. } }
    { apply formulas_disjoint_state; reflexivity. }
  Qed.

  Lemma UpperLower_full :
    |-- SysSafe SpecR.
  Proof.
    apply SysSafe_rule. apply always_tauto.
    apply UpperLower_enabled.
  Qed.

End UpperLower.