Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import TLA.EnabledLemmas.
Require Import TLA.DifferentialInduction.
Require Import Examples.System.
Require Import Examples.FirstDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import BasicProofRules.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module Type UpperLowerFirstParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
End UpperLowerFirstParams.

Module UpperLowerFirst (P : UpperLowerFirstParams).
  Module V <: FirstDerivShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End V.

  Module Vel := FirstDerivShim V.

  Let mirror :=
    ("v",--"v")::("a",--"a")::nil.

  Definition SpecVelocityMirrorR :
    { x : SysRec &
          SysRec_equiv
            (SysRename
               (to_RenameMap mirror)
               (deriv_term_RenameList mirror)
               Vel.SpecR)
            x}.
  Proof.
    discharge_sysrec_equiv_rename.
  Defined.

  Definition SpecR :=
    SysCompose (projT1 SpecVelocityMirrorR) Vel.SpecR.

  Definition Safe : Formula :=
    --P.ub <= "v" <= P.ub.

  Lemma UpperLower_safe :
    |-- PartialSysD SpecR -->> []Safe.
  Proof.
    apply PartialCompose.
    - charge_intros.
      rewrite_rename_pf SpecVelocityMirrorR.
      rewrite PartialSysRename_sound
        by sysrename_side_cond.
      pose proof Vel.ctrl_safe.
      rename_hyp mirror H.
      rewrite Rename_impl in H. rewrite Rename_True in H.
      restoreAbstraction. apply landAdj in H.
      rewrite landtrueL in H. rewrite H. clear.
      rewrite <- Rename_ok by rw_side_condition.
      tlaRevert. apply always_imp. unfold V.ub.
      solve_linear.
    - charge_intros. pose proof Vel.ctrl_safe.
      unfold V.ub in *. charge_apply H. charge_tauto. 
  Qed.

  Lemma Prog_enabled :
    |-- Enabled SpecR.(Prog).
  Proof.
    simpl. restoreAbstraction.
    enable_ex_st. smart_repeat_eexists. solve_linear.
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

End UpperLowerFirst.
