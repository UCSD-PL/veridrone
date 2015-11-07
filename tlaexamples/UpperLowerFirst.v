Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TLA.TLA.
Require Import TLA.EnabledLemmas.
Require Import TLA.ProofRules.
Require Import TLA.Inductively.
Require Import Examples.System2.
Require Import Examples.FirstDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import ChargeTactics.Indexed.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope string_scope.
Local Open Scope HP_scope.

Module Type UpperLowerFirstParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
End UpperLowerFirstParams.

Module UpperLowerFirst (Import P : UpperLowerFirstParams).
  Module V <: FirstDerivShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End V.

  Module Vel := FirstDerivShim V.

  Let mirror : RenameList :=
    {{ "v" ~> --"v" ; "a" ~> --"a" }}%rn.

  Definition mirrored : ActionFormula :=
    SysRename mirror (deriv_term_RenameList mirror)
              Vel.Next.

  Definition Next : ActionFormula :=
    SysCompose mirrored Vel.Next.

  Definition IndInv : StateFormula :=
    Rename mirror Vel.IndInv //\\ Vel.IndInv.

  Lemma TimedPreserves_Next :
    |-- TimedPreserves d IndInv Next.
  Proof with (refine _).
    unfold IndInv, Next. unfold SysCompose.
    rewrite SysCompose_simpl.
    rewrite <- TimedPreserves_And...
    charge_split.
    { rewrite Sys_rename_formula by eauto with rw_rename.
      rewrite SysRename_rule by eauto with rw_rename.
      rewrite TimedPreserves_Rename by eauto with rw_rename.
      eapply Proper_Rename_True.
      apply Vel.TimedPreserves_Next. }
    { eapply Vel.TimedPreserves_Next. }
  Qed.

  Theorem SysNeverStuck_Next : |-- SysNeverStuck d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys'; [ refine _ | pose proof d_gt_0 ; solve_linear | | ].
    { enable_ex_st.
      pose proof d_gt_0.
      do 2 eexists; exists d; solve_linear. }
    { admit. (** Provable, but we won't worry about it *) }
  Qed.

  Definition Safe : Formula :=
    --P.ub <= "v" <= P.ub.

  Lemma IndInv_impl_Inv : IndInv //\\ 0 <= "T" <= d |-- Safe.
  Proof with (eauto with rw_rename).
    unfold IndInv, Safe, Vel.IndInv, V.ub.
    rewrite <- Rename_ok...
    solve_nonlinear.
  Qed.

  Theorem Spec_safe :
    |-- (IndInv //\\ 0 <= "T" <= d) //\\ []Next -->> []Safe.
  Proof.
    rewrite Preserves_Inv_simple.
    { rewrite IndInv_impl_Inv.
      charge_tauto. }
    { compute; tauto. }
    { apply TimedPreserves_Next. }
  Qed.

End UpperLowerFirst.
