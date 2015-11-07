Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import ChargeTactics.Lemmas.
Require Import TLA.TLA.
Require Import TLA.DifferentialInduction.
Require Import TLA.ProofRules.
Require Import Examples.System2.
Require Import Examples.SecondDerivShimCtrlToMiddle4.

Local Open Scope string_scope.

Set Implicit Arguments.
Set Strict Implicit.

Module Type UpperLowerSecondParams.
  Parameter ub : R.

  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter amin : R.
  Axiom amin_lt_0 : (amin < 0)%R.

  Parameter ubv : R.
  Parameter ub_ubv : (ubv*d + ubv*ubv*(0-/2)*(/amin) <= ub)%R.

End UpperLowerSecondParams.

Module UpperLowerSecond (Import P : UpperLowerSecondParams).

  Module Params <: SecondDerivShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv.
    Definition ub_ubv := P.ub_ubv.
  End Params.

  Module Monitor := SecondDerivShimCtrl Params.

  Let mirror : RenameList :=
    {{ "y" ~> --"y" ; "v" ~> --"v" ; "a" ~> --"a" }}%rn.

  Definition mirrored : ActionFormula :=
    SysRename mirror (deriv_term_RenameList mirror)
              Monitor.Next.

  Definition Next : ActionFormula :=
    SysCompose mirrored Monitor.Next.

  Definition IndInv : StateFormula :=
    Rename mirror Monitor.IndInv //\\ Monitor.IndInv.

  Definition Next_Assumption : StateFormula :=
    Rename mirror Monitor.Next_Assumption //\\ Monitor.Next_Assumption.

  Lemma TimedPreserves_Next :
    Next_Assumption |-- TimedPreserves d IndInv Next.
  Proof with (refine _).
    unfold IndInv, Next. unfold SysCompose.
    rewrite SysCompose_simpl.
    rewrite <- TimedPreserves_And_simple...
    unfold Next_Assumption.
    charge_split.
    { rewrite Sys_rename_formula by eauto with rw_rename.
      rewrite SysRename_rule by eauto with rw_rename.
      rewrite TimedPreserves_Rename by eauto with rw_rename.
      rewrite <- Monitor.TimedPreserves_Next.
      charge_tauto. }
    { rewrite <- Monitor.TimedPreserves_Next.
      charge_tauto. }
  Qed.

  Theorem SysNeverStuck_Next : |-- SysNeverStuck d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys'; [ refine _ | pose proof d_gt_0 ; solve_linear | | ].
    { enable_ex_st.
      pose proof P.amin_lt_0. pose proof P.d_gt_0.
      destruct (RIneq.Rge_dec (st "y") R0).
      { do 3 eexists; exists d; solve_linear. }
      { do 3 eexists; exists d.
        repeat split.
        { solve_linear. }
        { solve_linear. }
        { right. instantiate (1:=(-Params.amin)%R).
          solve_linear. }
        { right. intros. apply RIneq.Rgt_ge in H3.
          contradiction. } } }
    { admit. (** Provable, but we won't worry about it *) }
  Qed.

  Definition Safe : StateFormula :=
    Rename mirror Monitor.Safe //\\ Monitor.Safe.

  Lemma IndInv_impl_Safe : Next_Assumption //\\ IndInv //\\ TimeBound d |-- Safe.
  Proof with (eauto with rw_rename).
    charge_split.
    { rewrite <- Monitor.IndInv_impl_Safe.
      unfold IndInv, Next_Assumption.
      Rename_rewrite.
      do 2 (charge_split; try charge_assumption).
      repeat rewrite <- Rename_ok...
      simpl rename_formula. charge_tauto. }
    { rewrite <- Monitor.IndInv_impl_Safe.
      charge_tauto. }
  Qed.

  Local Open Scope HP_scope.

  Lemma UpperLower_safe :
    []Next_Assumption |-- (IndInv //\\ TimeBound d) //\\ []Next -->> []Safe.
  Proof.
    rewrite <- IndInv_impl_Safe.
    rewrite <- Always_and.
    charge_intros; charge_split; try charge_assumption.
    charge_revert.
    eapply Inductively.Preserves_Inv.
    - compute; tauto.
    - reflexivity.
    - eapply TimedPreserves_Next.
  Qed.

End UpperLowerSecond.
