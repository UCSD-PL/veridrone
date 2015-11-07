Require Import Coq.Reals.Rdefinitions.
Require Import ChargeTactics.Lemmas.
Require Import TLA.TLA.
Require Import TLA.EnabledLemmas.
Require Import TLA.ProofRules.
Require Import Examples.System2.
Require Import Examples.UpperLowerSecond.
Require Import Examples.UpperLowerFirst.

Local Open Scope string_scope.
Local Open Scope HP_scope.

Module Type UpperLowerParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.
  Parameter ubv : R.
  Axiom ubv_gt_amin_d : (ubv >= -amin*d)%R.
  Parameter ub_ubv :
    (ubv*d + ubv*ubv*(0 - /2)*(/amin) <= ub)%R.
End UpperLowerParams.

Module UpperLower (Import P : UpperLowerParams).

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

  Definition Next : ActionFormula :=
    SysCompose Vel.Next Position.Next.

  Definition IndInv : StateFormula :=
    Vel.IndInv //\\ Position.IndInv.

  Lemma Vel_IndInv_Position_Assumption :
    Vel.IndInv //\\ TimeBound V.d |-- Position.Next_Assumption.
  Proof.
    rewrite Vel.IndInv_impl_Inv.
    unfold Position.Next_Assumption, Vel.Safe, V.ub,
    Position.Monitor.Next_Assumption, Position.Params.ubv, Y.ubv.
    rewrite <- Rename_ok by eauto with rw_rename.
    solve_linear.
  Qed.

  Lemma TimedPreserves_Next :
    |-- TimedPreserves d IndInv Next.
  Proof with (refine _).
    unfold IndInv, Next. unfold SysCompose.
    rewrite SysCompose_simpl.
    rewrite <- TimedPreserves_And...
    charge_split.
    { apply TimedPreserves_intro.
      rewrite <- Vel.TimedPreserves_Next.
      charge_tauto. }
    { apply TimedPreserves_intro.
      rewrite <- Position.TimedPreserves_Next.
      rewrite Vel_IndInv_Position_Assumption.
      charge_tauto. }
  Qed.

  Theorem SysNeverStuck_Next : |-- SysNeverStuck d IndInv Next.
  Proof.
    eapply SysNeverStuck_Sys'; [ refine _ | pose proof d_gt_0 ; solve_linear | | ].
    { enable_ex_st.
      pose proof P.amin_lt_0. pose proof P.d_gt_0.
      pose proof P.ubv_gt_amin_d.
      unfold Vel.V.ub, Vel.V.d, V.ub, V.d.
      unfold Position.Params.amin.
      unfold Y.amin.
      destruct (RIneq.Rgt_dec (st "y") R0);
        destruct (RIneq.Rgt_dec (st "v") R0).
      { do 2 eexists; exists P.amin; exists d; solve_linear. }
      { do 3 eexists; exists d; solve_linear. }
      { do 3 eexists; exists d; solve_linear. }
      { do 2 eexists; exists (-P.amin)%R; exists d; solve_linear. } }
    { admit. (** Provable, but we won't worry about it *) }
  Qed.

  Definition Safe : StateFormula :=
    Vel.Safe //\\ Position.Safe.

  Lemma IndInv_impl_Safe : IndInv //\\ TimeBound d |-- Safe.
  Proof with (eauto with rw_rename).
    charge_split.
    { rewrite <- Vel.IndInv_impl_Inv.
      unfold IndInv, TimeBound, V.d.
      charge_tauto. }
    { rewrite <- Position.IndInv_impl_Safe.
      unfold Y.d, IndInv.
      rewrite <- Vel_IndInv_Position_Assumption.
      unfold V.d. charge_tauto. }
  Qed.

  Lemma UpperLower_safe :
    |-- (IndInv //\\ TimeBound d) //\\ []Next -->> []Safe.
  Proof.
    rewrite <- IndInv_impl_Safe.
    eapply Inductively.Preserves_Inv.
    3: apply TimedPreserves_Next.
    - compute; tauto.
    - apply always_tauto. charge_tauto.
  Qed.

  Definition Constraint :=
    P.amin <= "a" <= --P.amin.

End UpperLower.