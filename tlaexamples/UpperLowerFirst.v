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

  Let mirror :=
    ("v",--"v")::("a",--"a")::nil.


Definition mirrored : ActionFormula :=
  SysRename (to_RenameMap mirror) (deriv_term_RenameList mirror)
            Vel.Next.

Definition upper_lower : ActionFormula :=
  SysCompose mirrored Vel.Next.

  Definition Next :
    { x : ActionFormula | x |-- Rename (to_RenameMap mirror) Vel.Next //\\ Vel.Next }.
  Proof.
    eexists.
    unfold Vel.Next.
    match goal with
    | |- context [ Rename (to_RenameMap ?m) ?s ] =>
      rewrite <- (@SysRename_rule _ _ _ (to_RenameMap m)
                                  (deriv_term_RenameList m))
    end;
      [ | unfold RenameMapOk; is_st_term_list
        | reflexivity
        | apply RenameDerivOk_deriv_term; apply deriv_term_list; reflexivity ].
    rewrite <- Sys_rename_formula by rw_side_condition.
    apply SysCompose_simpl.
  Defined.

  Definition IndInv :
    { x : StateFormula | x -|- Rename (to_RenameMap mirror) Vel.IndInv //\\ Vel.IndInv }.
  Proof.
    eexists.
    rewrite <- Rename_ok by rw_side_condition.
    reflexivity.
  Defined.


Ltac rewrite_projT2_L s :=
  let H := fresh in
  pose proof (projT2 s) as H;
    cbv beta in H; rewrite <- H; clear H.

Ltac rewrite_projT2_R s :=
  let H := fresh in
  pose proof (projT2 s) as H;
    cbv beta in H; rewrite H; clear H.

Lemma TimedPreserves 

  Lemma UpperLower_preserves :
    |-- TimedPreserves d (projT1 IndInv) (projT1 Next).
  Proof.
    unfold TimedPreserves.
pose proof (projT2 Next).
cbv beta in H.
rewrite H. clear H.
rewrite Preserves_equiv.
5: reflexivity.
Focus 4.
 pose proof (projT2 IndInv).
cbv beta in H. rewrite H. reflexivity.
2: compute; tauto.
2: compute; tauto.

SearchAbout Preserves.
     (projT2 IndInv).
    etransitivity. 2: apply Preserves_entails.
Focus 4. pose proof (projT2 IndInv).
cbv beta in H. rewrite H. reflexivity.
Focus 4. apply (projT2 Next).
2: compute; tauto.
2: 
2
    pose proof (projT2 Next).
    cbv beta in H. rewrite H.
    pose proof (projT2 IndInv).
    cbv beta in H. rewrite H.
    rewrite (H (projT1 IndInv)).
    unfold Preserves. charge_intros. rewrite (projT2 X) at 1.
    SearchAbout TimedPreserves. rewrite Preserves_And.

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
      tlaRevert. apply Always_imp. unfold V.ub.
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
