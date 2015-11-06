Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TLA.TLA.
Require Import TLA.EnabledLemmas.
Require Import TLA.ProofRules.
Require Import Examples.System2.
Require Import Examples.FirstDerivShimCtrl.
Require Import ChargeTactics.Lemmas.

Set Implicit Arguments.
Set Strict Implicit.

Local Open Scope string_scope.
Local Open Scope HP_scope.

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

  Definition Next' : ActionFormula :=
    Rename (to_RenameMap mirror) Vel.Next //\\ Vel.Next.

(*
  Inductive SysCombine : Formula -> Formula -> Type :=
  | SysCombine_X : forall {D1 D2 W1 W2 d}, SysCombine (Sys D1 W1 d) (Sys D2 W2 d).

  Definition SysFromCombine A B (SC : SysCombine A B) : Formula :=
    match SC with
    | SysCombine_X D1 D2 W1 W2 d =>
      Sys (D1 //\\ D2) (W1 //\\ W2) d
    end.

  Definition SC_Next : Formula :=
    Eval cbv beta iota zeta delta [ SysFromCombine ] in @SysFromCombine (Vel.Next) (Vel.Next) (SysCombine_X).

  Definition SC_Next : SysCombine (Vel.Next) Vel.Next.
  Proof. constructor. Defined.
    constructor.
*)
(*
  Definition Next' : ActionFormula :=
    Rename (to_RenameMap mirror) Vel.Next //\\ Vel.Next.
*)


  Definition SpecVelocityMirrorR :
    { x : ActionFormula | x |-- Next' }.
  Proof.
eexists.
    unfold Next'.
Check SysRename_rule.
Print RenameMapOk.
Check Rename_ok.
unfold Vel.Next.
match goal with
  | |- context [ Rename (to_RenameMap ?m) ?s ] =>
    rewrite <- (@SysRename_rule _ _ _ (to_RenameMap m) (deriv_term_RenameList m))
end.
Focus 2. simpl. red. intros. destruct (string_dec x "v"); auto. destruct (string_dec x "a"); auto.
Focus 2. reflexivity.
Focus 2. apply RenameDerivOk_deriv_term. apply deriv_term_list. reflexivity.
repeat rewrite <- Rename_ok. simpl rename_formula. restoreAbstraction.
unfold Sys, World, mkEvolution.
SearchAbout Continuous  Morphisms.Proper.
rewrite <- Rename_ok.
Focus.
eapply land_lentails_m; [ | reflexivity ].
eapply Proper_Sys_lentails; [ reflexivity | | reflexivity ].
Lemma X : forall (X Y : _ -> Evolution),
    (forall x y, X x y = Y x y) ->
    (fun st' => Forall st'' : state, (Forall x : Var, st'' x = deriv_term_RenameList mirror st' x) -->> X st' st'')
    |-- (fun st' => Forall st'' : state, (Forall x : Var, st'' x = deriv_term_RenameList mirror st' x) -->> Y st' st'').
Proof. Admitted.
eapply X. intros.

    exists
      (Sys_rename_formula (to_RenameMap m)
                           s)
  end.
  apply SysRename_rename_formula_equiv;
  rw_side_condition.


    eexists.
    unfold Next'. SearchAbout Rename Sys.
    unfold Vel.Next.

rewrite <- SysRename_rule.
    4: eapply RenameDerivOk_deriv_term.
    Focus 4. simpl.
    RenameDerivOk.
    { rewrite <- Rename_ok.
      simpl rename_formula. restoreAbstraction.
      
rewrite_rename_ok. apply SysCompose_simpl. }
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
