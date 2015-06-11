Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.SecondDerivShimCtrl.
Require Import ChargeTactics.Lemmas.
Require Import TLA.DifferentialInduction.

Set Implicit Arguments.
Set Strict Implicit.

Module Type CornerParams.
  Parameter ub_X : R.
  Parameter d : R.
  Axiom d_gt_0 : (d > 0)%R.

  Parameter amin_X : R.
  Axiom amin_lt_0_X : (amin_X < 0)%R.

  Parameter ub_Y : R.
End CornerParams.

Module Corner (P : CornerParams).
  Module X <: SecondDerivShimParams.
    Definition ub := P.ub_X.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin_X.
    Definition amin_lt_0 := P.amin_lt_0_X.
    Definition WC := TRUE.
  End X.

  Module Y <: SecondDerivShimParams.
    Definition ub := P.ub_Y.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin : R := (-1)%R. (** TODO **)
    Theorem amin_lt_0 : (amin < 0)%R.
    Admitted.
    Definition WC := TRUE.
  End Y.

  Module SDSP_X := SecondDerivShimCtrl X.
  Module SDSP_Y := SecondDerivShimCtrl Y.

  Require Import Coq.Strings.String.
  Local Open Scope string_scope.

  Require Import BasicProofRules.
  Require Import Coq.Lists.List.

Definition RenameListC (l : list (string * string)) :
  list (Var * Term) :=
  List.map (fun p => (fst p, VarNowT (snd p))) l.

  Let rename_y :=
    RenameListC (("A","Ay")::("V","Vy")::("Y","Y")::("y","y")::
                 ("v","vy")::("a","ay")::("Ymax","Ymax")::
                 ("Vmax","Vymax")::nil).
  Let rename_x :=
    RenameListC (("A","Ax")::("V","Vx")::("Y","X")::("y","x")::
                 ("v","vx")::("a","ax")::("Ymax","Xmax")::
                 ("Vmax","Vxmax")::nil).

  Definition deriv_term_succeed (t : Term) :=
    match deriv_term t with
    | Some t => t
    | None => fun _ => R0
    end.

  Fixpoint deriv_term_RenameList (l : list (Var*Term))
    (st' : state) : RenameMap :=
    match l with
    | nil => st'
    | (v, t) :: l =>
      fun x => if String.string_dec x v
               then deriv_term_succeed t st'
               else deriv_term_RenameList l st' x
    end.

Lemma deriv_term_list : forall l,
  List.forallb (fun p => match deriv_term (snd p) with
                         | None => false
                         | Some _ => true
                         end) l = true ->
  forall x,
    deriv_term (to_RenameMap l x) =
    Some (fun st' => deriv_term_RenameList l st' x).
Proof.
  induction l.
  - reflexivity.
  - simpl. destruct a. simpl.
    destruct (deriv_term t) eqn:?.
    + intros. destruct (String.string_dec x v).
      * subst. unfold deriv_term_succeed. rewrite Heqo.
        reflexivity.
      * rewrite IHl; auto.
    + inversion 1.
Qed.

  Definition Spec :=
    SysCompose (SysRename (to_RenameMap rename_x)
                          (deriv_term_RenameList rename_x)
                          SDSP_X.SpecR)
               (SysRename (to_RenameMap rename_y)
                          (deriv_term_RenameList rename_y)
                          SDSP_Y.SpecR).

Ltac is_st_term_list :=
  simpl; intros;
  repeat match goal with
           |- context [ String.string_dec ?e1 ?e2 ] =>
           destruct (String.string_dec e1 e2)
         end; try reflexivity.

  Lemma the_box_rect
  : |-- SysD Spec -->>
        [](Rename (to_RenameMap rename_x) SDSP_X.Safe //\\
           Rename (to_RenameMap rename_y) SDSP_Y.Safe).
  Proof.
    eapply Compose.
    { apply SysSafe_rule; apply always_tauto.
      unfold SDSP_X.SpecR, SDSP_X.Ctrl, SDSP_X.History,
             SDSP_Y.SpecR, SDSP_Y.Ctrl, SDSP_Y.History.
      simpl. restoreAbstraction.
      unfold Max, Discr.
      repeat rewrite <- Rename_ok by is_st_term_list.
(* TODO: We should be able to make this more efficient with a [cbv] 
      cbv beta iota zeta delta [ rename_formula rename_term find_term land lor limpl ILogicOps_Formula ltrue option_map find string_dec ].
*)
      Time simpl rename_formula; restoreAbstraction.
      unfold Discr.
      unfold X.d, Y.d.
      enable_ex_st.
      rewrite Rbasic_fun.Rmin_left by reflexivity.
      exists P.d.
      repeat match goal with
             | |- exists x, _ => eexists
             end.
      solve_linear. }
    { tlaIntro.
      rewrite <- Rename_Always.
      unfold rename_x.
      rewrite SysRename_sound.
      { eapply Proper_Rename.
        { reflexivity. }
        { pose proof SDSP_X.ctrl_safe.
          charge_apply H. unfold SDSP_X.Spec.
          charge_split; try charge_assumption. admit. } }
      { compute. tauto. }
      { intros. apply deriv_term_list; reflexivity. }
      { reflexivity. }
      { apply forget_prem. rewrite <- Rename_ok.
        simpl rename_formula. restoreAbstraction.
        enable_ex_st. repeat eexists. solve_linear.
        reflexivity. is_st_term_list. } }
    { apply forget_prem. tlaIntro.
      rewrite <- Rename_Always.
      unfold rename_y.
      rewrite SysRename_sound.
      { eapply Proper_Rename.
        { reflexivity. }
        { pose proof SDSP_Y.ctrl_safe.
          charge_apply H. unfold SDSP_Y.Spec.
          charge_split; try charge_assumption. admit. } }
      { compute. tauto. }
      { intros. apply deriv_term_list; reflexivity. }
      { reflexivity. }
      { apply forget_prem. rewrite <- Rename_ok.
        simpl rename_formula. restoreAbstraction.
        enable_ex_st. repeat eexists. solve_linear.
        reflexivity. is_st_term_list. } }
  Qed.

End Corner.