Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.SecondDerivShimCtrl.

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

  Let rename_y :=
    VarRenameMap (("A","Ay")::("V","Vy")::("Y","Y")::("y","y")::("v","vy")::("a","ay")::("Ymax","Ymax")::("Vmax","Vymax")::nil).
  Let rename_x :=
    VarRenameMap (("A","Ax")::("V","Vx")::("Y","X")::("y","x")::("v","vx")::("a","ax")::("Ymax","Xmax")::("Vmax","Vxmax")::nil).

  Definition Spec :=
    SysCompose (SysRename rename_x SDSP_X.SpecR)
               (SysRename rename_y SDSP_Y.SpecR).

  Lemma the_box'
  : |-- SysD Spec -->> [] (Rename rename_x SDSP_X.Safe //\\ Rename rename_y SDSP_Y.Safe).
  Proof.
    eapply Compose.
    { apply SysSafe_rule; apply always_tauto.
      unfold SDSP_X.SpecR, SDSP_X.Ctrl, SDSP_X.History,
             SDSP_Y.SpecR, SDSP_Y.Ctrl, SDSP_Y.History.
      simpl. restoreAbstraction.
      unfold Max.
      repeat rewrite <- Rename_ok by (repeat constructor).
(* TODO: We should be able to make this more efficient with a [cbv] 
      cbv beta iota zeta delta [ rename_formula rename_term find_term land lor limpl ILogicOps_Formula ltrue option_map find string_dec ].
*)
      Time simpl rename_formula; restoreAbstraction.
      unfold Discr.

      (** TODO: This stuff should move! *)
      Fixpoint get_next_vars_term (t : Term) : list Var :=
        match t with
        | VarNextT t => t :: nil
        | VarNowT _ | NatT _ | RealT _ => nil
        | PlusT a b | MinusT a b | MultT a b => get_next_vars_term a ++ get_next_vars_term b
        | InvT a | CosT a | SinT a => get_next_vars_term a
        end.

      Fixpoint get_next_vars_formula (f : Formula) : list Var :=
        match f with
        | Always a | Eventually a | Enabled a => get_next_vars_formula a
        | And a b | Or a b | Imp a b => get_next_vars_formula a ++ get_next_vars_formula b
        | Rename _ a => get_next_vars_formula a
        | Comp l r _ => get_next_vars_term l ++ get_next_vars_term r
        | _ => nil
        end.

      Fixpoint remove_dup (ls : list Var) : list Var :=
        match ls with
        | nil => nil
        | l :: ls => let ls' := remove_dup ls in if in_dec string_dec l ls' then ls' else l :: ls'
        end.
      Ltac enabled_ex_st :=
      match goal with
      | |- lentails _ (Enabled ?X) =>
        let vars := eval compute in (remove_dup (get_next_vars_formula X)) in
        let rec foreach ls :=
            match ls with
            | @cons _ ?l ?ls => eapply (ex_state l); simpl ; foreach ls
            | _ => idtac
            end
        in
        eapply Enabled_action; intros; eapply ex_state_flow_any; auto; simpl; intros;
        foreach vars
      end; try (eapply ex_state_any; (let st := fresh in
                                          intro st; clear st)).
      enabled_ex_st.
      unfold X.d, Y.d.
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
      { compute. intuition congruence. }
      { admit. (** this is not trivial **) } }
    { (* similar to above *) admit. }
  Qed.
End Corner.