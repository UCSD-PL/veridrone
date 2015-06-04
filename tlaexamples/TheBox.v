Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.
Require Import Examples.SecondDerivShimCtrl.
Require Import ChargeTactics.Lemmas.

Require Import TLA.DifferentialInduction.
Print Ranalysis1.derivable_pt.
Print derive_stateF.

Lemma subst_state_derivable : forall f m,
    (forall x,
        Ranalysis1.derivable (fun t => f t x)) ->
    forall x,
      Ranalysis1.derivable
        (fun t => subst_state m (f t) x).
Proof.
Admitted.
(*
  intros.
  induction m.
  - simpl. auto.
  - simpl. destruct a. simpl.
    destruct (String.string_dec x v).
    + subst. apply H.
    + auto.
Qed.
*)

Lemma find_term_list_in : forall x m t,
  BasicProofRules.find_term m x = Some t ->
  List.In (x, t) m.
Proof.
  induction m.
  - compute. discriminate.
  - unfold BasicProofRules.find_term. simpl.
    intros. destruct a. simpl in *.
    destruct (String.string_dec x v).
    + simpl in *. inversion H. subst. auto.
    + right. apply IHm; auto.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma Rename_continuous : forall m m' w,
(*  (forall f pf,
      List.map (fun p : Var*(state->Term) => fun t => eval_term ((snd p) (derive_stateF f pf t))
                                                  (f t) (f t)) m' =
      List.map (fun p : MapProof => Ranalysis1.derive
                   (fun t => eval_term (snd (snd p)) (f t) (f t)) (fst p)) m) ->*)
  (forall st, BasicProofRules.is_st_formula (w st)) ->
  (forall v e f, exists pf1 pf2,
        List.In (v,e) m ->
        exists e',
          List.In (v,e') m' /\
          Ranalysis1.derive
            (fun t => eval_term e (f t) (f t)) pf1 =
          fun t => eval_term (e' (derive_stateF f pf2 t))
                             (f t) (f t)) ->
  Continuous
  (fun st' =>
     Rename m (w (subst_state
       (List.map (fun p => (fst p, (snd p) st')) m') st'))) |--
  Rename m (Continuous w).
Proof.
  intros. breakAbstraction. intros.
  destruct tr as [[st1 f] [[st2 ?] ?]]. simpl in *.
  destruct H1 as [r H1]. exists r. intuition.
  { unfold subst_flow. subst. auto. }
  { unfold subst_flow. subst. auto. }
  { unfold is_solution, solves_diffeqs in *.
    destruct H5 as [pf H5]. unfold subst_flow.
    exists (subst_state_derivable f m pf).
    intros. specialize (H5 _ H4). simpl in *.
    rewrite Stream.stream_map_forever in *.
    unfold subst in *. simpl in *.
    eapply BasicProofRules.st_formula_hd.
    { auto. }
    { eapply BasicProofRules.Proper_eval_formula.
      3: apply H5.
      { clear - H0.
        match goal with
        |- _ ?st1 -|- _ ?st2 =>
        assert (st1 = st2) as Heq; [ | rewrite Heq; auto]
        end.
        apply functional_extensionality; intros.
        destruct (BasicProofRules.find_term m x) eqn:?.
        { specialize (H0 x t f).
          destruct H0 as [pf1 [pf2 H0]].
          apply find_term_list_in in Heqo.
          specialize (H0 Heqo). destruct H0 as [e' H0].
          Check BasicProofRules.find_term_now_Some_ok.
          erewrite <- BasicProofRules.find_term_now_Some_ok.
          SearchAbout subst_state.
          
erewrite <- BasicProofRules.find_term_now_Some_ok.

        SearchAbout subst_state.
        
 }
      { reflexivity. } }
    { reflexivity. }
    { admit. (* eq is an equivalence relation *) }

Focus 2.

    
    SearchAbout Stream.forever.

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

  Lemma the_box_rect
  : |-- SysD Spec -->>
        [](Rename rename_x SDSP_X.Safe //\\
           Rename rename_y SDSP_Y.Safe).
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
      enable_ex_st.
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
      { apply forget_prem. rewrite <- Rename_ok.
        simpl rename_formula. restoreAbstraction.
        enable_ex_st. repeat eexists. solve_linear.
        reflexivity. reflexivity. } }
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
      { compute. intuition congruence. }
      { apply forget_prem. rewrite <- Rename_ok.
        simpl rename_formula. restoreAbstraction.
        enable_ex_st. repeat eexists. solve_linear.
        reflexivity. reflexivity. } }
  Qed.

End Corner.