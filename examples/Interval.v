Require Import Coq.Reals.Reals.
Require Import ChargeCore.Tactics.Lemmas.
Require Import Logic.Logic.
Require Import Logic.EnabledLemmas.
Require Import Logic.ProofRules.
Require Import Logic.ArithFacts.
Require Import Examples.System.
Require Import Examples.UtilPosition.
Require Import Examples.Position.
Require Import Examples.Velocity.

Local Open Scope string_scope.
Local Open Scope HP_scope.

Module Type IntervalParams.
  Parameter ub : R.
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.
  Parameter ubv : R.
  Axiom ubv_gt_amin_d : (ubv >= -amin*d)%R.
  Parameter ubv_gt_0 : (ubv > 0)%R.
  Parameter ub_ubv :
    (ubv*d + ubv*ubv*(0 - /2)*(/amin) <= ub)%R.
End IntervalParams.

Module IntervalShim (Import P : IntervalParams).

  Module X_Params <: PositionShimParams.
    Definition ub := P.ub.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
    Definition amin := P.amin.
    Definition amin_lt_0 := P.amin_lt_0.
    Definition ubv := P.ubv.
    Definition ub_ubv := P.ub_ubv.
  End X_Params.

  Module X := PositionShim X_Params.

  Module V_Params <: VelocityShimParams.
    Definition ub := P.ubv.
    Definition d := P.d.
    Definition d_gt_0 := P.d_gt_0.
  End V_Params.

  Module V := VelocityShim V_Params.

  Module SdistUtil := SdistUtil(X_Params).
  Import SdistUtil.

  Let mirror : RenameList :=
    {{ "y" ~> --"y" & "v" ~> --"v" & "a" ~> --"a" }}%rn.

  Definition mirroredX : ActionFormula :=
    SysRename mirror (deriv_term_RenameList mirror) X.Next.

  Definition mirroredV : ActionFormula :=
    SysRename mirror (deriv_term_RenameList mirror) V.Next.

  Definition Next : ActionFormula :=
    SysCompose (SysCompose X.Next mirroredX)
               (SysCompose V.Next mirroredV).

  Definition IndInv : StateFormula :=
    (X.IndInv //\\ Rename mirror X.IndInv) //\\
    (V.IndInv //\\ Rename mirror V.IndInv).

  Lemma TimedPreserves_Next :
    |-- TimedPreserves d IndInv Next.
  Proof with (refine _).
    unfold IndInv, X.IndInv, V.IndInv, Next, X.SafeAcc.
    unfold SysCompose.
    repeat ((try simple apply TimedPreserves_intro);
      rewrite SysCompose_simpl;
      rewrite <- TimedPreserves_And by tlaIntuition;
      charge_split).
      { apply TimedPreserves_intro. rewrite <- X.TimedPreserves_Next.
        charge_tauto. }
      { apply TimedPreserves_intro.
        rewrite Sys_rename_formula by eauto with rw_rename.
        rewrite SysRename_rule by eauto with rw_rename.
        rewrite TimedPreserves_Rename by eauto with rw_rename.
        rewrite <- X.TimedPreserves_Next. rewrite Rename_True.
        charge_tauto. }
      { apply TimedPreserves_intro. rewrite <- V.TimedPreserves_Next.
        charge_tauto. }
      { apply TimedPreserves_intro.
        rewrite Sys_rename_formula by eauto with rw_rename.
        rewrite SysRename_rule by eauto with rw_rename.
        rewrite TimedPreserves_Rename by eauto with rw_rename.
        rewrite <- V.TimedPreserves_Next. rewrite Rename_True.
        charge_tauto. }
  Qed.

  Lemma velocity_refinement :
    "v" <= ubv //\\
    "v" + "a"!*d <= ubv //\\
    ("y" > 0 -->> X.SafeAccZeroOrder "a"! d)
    |-- X.SafeAccZeroOrder "a"! d.
  Proof.
    pose proof d_gt_0 as d_gt_0. pose proof amin_lt_0 as amin_lt_0.
    pose proof ubv_gt_0 as ubv_gt_0. pose proof ub_ubv as ub_ubv.
    intros. reason_action_tac.
    destruct H as [Hubv1 [Hubv2 Hctrl]].
    destruct (Rgt_dec (pre "y") R0).
    { auto. }
    { clear Hctrl. split; intros.
      { eapply Rle_trans; eauto.
        pose proof (sdist_incr (pre "v" + post "a" * d)
                               ubv (Stream.forever (fun _ => R0))).
        breakAbstraction. specialize_arith_hyp H0. rewrite H0.
        assert ((pre "v" * d + / 2 * post "a" * (d * (d * 1))) <=
                ubv * d)%R.
        { clear - Hubv1 Hubv2 H d_gt_0. solve_nonlinear. }
        { unfold X_Params.amin, X_Params.ub in *. solve_linear. } }
      { unfold X_Params.ub. transitivity (ubv*d)%R.
        { field_simplify; [ | solve_nonlinear ].
          apply Rmult_le_algebra_neg; [ solve_nonlinear | ].
          unfold Rdiv. rewrite RMicromega.Rinv_1. simpl.
          clear - Hubv1 d_gt_0 H n. solve_nonlinear. }
        { assert ((0 - / 2) < 0)%R by solve_linear.
          assert (/amin < 0)%R by solve_linear.
          generalize dependent (/amin)%R.
          generalize dependent (0-/2)%R. intros.
          clear -H0 H1 ubv_gt_0 ub_ubv0. solve_nonlinear. } } }
  Qed.

  Definition Constraint :=
    amin <= "a" <= --amin.

   Lemma SysNeverStuck_Discr :
     IndInv //\\ "T" = 0
     |-- Enabled ((0 <= "T"! <= d //\\ Sys_D Next) //\\
                     next Constraint).
   Proof.
     unfold Sys_D, IndInv, X.IndInv. repeat rewrite Rename_ok by eauto with rw_rename.
     rewrite <- velocity_refinement.
     charge_assert (X.SafeAcc "a" 0).
     { rewrite <- (X.SafeAcc_downclock "a" 0 "T"). solve_linear. }
     charge_assert (Rename mirror (X.SafeAcc "a" 0)).
     { rewrite <- (X.SafeAcc_downclock "a" 0 "T").
       repeat rewrite <- Rename_ok by eauto with rw_rename. solve_linear. }
     charge_assert ("v" <= ubv).
     { reason_action_tac. assert (pre "a" < 0 \/ pre "a" >= 0)%R by solve_linear.
       destruct H. rewrite H1 in *. rewrite_real_zeros. solve_linear. }
     charge_assert (--"v" <= ubv).
     { repeat rewrite <- Rename_ok by eauto with rw_rename.
       reason_action_tac. assert (0 - pre "a" < 0 \/ 0 - pre "a" >= 0)%R by solve_linear.
       destruct H. rewrite H1 in *. rewrite_real_zeros. solve_linear. }
     charge_assert ("y" <= ub).
     { rewrite <- (X.SafeAcc_Safe "a" "T"). solve_linear. }
     charge_assert (Rename mirror ("y" <= ub)).
     { rewrite <- (X.SafeAcc_Safe "a" "T").
       repeat rewrite <- Rename_ok by eauto with rw_rename. solve_linear. }
     rewrite X.SafeAcc_ZeroOrder_amin. charge_clear. charge_intros.
     repeat rewrite <- Rename_ok by eauto with rw_rename. enable_ex_st'.
     pose proof P.amin_lt_0. pose proof P.d_gt_0.
     pose proof P.ubv_gt_amin_d.
     unfold V_Params.ub, V_Params.d, X_Params.ub, X_Params.amin, X_Params.d in *.
     destruct (Rgt_dec (st "y") R0);
       destruct (Rgt_dec (st "v") R0).
     { exists amin; do 2 eexists; exists d; solve_nonlinear. }
     { exists R0; do 2 eexists; exists d; intuition; try solve [solve_linear].
       rewrite_real_zeros. destruct H11; [ solve_linear | rewrite <- H11 ].
       rewrite_real_zeros. solve_linear. exfalso. solve_linear. }
     { exists R0; do 2 eexists; exists d; intuition; try solve [solve_linear].
       exfalso. solve_linear. }
     { exists (-amin)%R; do 2 eexists; exists d; solve_linear.
       solve_nonlinear. rewrite_real_zeros. repeat rewrite Ropp_involutive. solve_linear. }
   Qed.

   Require Import Examples.Quadcopter.

   Variable g : R.
   Hypothesis amin_lt_g : (amin > -g)%R.
   Variable angle_min : R.
   Hypothesis angle_min_le_0 : (angle_min < 0)%R.

   (* Map the interval onto the vertical dimension of
      the quadcopter. *)
   Let rename_quad : RenameList :=
    {{ "a" ~> "A"*cos("pitch")*cos("roll") - g &
       "y" ~> "z" & "v" ~> "vz" }}%rn.

  Let quad_inv : RenameList :=
    {{ "roll" ~> 0 & "pitch" ~> 0 & "A" ~> "a" + g &
       "z" ~> "y" & "vz" ~> "v" }}%rn.

  Let small_angle := small_angle angle_min.

  Lemma Constraint_small_angle :
    Constraint |-- Rename quad_inv small_angle.
  Proof.
    rewrite <- Rename_ok by eauto with rw_rename.
    breakAbstraction. intros. pose proof amin_lt_g.
    pose proof angle_min_le_0. solve_linear.
  Qed.

  Lemma quad_inv_ok :
    forall xs,
      List.forallb (fun x => if String.string_dec x "A"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "roll"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "pitch"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "z"
                             then false else true) xs =
      true ->
      List.forallb (fun x => if String.string_dec x "vz"
                             then false else true) xs =
      true ->
      forall st x,
        List.In x xs ->
        eval_formula Constraint (Stream.forever st) ->
        subst_state rename_quad
                    (subst_state quad_inv st) x = st x.
  Proof.
    simpl. unfold Value, subst_state. simpl. intros.
    repeat destruct_ite; subst; simpl in *; try reflexivity.
    { rewrite cos_0. solve_linear. }
    { rewrite List.forallb_forall in *. specialize (H "A").
      specialize (H0 "roll"). specialize (H1 "pitch").
      specialize (H2 "z"). specialize (H3 "vz").
      repeat destruct_ite; subst; simpl; try reflexivity;
        try match goal with
        | [ H : ?X -> _ |- _ ] =>
            match type of H4 with
            | X => specialize (H H4); simpl in *; discriminate
            end
        end. }
  Qed.

  Definition Next_quad : ActionFormula :=
    SysCompose
      (SysRename rename_quad
                 (deriv_term_RenameList rename_quad) Next)
      (Sys (next small_angle) ltrue P.d).

  Definition IndInv_quad := Rename rename_quad IndInv.

  Transparent ILInsts.ILFun_Ops.

  Lemma TimedPreserves_Next_quad :
    |-- TimedPreserves P.d IndInv_quad Next_quad.
  Proof with eauto with rw_rename.
    unfold IndInv_quad, Next_quad.
    rewrite SysCompose_abstract. unfold SysRename.
    rewrite Sys_rename_formula... rewrite SysRename_rule...
    rewrite TimedPreserves_Rename...
    rewrite <- TimedPreserves_Next. rewrite Rename_True.
    charge_tauto.
  Qed.

  Opaque ILInsts.ILFun_Ops.

  Lemma SysNeverStuck_Discr_quad :
    IndInv_quad //\\ "T" = 0 |-- Enabled (Sys_D Next_quad).
  Proof.
    unfold Sys_D, IndInv_quad.
    rewrite_rename_equiv ("T" = 0) rename_quad.
    rewrite <- Rename_and.
    rewrite Rename_ok by eauto with rw_rename.
    eapply subst_enabled_full
    with (R:=Constraint) (Q:=small_angle).
    { tlaIntuition. }
    { tlaIntuition. }
    { apply is_action_formula_ok; simpl; tauto. }
    { apply get_vars_next_state_vars; reflexivity. }
    { intros. eapply quad_inv_ok. 6: apply H.
      reflexivity. reflexivity. reflexivity. reflexivity.
      reflexivity. auto. }
    { apply Constraint_small_angle. }
    { pose proof SysNeverStuck_Discr. unfold Sys_D in H.
      rewrite Rename_ok in * by eauto with rw_rename.
      rewrite H. apply Proper_Enabled_lentails.
      charge_tauto. }
  Qed.

  Theorem SysNeverStuck_Next :
    |-- SysNeverStuck P.d IndInv_quad Next_quad.
  Proof.
    eapply SysNeverStuck_Sys;
    [ pose proof P.d_gt_0 ; solve_linear | | ].
    { rewrite <- disjoint_state_enabled.
      { charge_split.
        { charge_clear. apply Enabled_TimeBound.
          pose proof P.d_gt_0. assumption. }
        { apply SysNeverStuck_Discr_quad. } }
      { apply formulas_disjoint_state; reflexivity. } }
    { admit. (** Provable, but we won't worry about it *) }
  Admitted.

  Definition Safe : StateFormula :=
    (X.Safe //\\ Rename mirror X.Safe) //\\
    ("v" <= V_Params.ub //\\ Rename mirror ("v" <= V_Params.ub)).

  Definition Safe_quad : StateFormula :=
    Rename rename_quad Safe.

  Lemma IndInv_impl_Safe : IndInv //\\ TimeBound d |-- Safe.
  Proof with (eauto with rw_rename).
    unfold Safe. charge_split.
    { charge_split.
      { rewrite <- X.IndInv_impl_Safe. charge_tauto. }
      { rewrite <- X.IndInv_impl_Safe. rewrite Rename_and.
        unfold IndInv. charge_split; [ charge_assumption | ].
        rewrite <- (Rename_ok (TimeBound X_Params.d))...
        solve_linear. } }
    { charge_split.
      { rewrite <- V.IndInv_impl_Inv. charge_tauto. }
      { rewrite <- V.IndInv_impl_Inv. rewrite Rename_and.
        unfold IndInv. charge_split; [ charge_assumption | ].
        rewrite <- (Rename_ok (TimeBound X_Params.d))...
        solve_linear. } }
  Qed.

  Lemma IndInv_impl_Safe_quad :
    IndInv_quad //\\ TimeBound P.d |-- Safe_quad.
  Proof with (eauto with rw_rename).
    unfold Safe, TimeBound, IndInv_quad.
    rewrite_rename_equiv (0 <= "T" <= P.d) rename_quad.
    rewrite <- Rename_and.
    apply Proper_Rename_lentails; try reflexivity.
    apply IndInv_impl_Safe.
  Qed.

  Lemma W_quad_refines :
    W_quad g |-- Sys_w Next_quad.
  Proof.
    (* Mechanical reasoning about abstractions of
       differential equations. *)
  Admitted.

  (* Our main safety theorem. *)
  Theorem Interval_safe :
    |-- (IndInv_quad //\\ TimeBound P.d) //\\
        []SysSystem (Quadcopter P.d g angle_min
                                (Sys_D Next_quad))
        -->> []Safe_quad.
  Proof.
    rewrite Inductively.Preserves_Inv_simple.
    { rewrite IndInv_impl_Safe_quad.
      charge_tauto. }
    { compute; tauto. }
    { apply SafeAndReactive_TimedPreserves.
      eapply Quadcopter_refine.
      { apply P.d_gt_0. }
      { pose proof angle_min_le_0. solve_linear. }
      { apply TimedPreserves_Next_quad. }
      { apply SysNeverStuck_Next. }
      { unfold Sys_D. unfold small_angle. charge_assumption. }
      { apply W_quad_refines. } }
  Qed.

End IntervalShim.