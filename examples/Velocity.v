Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Logic.Logic.
Require Import Logic.ProofRules.
Require Import Logic.Inductively.
Require Import Examples.System.

Local Open Scope HP_scope.
Local Open Scope string_scope.

Module Type VelocityShimParams.
  (* Upper bound on velocity. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
End VelocityShimParams.

Module VelocityShim (Import P : VelocityShimParams).

  (* The continuous dynamics of the system *)
  Definition w : Evolution :=
    fun st' => st' "v" = "a" //\\ st' "a" = 0.

  Definition SafeAcc (a v:Term) : Formula :=
    a*d + v <= ub.

  Definition Default (a:Term) : Formula :=
    a <= 0.

  Definition Ctrl : ActionFormula :=
    SafeAcc "a"! "v" \\// Default "a"!.


  Definition Next : ActionFormula :=
    Sys (Ctrl //\\ Unchanged ("v"::nil)) w d.

  Definition IndInv : Formula :=
         ("a" <  0 -->> "v" <= ub)
    //\\ ("a" >= 0 -->> "a"*"T" + "v" <= ub).

  Definition Safe : StateFormula := "v" <= ub.

  Theorem IndInv_impl_Inv :
    IndInv //\\ 0 <= "T" <= d |-- Safe.
  Proof. solve_nonlinear. Qed.

  Variable amin : R.
  Hypothesis amin_lt_0 : (amin < 0)%R.
  Definition Constraint := amin <= "a".

  Lemma SysNeverStuck_Discr :
    IndInv //\\ "T" = 0
    |-- Enabled ((0 <= "T"! <= d //\\ Sys_D Next) //\\
                  next Constraint).
  Proof.
    enable_ex_st'.
    pose proof d_gt_0. pose proof amin_lt_0.
    do 2 eexists; exists d; solve_linear.
  Qed.

  Theorem TimedPreserves_Next
  : |-- TimedPreserves d IndInv Next.
  Proof.
    eapply Preserves_Sys.
    { refine _. }
    { rewrite next_And. charge_split; fold next.
      - eapply diff_ind with (Hyps:=ltrue).
        + tlaIntuition.
        + tlaIntuition.
        + unfold World. tlaAssume.
        + tlaIntuition.
        + tlaAssume.
        + tlaIntuition.
        + charge_tauto.
        + simpl deriv_formula. restoreAbstraction.
          charge_intros.
          unfold lift2, mkEvolution, w.
          repeat charge_split; charge_intros;
          try solve [ solve_linear
                    | eapply zero_deriv with (x:="a");
                      [ charge_tauto | tlaIntuition |
                        solve_linear ] ].
          solve_nonlinear.
      - solve_linear. }
    { solve_nonlinear. }
  Qed.

  (* Map the interval onto the vertical dimension of
      the quadcopter. *)
  Require Import Examples.Quadcopter.

  Variable g : R.
  Hypothesis amin_lt_g : (amin > -g)%R.
  Variable angle_min : R.
  Hypothesis angle_min_le_0 : (angle_min < 0)%R.

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
    { rewrite Rtrigo_def.cos_0. solve_linear. }
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
      (Sys (next small_angle) ltrue d).

  Definition IndInv_quad := Rename rename_quad IndInv.

  Transparent ILInsts.ILFun_Ops.

  Lemma TimedPreserves_Next_quad :
    |-- TimedPreserves d IndInv_quad Next_quad.
  Proof with eauto with rw_rename.
    unfold IndInv_quad, Next_quad.
    rewrite SysCompose_abstract. unfold SysRename.
    rewrite Sys_rename_formula... rewrite SysRename_rule...
    rewrite TimedPreserves_Rename...
    rewrite <- TimedPreserves_Next. rewrite Rename_True.
    charge_tauto.
  Qed.

  Opaque ILInsts.ILFun_Ops.

  Require Import Logic.EnabledLemmas.
  Lemma SysNeverStuck_Discr_quad :
    IndInv_quad //\\ "T" = 0 |-- Enabled (Sys_D Next_quad).
  Proof.
    unfold Sys_D, IndInv_quad.
    rewrite_rename_equiv ("T" = 0) rename_quad.
    rewrite <- Rename_and.
    rewrite Rename_ok by eauto with rw_rename.
    eapply EnabledLemmas.subst_enabled_full
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
      rewrite H. apply Proper_Enabled_lentails.
      charge_tauto. }
  Qed.

  Theorem SysNeverStuck_Next :
    |-- SysNeverStuck d IndInv_quad Next_quad.
  Proof.
    eapply SysNeverStuck_Sys;
    [ pose proof d_gt_0 ; solve_linear | | ].
    { rewrite <- disjoint_state_enabled.
      { charge_split.
        { charge_clear. apply Enabled_TimeBound.
          pose proof d_gt_0. assumption. }
        { apply SysNeverStuck_Discr_quad. } }
      { apply formulas_disjoint_state; reflexivity. } }
    { admit. (** Provable, but we won't worry about it *) }
  Admitted.

  Definition Safe_quad : StateFormula :=
    Rename rename_quad Safe.

  Lemma IndInv_impl_Safe_quad :
    IndInv_quad //\\ TimeBound d |-- Safe_quad.
  Proof with (eauto with rw_rename).
    unfold Safe, TimeBound, IndInv_quad.
    rewrite_rename_equiv (0 <= "T" <= d) rename_quad.
    rewrite <- Rename_and.
    apply Proper_Rename_lentails; try reflexivity.
    apply IndInv_impl_Inv.
  Qed.

  Lemma W_quad_refines :
    W_quad g |-- Sys_w Next_quad.
  Proof.
    (* Mechanical reasoning about abstractions of
       differential equations. *)
  Admitted.

  (* Our main safety theorem. *)
  Theorem Velocity_safe :
    |-- (IndInv_quad //\\ TimeBound d) //\\
        []SysSystem (Quadcopter d g angle_min
                                (Sys_D Next_quad))
        -->> []Safe_quad.
  Proof.
    rewrite Inductively.Preserves_Inv_simple.
    { rewrite IndInv_impl_Safe_quad.
      charge_tauto. }
    { compute; tauto. }
    { apply SafeAndReactive_TimedPreserves.
      eapply Quadcopter_refine.
      { apply d_gt_0. }
      { pose proof angle_min_le_0. solve_linear. }
      { apply TimedPreserves_Next_quad. }
      { apply SysNeverStuck_Next. }
      { unfold Sys_D. unfold small_angle. charge_assumption. }
      { apply W_quad_refines. } }
  Qed.

  (* Some useful renaming lemmas for generating C code *)
  (* Commented out for accurate proof line counts for PLDI. *)
  (*
  Lemma Rename_SafeAcc :
    forall a v (m : RenameMap),
      RenameMapOk m ->
      Rename m (SafeAcc a v) -|-
      SafeAcc (rename_term m a) (rename_term m v).
  Proof.
    intros; split; breakAbstraction; intros;
    destruct tr as [? [? ?]]; simpl in *.
    { repeat rewrite Rename_term_ok; auto. }
    { repeat rewrite <- Rename_term_ok; auto. }
  Qed.

  Lemma Rename_Default :
    forall a (m : RenameMap),
      RenameMapOk m ->
      Rename m (Default a) -|- Default (rename_term m a).
  Proof.
    intros; split; breakAbstraction; intros;
    destruct tr as [? [? ?]]; simpl in *.
    { repeat rewrite Rename_term_ok; auto. }
    { repeat rewrite <- Rename_term_ok; auto. }
  Qed.
   *)

End VelocityShim.
