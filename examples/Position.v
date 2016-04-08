Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import Logic.Logic.
Require Import Logic.ProofRules.
Require Import Logic.ArithFacts.
Require Import Examples.System.
Require Import Examples.UtilPosition.
Require Import Examples.DiffEqSolutions.

Open Scope HP_scope.
Open Scope string_scope.

Module Type PositionShimParams <: SdistParams.

  (* The upper bound on y. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  (* Our breaking acceleration. *)
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

End PositionShimParams.

Module PositionShim (Import Params : PositionShimParams).

  Module SdistUtil := SdistUtil(Params).
  Import SdistUtil.

  (* The continuous dynamics of the system *)
  Definition w : state->Formula :=
    fun st' =>
      st' "y" = "v" //\\ st' "v" = "a" //\\ st' "a" = 0.

  Definition Safe : Formula :=
    "y" <= ub.
  
  Definition SafeAcc (a : Term) (d : Term) : Formula :=
    Forall t : R,
      (0 <= t //\\ t <= d) -->>
      "y" + tdist "v" a t + sdist MAX("v" + a*t, 0) <= ub.

  Definition SafeAccZeroOrder (a : Term) (d : Term)
    : Formula :=
    (0 <= "v" + a*d -->>
     "y" + tdist "v" a d + sdist ("v" + a*d) <= ub) //\\
    (("v" + a*d <= 0 //\\ 0 < "v") -->>
     "y" + tdist "v" a (--"v"/a) <= ub).

  Definition Ctrl := SafeAccZeroOrder "a"! d.

  Definition IndInv := SafeAcc "a" "T".

  Definition Next : Formula :=
    Sys (Ctrl //\\ Unchanged ("v"::"y"::nil)) w d.

  Lemma SafeAccZeroOrder_refines :
    forall a,
      SafeAccZeroOrder a d //\\ "y" <= ub //\\ SafeAcc amin d
      |-- SafeAcc a d.
  Proof.
    intros. reason_action_tac.
    pose proof d_gt_0.
    unfold Rbasic_fun.Rmax. destruct_ite.
    - rewrite_real_zeros.
      destruct (RIneq.Rlt_dec 0 (pre "v"))%R.
      + assert (pre "v" + eval_term a pre post * d <= 0)%R
          by solve_nonlinear. intuition.
        assert (eval_term a pre post <> 0%R)
          by solve_nonlinear. intuition.
        eapply Rle_trans; eauto.
        field_simplify; auto. simpl.
        apply Rmult_le_reg_r with (r:=2%R);
          [ solve_linear | ].
        apply Rmult_le_reg_r
        with (r:=(-(eval_term a pre post))%R);
          [ solve_nonlinear | ].
        repeat rewrite Ropp_mult_distr_r_reverse.
        field_simplify; auto. simpl.
        unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
        solve_nonlinear.
      + solve_nonlinear.
    - destruct (RIneq.Rle_dec
                  (pre "v" + eval_term a pre post * d) 0)%R.
      + destruct (RIneq.Rlt_dec 0 (pre "v"))%R.
        * intuition.
          assert (eval_term a pre post <> 0%R)
            by solve_nonlinear. intuition.
          pose proof amin_lt_0.
          assert (amin <> 0%R) by solve_linear.
          destruct
            (RIneq.Rle_dec amin (eval_term a pre post)).
          { eapply Rle_trans; eauto.
            field_simplify; auto. simpl.
            apply Rmult_le_reg_r with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_r
            with (r:=(-(eval_term a pre post))%R);
              [ solve_nonlinear | ].
            apply Rmult_le_reg_r with (r:=(-amin)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_r_reverse.
            field_simplify; auto. simpl.
            unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
            clear - r1. solve_nonlinear. }
          { specialize (H6 0%R). specialize_arith_hyp H6.
            revert H6. unfold Rbasic_fun.Rmax.
            repeat destruct_ite; rewrite_real_zeros.
            { solve_linear. }
            { intros. eapply Rle_trans; eauto.
              assert (pre "v"+eval_term a pre post*x > 0)%R
                by solve_linear.
              field_simplify; auto. simpl.
              apply Rmult_le_reg_r with (r:=2%R);
                [ solve_linear | ].
              apply Rmult_le_reg_r
              with (r:=(-(eval_term a pre post))%R);
                [ solve_nonlinear | ].
              apply Rmult_le_reg_r with (r:=(-amin)%R);
                [ solve_linear | ].
              repeat rewrite Ropp_mult_distr_r_reverse.
              field_simplify; auto. simpl.
              unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
              clear - H9 n0 H7 H1 H. solve_nonlinear. } }
        * solve_nonlinear.
      + assert (0 <= pre "v" + eval_term a pre post * d)%R
          as Hvd by solve_linear. intuition.
        destruct
            (RIneq.Rle_dec amin (eval_term a pre post)).
        { eapply Rle_trans; eauto.
          pose proof amin_lt_0.
          assert (amin <> 0%R) by solve_linear.
          assert (0 <= pre "v" + eval_term a pre post * x)%R
            as Hvx by solve_linear.
          apply Rmult_le_reg_l with (r:=(-amin)%R);
            [ solve_linear | ].
          ring_simplify; simpl; field_simplify; auto; simpl.
          apply Rmult_le_reg_r with (r:=2%R);
            [ solve_linear | ].
          field_simplify; simpl.
          unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
          clear - Hvd Hvx H4 r. solve_nonlinear. }
        { pose proof amin_lt_0.
          assert (amin <> 0%R) by solve_linear.
          specialize (H6 0%R). specialize_arith_hyp H6.
          revert H6. unfold Rbasic_fun.Rmax.
          repeat destruct_ite; rewrite_real_zeros.
          { intros. eapply Rle_trans; eauto.
            assert (pre "v"+eval_term a pre post*x > 0)%R
              by solve_linear.
            field_simplify; auto. simpl.
            apply Rmult_le_reg_r with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_r
            with (r:=(-(eval_term a pre post))%R);
              [ solve_nonlinear | ].
            apply Rmult_le_reg_r with (r:=(-amin)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_r_reverse.
            field_simplify; auto. simpl.
            unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
            clear - H8 r H5 n1 H. solve_nonlinear. }
          { intros. eapply Rle_trans; eauto.
            assert (pre "v"+eval_term a pre post*x > 0)%R
              by solve_linear.
            field_simplify; auto. simpl.
            apply Rmult_le_reg_r with (r:=2%R);
              [ solve_linear | ].
            apply Rmult_le_reg_r
            with (r:=(-(eval_term a pre post))%R);
              [ solve_nonlinear | ].
            apply Rmult_le_reg_r with (r:=(-amin)%R);
              [ solve_linear | ].
            repeat rewrite Ropp_mult_distr_r_reverse.
            field_simplify; auto. simpl.
            unfold Rdiv. repeat rewrite RMicromega.Rinv_1.
            clear - H8 n2 H5 n1 H. solve_nonlinear. } }
  Qed.

  Lemma SafeAcc_downclock :
    forall a t1 t2,
      t1 <= t2 //\\ SafeAcc a t2 |-- SafeAcc a t1.
  Proof.
    intros. reason_action_tac. intuition.
    apply H2. solve_linear.
  Qed.

  Lemma SafeAcc_Safe :
    forall a d,
      0 <= d //\\ SafeAcc a d |-- "y" <= ub.
  Proof.
    intros. reason_action_tac. intuition. specialize (H1 R0).
    specialize_arith_hyp H1. rewrite_real_zeros.
    unfold Rbasic_fun.Rmax in *. revert H1. destruct_ite.
    { rewrite_real_zeros. auto. }
    { intros. assert (-/2 < 0)%R by solve_linear.
      assert (/amin < 0)%R by (pose proof amin_lt_0; solve_linear).
      generalize dependent (-/2)%R.
      generalize dependent (/amin)%R.
      intros. solve_nonlinear. }
  Qed.

  Lemma SafeAcc_amin :
    forall a,
      SafeAcc a 0 |-- SafeAcc amin d.
  Proof.
    intros. reason_action_tac. specialize (H R0).
    specialize_arith_hyp H. revert H.
    unfold Rbasic_fun.Rmax. repeat destruct_ite.
    { rewrite_real_zeros. intros.
      pose proof (tdist_vel_neg "v" amin x).
      breakAbstraction.
      specialize
        (H1 (Stream.Cons pre (Stream.forever (fun _ => R0)))).
      simpl in *. solve_linear. }
    { rewrite_real_zeros. intros. pose proof amin_lt_0.
      solve_nonlinear. }
    { rewrite_real_zeros. intros.
      pose proof (sdist_tdist "v" x). breakAbstraction.
      specialize
        (H1 (Stream.Cons pre (Stream.forever (fun _ => R0)))).
      simpl in *. solve_linear. }
    { rewrite_real_zeros. intros. pose proof amin_lt_0.
      pose proof (sdist_tdist_tdist "v" x).
      specialize
        (H2 (Stream.Cons pre (Stream.forever (fun _ => R0)))).
      simpl in *. solve_linear. }
  Qed.

  Theorem TimedPreserves_Next :
    |-- TimedPreserves d IndInv Next.
  Proof.
    pose proof amin_lt_0 as amin_lt_0.
    pose proof d_gt_0 as d_gt_0.
    eapply Preserves_Sys; [ refine _ | | ].
    { simpl next; restoreAbstraction.
      unfold World.
      zero_deriv_tac "a".
      pose proof solve_dbl_int.
      apply (Proper_Rename_lentails {{ "t" ~> --"T" }}%rn
                                    {{ "t" ~> --"T" }}%rn) in H;
        [ | reflexivity ].
      rewrite <- Rename_Continuous_deriv_term'
        in H by sysrename_side_cond.
      rewrite <- Rename_ok in H by rw_side_condition.
      simpl rename_formula in H. restoreAbstraction.
      match type of H with
      | Continuous ?eqs |-- _ =>
        assert (mkEvolution w |-- eqs)
      end.
      { apply Evolution_lentails_lentails.
        red. clear H. intros. apply lforallR. intros.
        rewrite <- Rename_ok by rw_side_condition.
        simpl rename_formula. restoreAbstraction.
        simpl deriv_term_RenameList. unfold deriv_term_succeed.
        simpl deriv_term.
        simpl. restoreAbstraction. breakAbstraction.
        solve_linear.
        pose proof (H0 "y"). simpl in *. congruence.
        pose proof (H0 "v"). simpl in *. congruence.
        pose proof (H0 "a"). simpl in *. congruence.
        pose proof (H0 "t"). simpl in *. solve_linear. }
      rewrite H0. clear H0. rewrite H. clear H.
      unfold IndInv, SafeAcc. simpl next.
      restoreAbstraction.
      charge_split.
      { apply lforallR. intro.
        charge_intros; reason_action_tac; intuition;
        match goal with
        | [ H : forall _ : R, _ |- _ ]
          => specialize (H (x + pre "T" - post "T")%R)
        end; intuition;
        repeat match goal with
               | [ H : eq _ _ |- _ ]
                 => rewrite H in *
               end.
        specialize_arith_hyp H12.
        unfold Rbasic_fun.Rmax in *. revert H12.
        repeat destruct_ite; solve_linear. }
      { solve_linear. } }
    { unfold Discr, Ctrl, IndInv. rewrite next_And.
      pose proof (SafeAcc_downclock "a" "T" d).
      apply next_st_formula_entails in H;
        [ | simpl; tauto | simpl; tauto ].
      rewrite <- H. clear H. rewrite next_And.
      pose proof (SafeAccZeroOrder_refines "a").
      apply next_st_formula_entails in H;
      [ | simpl; tauto | simpl; tauto ].
      rewrite <- H. clear H.
      charge_assert (0 <= "T" //\\ SafeAcc "a" "T");
        [ charge_split; [ solve_linear | charge_assumption ] | ].
      rewrite (SafeAcc_downclock "a" 0 "T").
      rewrite SafeAcc_amin.
      charge_assert (0 <= "T" //\\ SafeAcc "a" "T");
        [ charge_split; [ solve_linear | charge_assumption ] | ].
      rewrite SafeAcc_Safe.
      charge_intros. charge_split.
      { charge_split.
        { simpl next. restoreAbstraction. charge_tauto. }
        { repeat rewrite next_And.
          breakAbstraction.
          intuition;
            repeat match goal with
                   | [ H : eq _ _ |- _ ]
                     => rewrite H
                   end; solve_linear. } }
      { simpl next. restoreAbstraction. charge_assumption. } }
  Qed.

  (* A proof that the inductive safety condition
     Inv implies the safety contition
     we actually care about, Safe. *)
  Lemma IndInv_impl_Safe :
    IndInv //\\ TimeBound d |-- Safe.
  Proof.
    pose proof d_gt_0.
    pose proof amin_lt_0.
    breakAbstraction. intuition.
    specialize (H2 R0). rewrite_real_zeros. intros.
    destruct (Rle_dec R0 (Stream.hd tr "v")).
    - intuition. specialize_arith_hyp H3.
      simpl_Rmax.
      assert (- / 2 < 0)%R by solve_linear.
      assert (/amin < 0)%R by solve_linear.
      generalize dependent (-/2)%R.
      generalize dependent (/amin)%R.
      intros. eapply Rle_trans; eauto.
      clear H3. solve_nonlinear.
    - simpl_Rmax. rewrite_real_zeros.
      solve_linear.
  Qed.

  Lemma SafeAcc_ZeroOrder_amin :
    forall a,
      SafeAcc a 0 |-- SafeAccZeroOrder amin d.
  Proof.
    unfold SafeAcc, SafeAccZeroOrder.
    pose proof amin_lt_0. pose proof d_gt_0.
    intros. reason_action_tac. split.
    { specialize (H1 R0). intros. specialize_arith_hyp H1.
      rewrite_real_zeros. assert (pre "v" > 0)%R by solve_nonlinear. simpl_Rmax.
      pose proof (sdist_tdist_tdist "v" d (Stream.Cons pre (Stream.forever (fun _ => R0)))).
      breakAbstraction. solve_linear. }
    { specialize (H1 0)%R. intros. rewrite_real_zeros. simpl_Rmax.
      pose proof (sdist_tdist "v" (- pre "v" * / amin)%R
                              (Stream.Cons pre (Stream.forever (fun _ => R0)))).
      breakAbstraction. solve_linear. }
  Qed.

  Definition Constraint := amin <= "a".

  Lemma SysNeverStuck_Discr :
    IndInv //\\ "T" = 0
    |-- Enabled ((0 <= "T"! <= d //\\ Sys_D Next) //\\
                  next Constraint).
  Proof.
    charge_assert (SafeAcc "a" 0).
    { rewrite <- (SafeAcc_downclock "a" 0 "T").
      solve_linear. }
    rewrite SafeAcc_ZeroOrder_amin. charge_clear.
    charge_intros. enable_ex_st'. pose proof d_gt_0.
    do 3 eexists; exists d; solve_linear.
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

End PositionShim.