Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import TLA.TLA.
Require Import TLA.ProofRules.
Require Import TLA.ArithFacts.
Require Import Examples.System2.
Require Import Examples.SecondDerivUtil.

Open Scope HP_scope.
Open Scope string_scope.

Module Type SecondDerivShimParams <: SdistParams.

  (* The upper bound on y. *)
  Parameter ub : R.
  (* Max time between executions of the
     controller. *)
  Parameter d : R.
  Parameter d_gt_0 : (d > 0)%R.
  (* Our breaking acceleration. *)
  Parameter amin : R.
  Parameter amin_lt_0 : (amin < 0)%R.

End SecondDerivShimParams.

Module SecondDerivShimCtrl (Import Params : SecondDerivShimParams).

  Module SdistUtil := SdistUtil(Params).
  Import SdistUtil.

  (* The continuous dynamics of the system *)
  Definition w : state->Formula :=
    fun st' =>
      st' "y" = "v" //\\ st' "v" = "a" //\\ st' "a" = 0.

  Definition Ctrl : Formula :=
    "y" + tdist "v" MAX("a"!,0) d +
    sdist MAX("v" + MAX("a"!,0)*d,0) <= ub
    \\// ("a"! <= amin).

  Definition Safe : Formula :=
    "y" <= ub.

  Definition IndInv : Formula :=
    Forall t : R,
      0 <= t <= "T" -->>
      "y" + (tdist "v" "a" t) + sdist MAX("v" + "a"*t,0) <= ub.

  Definition Next : Formula :=
    Sys (Ctrl //\\ Unchanged ("v"::"y"::nil)) w d.

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

Ltac simpl_Rmax :=
  repeat first [rewrite Rbasic_fun.Rmax_left in * by solve_linear |
                rewrite Rbasic_fun.Rmax_right in * by solve_linear ].

Ltac rewrite_real_zeros :=
  repeat (first
   [ rewrite Rmult_0_r in *
   | rewrite Rmult_0_l in *
   | rewrite Rplus_0_r in *
   | rewrite Rplus_0_l in *
   | rewrite Rminus_0_r in *
   | rewrite Rminus_0_l in * ]).

Lemma SafeAccZeroOrder_abstracts :
    forall a,
      SafeAcc a d |-- SafeAccZeroOrder a d.
Proof.
  unfold SafeAcc, SafeAccZeroOrder.
  intros. reason_action_tac.
  split.
  { specialize (H d). pose proof d_gt_0.
    intros. specialize_arith_hyp H.
    simpl_Rmax. auto. }
  { generalize dependent (eval_term a pre post);
    clear a; intro a; intros.
    specialize (H ((0 - pre "v") * / a))%R.
    pose proof d_gt_0.
    assert (a <> R0) by solve_nonlinear.
    rewrite Rbasic_fun.Rmax_right in H.
    { rewrite_real_zeros. apply H.
      assert (eq (a * / a) R1)%R by (apply Rinv_r; auto).
      solve_nonlinear. }
    { assert (eq (a * / a) R1)%R by (apply Rinv_r; auto).
      solve_nonlinear. } }
Qed.

Let mirror : RenameList :=
    {{ "y" ~> --"y" & "v" ~> --"v" & "a" ~> --"a" }}%rn.

Lemma Enabled_action' : forall P Q,
    is_st_formula Q ->
    (forall st,
        eval_formula Q (Stream.forever st) ->
        exists st',
          eval_formula P (Stream.Cons st (Stream.forever st'))) ->
    Q |-- Enabled P.
Proof.
  breakAbstraction; intros.
  specialize (H0 (Stream.hd tr)).
  eapply st_formula_hd in H1;
    [ apply H0 in H1 | assumption | reflexivity ]. 
  destruct H1. exists (Stream.forever x). auto.
Qed.

Ltac enable_ex_st' :=
  match goal with
  | |- _ |-- Enabled ?X =>
        let vars := eval compute in (remove_dup (get_next_vars_formula X)) in
        let rec foreach ls :=
         (match ls with
          | ?l :: ?ls => eapply (ex_state l); simpl; foreach ls
          | _ => idtac
          end) in
        eapply Enabled_action'; [ tlaIntuition | ]; simpl; intros; foreach vars
  end; try (eapply ex_state_any; (let st := fresh in
                                  intro st; clear st)).

Definition Next' : ActionFormula :=
  Sys (SafeAccZeroOrder "a"! d) w d.

Parameter spread : (-/2 * amin*d*d + amin*amin*d*d*-/2*/amin < 2*ub)%R.

Lemma inv_2 : (eq (2 * /2) R1)%R.
Proof. solve_linear. Qed.
Lemma inv_amin : (eq (amin * /amin) R1)%R.
Proof. pose proof amin_lt_0. solve_linear. Qed.

Ltac generalize_inv_2_amin :=
  pose proof inv_2; pose proof inv_amin;
  generalize dependent (/2)%R;
  generalize dependent (/amin)%R; intros.

Lemma Rmult_le_algebra_neg : forall r1 r2 r3,
  (r2 < 0 -> r1 >= r2*r3 -> r1 * (/r2) <= r3)%R.
Proof.
  intros.
  apply (Rmult_le_reg_r (-r2)%R); solve_linear.
  rewrite Rmult_assoc.
  rewrite Ropp_mult_distr_r_reverse.
  rewrite <- Rinv_l_sym; solve_linear.
Qed.


Lemma velocity_thing :
  forall ubv,
    (ubv > 0)%R ->
    (ubv*d + ubv*ubv*(0 - / 2)*(/amin) <= ub)%R ->
    "v" <= ubv //\\
    "v" + "a"!*d <= ubv //\\
    ("y" > 0 -->> SafeAccZeroOrder "a"! d)
    |-- SafeAccZeroOrder "a"! d.
Proof.
  pose proof d_gt_0 as d_gt_0. pose proof amin_lt_0 as amin_lt_0.
  intros. reason_action_tac.
  destruct H1 as [Hubv1 [Hubv2 Hctrl]].
  destruct (Rgt_dec (pre "y") R0).
  { auto. }
  { clear Hctrl. split; intros.
    { eapply Rle_trans; eauto.
      pose proof (sdist_incr (pre "v" + post "a" * d)
                    ubv (Stream.forever (fun _ => R0)) I).
      breakAbstraction. specialize_arith_hyp H2. rewrite H2.
      assert ((pre "v" * d + / 2 * post "a" * (d * (d * 1))) <=
              ubv * d)%R.
      { clear - Hubv1 Hubv2 H d_gt_0. solve_nonlinear. }
      { solve_linear. } }
    { transitivity (ubv*d)%R.
      { field_simplify; [ | solve_nonlinear ].
        apply Rmult_le_algebra_neg; [ solve_nonlinear | ].
        unfold Rdiv. rewrite RMicromega.Rinv_1. simpl.
        clear - Hubv1 d_gt_0 H1 n. solve_nonlinear. }
      { assert ((0 - / 2) < 0)%R by solve_linear.
        assert (/amin < 0)%R by solve_linear.
        generalize dependent (/amin)%R.
        generalize dependent (0-/2)%R. intros.
        clear - H0 H2 H3 H. solve_nonlinear. } } }
Qed.

(*
Lemma velocity_thing :
  forall ubv,
    (ubv > 0)%R ->
    (ubv*d + ubv*ubv*(0 - / 2)*(/amin) <= ub)%R ->
    "v" <= ubv //\\
    "v" + "a"!*d <= ubv //\\
    ("y" > 0 -->> Ctrl)
    |-- Ctrl.
Proof.
  pose proof d_gt_0 as d_gt_0. pose proof amin_lt_0 as amin_lt_0.
  intros. reason_action_tac.
  destruct H1 as [Hubv1 [Hubv2 Hctrl]].
  destruct (Rgt_dec (pre "y") R0).
  { auto. }
  { clear Hctrl. left. eapply Rle_trans; eauto.
    pose proof (sdist_incr
                  (Rbasic_fun.Rmax
                     (pre "v"+Rbasic_fun.Rmax (post "a") 0 * d) 0)
                  ubv (Stream.forever (fun _ => R0)) I).
    breakAbstraction.
    rewrite H1; clear H1.
    { assert (pre "v" * d +
              / 2 * Rbasic_fun.Rmax (post "a") 0 * (d*(d*1))
              <= ubv * d)%R.
      { unfold Rbasic_fun.Rmax; destruct_ite.
        { rewrite_real_zeros. solve_linear. }
        { clear - Hubv1 Hubv2 H d_gt_0. solve_nonlinear. } }
      { solve_linear. } }
    { unfold Rbasic_fun.Rmax; repeat destruct_ite;
      solve_linear. } }
Qed.
*)

Lemma upper_lower :
  forall ubv : R,
       (ubv > 0)%R ->
       (ubv * d + ubv * ubv * (0 - / 2) * / amin <= ub)%R ->
  |-- SysNeverStuck d (SafeAcc "a" "T" //\\ Rename mirror (SafeAcc "a" "T"))
      (SysCompose Next' (SysRename mirror (deriv_term_RenameList mirror) Next')).
Proof.
  intros. pose proof d_gt_0. pose proof amin_lt_0.
  eapply SysNeverStuck_Sys'; [ tlaIntuition | solve_linear | | ].
  { rewrite Rename_ok by eauto with rw_rename.
    rewrite <- (velocity_thing _ H H0).
    repeat rewrite <- Rename_ok by eauto with rw_rename.
    enable_ex_st.

Lemma upper_lower :
forall ubv : R,
       (ubv > 0)%R ->
       (ubv * d + ubv * ubv * (0 - / 2) * / amin <= ub)%R ->
  |-- SysNeverStuck d (IndInv //\\ Rename mirror IndInv)
                     (SysCompose Next (SysRename mirror (deriv_term_RenameList mirror) Next)).
Proof.
  intros.
  pose proof d_gt_0. pose proof amin_lt_0.
  eapply SysNeverStuck_Sys'; [ tlaIntuition | solve_linear | | ].
  { rewrite Rename_ok by eauto with rw_rename.
    rewrite <- (velocity_thing _ H H0).
    repeat rewrite <- Rename_ok by eauto with rw_rename.
    enable_ex_st.

    

rewrite <- H3 at 1. rewrite <- velocity_thing. enable_ex_st'. destruct H1 as [[Hinvpos Hinvneg] HT].
    unfold subst_state in *. simpl in *.
    specialize (Hinvpos R0). specialize (Hinvneg R0).
    specialize_arith_hyp Hinvpos. specialize_arith_hyp Hinvneg.
    exists (st "y"). exists (st "v").
    destruct (RIneq.Rle_dec 0 (st "v")).
    { destruct (RIneq.Rle_dec (st "y" + st "v" * d + st "v" * st "v" * (0 - /2) * /amin) ub).
      { exists 0%R. exists 0%R. simpl_Rmax.
        rewrite_real_zeros. solve_nonlinear. }
      { exists amin. exists 0%R. simpl_Rmax.
        rewrite_real_zeros. solve_linear.
        unfold Rbasic_fun.Rmax; destruct_ite.
        { rewrite_real_zeros. solve_nonlinear. }
        { left.
          z3_solve; admit. } } }
        rewrite Rbasic_fun.Rmax_right.

Lemma upper_lower :
  |-- SysNeverStuck d (SafeAcc "a" "T" //\\ Rename mirror (SafeAcc "a" "T"))
      (SysCompose Next' (SysRename mirror (deriv_term_RenameList mirror) Next')).
Proof.
  pose proof d_gt_0 as d_gt_0. pose proof amin_lt_0 as amin_lt_0.
  pose proof spread as spread.
  eapply SysNeverStuck_Sys; [ solve_linear | | ].
  { enable_ex_st'. destruct H as [[Hinvpos Hinvneg] HT].
    unfold subst_state in *. simpl in *.
    rewrite HT in *; clear HT. rewrite_real_zeros.
    specialize (Hinvpos R0). specialize (Hinvneg R0).
    specialize_arith_hyp Hinvpos. specialize_arith_hyp Hinvneg.
    destruct (Rle_dec R0 (st "v")); simpl_Rmax.
    { destruct (Rle_dec R0 (st "v" + amin * d)).
      { exists amin. exists d. split; [ solve_linear | ].
        rewrite_real_zeros. rewrite Ropp_involutive.
        solve_linear.
        - generalize_inv_2_amin.
          clear - H0 Hinvpos H1. eapply Rle_trans; eauto.
          clear Hinvpos. solve_nonlinear.
        - apply Rmult_le_reg_r with (r:=2%R);
          [ solve_linear | ].
          apply Rmult_le_reg_r with (r:=(-amin)%R);
            [ solve_linear | ].
          field_simplify. admit.
(*generalize_inv_2_amin. clear - H2 Hinvpos H. eapply Rle_trans; eauto.
          clear Hinvpos. solve_nonlinear.*) z3_solve; admit.
        - assert (eq (- st "v" + - amin * d) R0)%R by solve_linear.
          rewrite H0. rewrite_real_zeros. generalize_inv_2_amin.
          clear -Hinvneg r r0 amin_lt_0 H1 H2 d_gt_0. solve_nonlinear. z3_solve; admit. }
      { destruct r.
        { exists (st "v"*st "v"/(2*(st "y"-ub)))%R. exists d.
          split; [ solve_linear | ].
          rewrite_real_zeros. rewrite Ropp_involutive.
          solve_linear.
          - z3_solve; admit.
          - z3_solve; admit.
          - z3_solve; admit. }
        { rewrite <- H in *; clear H.
          exists R0. exists d. rewrite_real_zeros.
          repeat split; try solve [solve_linear].
          intros. exfalso. solve_linear. } } }
    { destruct (Rge_dec R0 (st "v" - amin * d)).
      { exists (-amin)%R. exists d. split; [ solve_linear | ].
        rewrite_real_zeros. rewrite Ropp_involutive.
        solve_linear.
        - z3_solve; admit.
        - z3_solve; admit.
        - z3_solve; admit. }
      { exists (st "v"*st "v"/(2*(ub+st "y")))%R. exists d.
        split; [ solve_linear | ].
        rewrite_real_zeros. rewrite Ropp_involutive.
        assert (st "v" < 0)%R by solve_linear.
        solve_linear.
        - z3_solve; admit.
        - z3_solve; admit.
        - z3_solve; admit. } } }
  { admit. }
Qed.
        
  

Lemma upper_lower :
  |-- SysNeverStuck d (IndInv //\\ Rename mirror IndInv)
                     (SysCompose Next (SysRename mirror (deriv_term_RenameList mirror) Next)).
Proof.
  pose proof d_gt_0. pose proof amin_lt_0.
  eapply SysNeverStuck_Sys; [ solve_linear | | ].
  { enable_ex_st'. destruct H1 as [[Hinvpos Hinvneg] HT].
    unfold subst_state in *. simpl in *.
    specialize (Hinvpos R0). specialize (Hinvneg R0).
    specialize_arith_hyp Hinvpos. specialize_arith_hyp Hinvneg.
    exists (st "y"). exists (st "v").
    destruct (RIneq.Rle_dec 0 (st "v")).
    { destruct (RIneq.Rle_dec (st "y" + st "v" * d + st "v" * st "v" * (0 - /2) * /amin) ub).
      { exists 0%R. exists 0%R. simpl_Rmax.
        rewrite_real_zeros. solve_nonlinear. }
      { exists amin. exists 0%R. simpl_Rmax.
        rewrite_real_zeros. solve_linear.
        unfold Rbasic_fun.Rmax; destruct_ite.
        { rewrite_real_zeros. solve_nonlinear. }
        { left. assert (amin > -(st "v") / d)%R by admit. z3_solve.
        rewrite Rbasic_fun.Rmax_right.


        { rewrite Rbasic_fun.Rmax_left by reflexivity.
          rewrite Rbasic_fun.Rmax_left by solve_linear.
          rewrite_real_zeros. left. 

exists amin. exists 0%R.
        solve_linear.
        replace (Rbasic_fun.Rmax (0 - amin) 0)%R with (-amin)%R
          by (unfold Rbasic_fun.Rmax; destruct_ite; solve_linear).
        
        

  (* A proof that the inductive safety condition
     Inv implies the safety contition
     we actually care about, Safe. *)
  Lemma inv_safe : IndInv //\\ TimeBound d |-- Safe.
  Proof.
    pose proof amin_lt_0.
    pose proof d_gt_0.
    tlaAssert (0 <= tdiff <= d);
    [ solve_linear | tlaIntro ].
    breakAbstraction; simpl; unfold eval_comp; simpl; intros.
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    specialize (H7 ((Stream.hd tr) "T" - (Stream.hd tr) "t"))%R.
    destruct (Rle_dec R0
                      ((Stream.hd tr) "V"+
                       (Stream.hd tr) "a"*
                       ((Stream.hd tr) "T" - (Stream.hd tr) "t"))%R);
      intuition.
    - eapply Rle_trans; eauto.
      rewrite <- Rplus_0_r with (r:=(Stream.hd tr) "y").
      apply Rplus_le_compat.
      + solve_linear.
      + rewrite Rmult_assoc.
        apply Rmult_0_le; solve_linear.
        apply pow_0_le.
        assert (/ amin < 0)%R by solve_linear.
        solve_linear.
    - assert
        (((Stream.hd tr) "V" +
          (Stream.hd tr) "a" *
          ((Stream.hd tr) "T" - (Stream.hd tr) "t") < 0)%R)
        by solve_linear.
      eapply Rle_trans; eauto.
      solve_linear.
  Qed.

  Lemma SysSafe_ctrl : forall P, P |-- SysSafe SpecR.
  Proof.
    intros.
    apply SysSafe_rule; apply always_tauto.
    enable_ex_st; repeat eexists; solve_linear.
  Qed.

  Theorem ctrl_safe :
    []"Vmax" >= "v" //\\ []"Ymax" >= "y" |-- Spec -->> []Safe.
  Proof.
    pose proof amin_lt_0 as amin_lt_0.
    pose proof d_gt_0 as d_gt_0.
    tlaIntro.
    eapply Sys_by_induction
    with (IndInv:=IndInv) (A:="Vmax" >= "v" //\\ "Ymax" >= "y").
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - tlaIntuition.
    - apply SysSafe_ctrl.
    - charge_apply ind_inv_init. charge_tauto.
    - tlaIntuition.
    - charge_apply inv_safe. charge_tauto.
    - unfold InvariantUnder, IndInv, Max. simpl.
      restoreAbstraction. unfold tdist, sdist.
      solve_linear; rewrite_next_st; solve_linear;
      specialize (H3 x); solve_linear.
    - simpl BasicProofRules.next. restoreAbstraction.
      repeat charge_split;
      try (apply lforallR; intro).
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:="v" - "V" <= "a"*tdiff)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ].
        eapply diff_ind with (Hyps:=TRUE);
          try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. solve_nonlinear.
        solve_nonlinear. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. solve_nonlinear. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ].
        - unfold IndInv;
          simpl; restoreAbstraction; unfold tdist, sdist;
          solve_linear; rewrite_next_st; solve_linear;
          specialize (H5 x); solve_linear.
        - simpl deriv_formula. restoreAbstraction.
          charge_intros; repeat charge_split;
          charge_intros.
          { eapply zero_deriv with (x:="a");
            [ charge_tauto | tlaIntuition | ].
            eapply zero_deriv with (x:="V");
              [ charge_tauto | tlaIntuition | ].
            solve_linear; rewrite_next_st;
            solve_linear. }
          { solve_linear. rewrite H6. rewrite H4. rewrite H7.
            solve_linear. }
          { eapply zero_deriv with (x:="a");
            [ charge_tauto | tlaIntuition | ].
            eapply zero_deriv with (x:="V");
              [ charge_tauto | tlaIntuition | ].
            solve_linear; rewrite_next_st;
            solve_linear. }
          { solve_linear. rewrite H6. rewrite H4. rewrite H7.
            solve_linear. } }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. }
      { unfold World. eapply zero_deriv with (x:="T");
            [ charge_tauto | tlaIntuition | ].
        solve_linear. }
    - repeat charge_split.
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { fold BasicProofRules.next. unfold Discr, Ctrl, Max.
        decompose_hyps.
        { tlaAssert ("A" <= 0 \\// "A" >= 0);
          [ solve_linear | tlaIntro ].
          repeat decompose_hyps.
          apply lforallR. intro x.
          charge_split.
          - simpl. restoreAbstraction. charge_intros.
            tlaAssert (tdist "V"! "a"! x +
                       (sdist ("V"! + "a"!*x)) <=
                       tdist "Vmax" 0 d + sdist ("Vmax" + 0 * d)).
            + pose proof (tdist_sdist_incr "V"! "Vmax" "a"! 0 x d).
              charge_apply H. solve_linear.
            + solve_linear.
          - simpl. restoreAbstraction. charge_intros.
            tlaAssert ("Vmax" >= 0 \\// "Vmax" <= 0);
              [ solve_linear | tlaIntro ].
            decompose_hyps.
            + simpl. restoreAbstraction.
              tlaAssert (tdist "v" "A" x <= tdist "Vmax" 0 d).
              * pose proof (tdist_incr "v" "Vmax" "A" 0 x d).
                charge_apply H. solve_linear. rewrite_real_zeros.
                apply Rmult_0_le; solve_linear.
              * tlaIntro. solve_linear.
                eapply Rle_trans; eauto.
                repeat rewrite Rplus_assoc.
                apply Rplus_le_compat.
                { solve_linear. }
                { rewrite_next_st. eapply Rle_trans; eauto.
                  repeat rewrite <- Rplus_assoc. apply Rplus_le_r.
                  rewrite Rmult_assoc.
                  apply Rmult_0_le; solve_linear.
                  apply pow_0_le.
                  clear - amin_lt_0.
                  assert (/ amin < 0)%R by solve_linear.
                  solve_linear. }
            + tlaAssert ("y" <= ub).
              { rewrite <- inv_safe. charge_tauto. }
              { tlaAssert (tdist "v" "A" x <= 0).
                - pose proof (tdist_vel_neg "v" "A" x).
                  charge_apply H. solve_linear.
                  solve_nonlinear.
                - solve_linear. rewrite_next_st. solve_linear. }
          - tlaIntro. charge_split.
            + simpl; restoreAbstraction. tlaIntro.
              tlaAssert (tdist "V"! "a"! x +
                         (sdist ("V"! + "a"!*x)) <=
                         tdist "Vmax" "A" d +
                         sdist ("Vmax" + "A" * d)).
              *  pose proof (tdist_sdist_incr "V"! "Vmax"
                                              "a"! "A" x d).
                 charge_apply H. solve_linear.
              * solve_linear.
            + tlaAssert ("y" <= ub).
              * rewrite <- inv_safe. charge_tauto.
              * simpl; restoreAbstraction. tlaIntro.
                reason_action_tac. intuition.
                repeat match goal with
                       | [ H : eq (post _) _ |- _ ]
                         => try rewrite H in *; clear H
                       end.
                assert (pre "v" <= 0)%R;
                  [ solve_nonlinear | intros ].
                clear - H2 H3 H4 H1 H5. solve_nonlinear. }
          - unfold IndInv. unfold History.
            tlaIntro. charge_split; simpl; restoreAbstraction.
            + charge_intros.
              tlaAssert (0 <= "V" + "a" * tdiff).
              * solve_nonlinear.
              * tlaAssert (0 <= tdiff <= d);
                [ solve_linear | charge_intros ].
                reason_action_tac. intuition.
                specialize (H11 (pre "T" - pre "t"))%R.
                intuition.
                eapply Rle_trans; eauto.
                repeat match goal with
                       | [ H : eq (post _) _ |- _ ]
                         => rewrite H in *; clear H
                       end.
                rewrite Rplus_assoc.
                apply Rplus_le_compat.
                { solve_linear. }
                { pose proof (sdist_tdist_tdist "v" x).
                  breakAbstraction. unfold eval_comp in *;
                                    simpl in *.
                  specialize (H15 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  pose proof (sdist_incr "v" ("V" + "a"*tdiff)).
                  breakAbstraction. unfold eval_comp in *;
                                    simpl in *.
                  specialize (H15 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  eapply Rle_trans; [ | apply H15 ].
                  { eapply Rle_trans; eauto.
                    apply Rplus_le_compat.
                    { apply Rplus_le_compat_l.
                      repeat rewrite Rmult_assoc.
                      apply Rmult_le_compat_l; solve_linear.
                      apply Rmult_le_compat_pos_r;
                        solve_nonlinear. }
                    { apply Rmult_le_compat_neg_r;
                      solve_linear.
                      apply Rmult_le_compat_neg_r;
                      solve_linear.
                      apply Rle_sq_pos; solve_linear.
                      solve_nonlinear. } }
                  { solve_nonlinear. }
                  { solve_nonlinear. } }
            + tlaAssert ("v" >= 0 \\// "v" <= 0);
              [ solve_linear | tlaIntro ].
              decompose_hyps.
              { reason_action_tac. intuition.
                intuition.
                specialize (H9 (pre "T" - pre "t"))%R.
                intuition.
                repeat match goal with
                       | [ H : eq (post _) _ |- _ ]
                         => rewrite H in *; clear H
                       end.
                repeat match type of H23 with
                       | ?H -> _ =>
                         let HH := fresh "H" in
                         assert H as HH by solve_linear;
                           specialize (H23 HH); clear HH
                       end.
                eapply Rle_trans; eauto.
                apply Rplus_le_compat.
                { solve_linear. }
                { pose proof (sdist_tdist "v" x).
                  breakAbstraction. unfold eval_comp in *;
                                    simpl in *.
                  specialize (H13 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  pose proof (sdist_incr "v" ("V" + "a"*tdiff)).
                  breakAbstraction.
                  specialize (H13 (Stream.Cons pre
                                               (Stream.Cons
                                                  post tr))).
                  intuition. simpl in *.
                  eapply Rle_trans; [ | apply H13 ].
                  { eapply Rle_trans; eauto.
                    apply Rplus_le_compat; solve_linear.
                    repeat rewrite Rmult_assoc.
                    apply Rmult_le_compat_l;
                      solve_linear.
                    apply Rmult_le_compat_pos_r;
                      solve_linear.
                    solve_nonlinear. }
                  { solve_nonlinear. }
                  { solve_nonlinear. } } }
            { tlaAssert ("y" <= ub).
              - rewrite <- inv_safe. charge_tauto.
              - reason_action_tac. intuition.
                repeat match goal with
                     | [ H : eq (post _) _ |- _ ]
                       => rewrite H in *; clear H
                     end.
                eapply Rle_trans; eauto.
                clear - H3 amin_lt_0 H2 H6 H18.
                solve_nonlinear. } }
      { solve_linear. }
      { solve_linear. }
  Qed.


(* This was an idea for showing that the system
   is a refinement of another system that does not have
   a continuous evolution but instead replaces the continous
   evolution with the solution to the differential equations.
   This is specified by Evolve. However, I couldn't
   figure out how to prove refinement. *)

(*
  Definition Evolve : Formula :=
         "y"! = "y" + tdist "v" "a" ("t" - "t"!)
    //\\ "v"! = "v" + "a"*("t" - "t"!).

  Definition AbstractNext :=
         Evolve
    \\// (Ctrl //\\ History).

  Definition AbstractSys : Formula :=
    I //\\ []AbstractNext.

  Theorem refinement :
    |-- Spec -->> AbstractSys.
  Proof.
    unfold Spec, SpecR, AbstractSys. charge_intros.
    charge_split.
    - charge_assumption.
    - unfold SysD. simpl. restoreAbstraction.
      unfold sysD. tlaRevert. apply BasicProofRules.always_imp.
      unfold Next, AbstractNext. charge_intros.
      decompose_hyps.
      + apply lorR1. unfold Evolve.
        *)

End SecondDerivShimCtrl.

Close Scope HP_scope.
Close Scope string_scope.