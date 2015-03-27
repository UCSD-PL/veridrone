Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import TLA.ArithFacts.
Require Import Examples.System.

Open Scope HP_scope.
Open Scope string_scope.

Section SecondDerivCtrl.

  (* The upper bound on y. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.
  (* Our breaking acceleration. *)
  Variable amin : R.
  Hypothesis amin_lt_0 : (amin < 0)%R.

  (* The continuous dynamics of the system *)
  Definition w : list DiffEq :=
    ["y"' ::= "v", "v"' ::= "a"].

  Definition tdist (v:Term) (a:Term) (t:Term) : Term :=
    v*t + (/2)%R*a*t^^2.

  Definition sdist (v:Term) : Term :=
    (v^^2)*(--(/2)%R)*(/amin)%R.

(*
  Definition Max (a b : Term) (c : Term -> Formula) : Formula :=
    (a >= b //\\ (c a)) \\// (a < b //\\ c b).
*)

  Definition Max (a b : Term)
             (c : Term -> Formula) : Formula :=
    (a >= b -->> (c a)) //\\ (a <= b -->> c b).


  Definition Ctrl : Formula :=
         (Max "A" 0 (fun mx => "Ymax" + tdist "Vmax" mx d +
                               sdist ("Vmax" + mx*d)
          <= ub) //\\ "a"! = "A")
    \\// ("a"! = amin).


  Definition History : Formula :=
    "Y"! = "y" //\\ "V"! = "v" //\\ "T"! = "t"!.
(*    "Y"! = "Ymax" //\\ "V"! = "Vmax" //\\ "T"! = "t"!.*)

  Definition Safe : Formula :=
    "y" <= ub.

  Definition tdiff : Term :=
    "T" - "t".

(*
  Definition IndInv : Formula :=
    sdist "v" - sdist ("v" + "a"*tdiff) >= tdist "v" "a" tdiff.
*)

  Definition IndInv : Formula :=
    "y" - "Y" <= tdist "V" "a" tdiff //\\
    "v" - "V" <= "a"*tdiff //\\
    Syntax.Forall R
           (fun t =>
              ((0 <= t <= d //\\ 0 <= "V" + "a"*t) -->>
                    "Y" + (tdist "V" "a" t) +
                    (sdist ("V" + "a"*t)) <= ub) //\\
              ((0 <= t <= d //\\ "V" + "a"*t < 0) -->>
                     "Y" + (tdist "V" "a" t) <= ub)) //\\
   "t" <= "T" <= d.

(*
        ("a" >= 0 -->> "y" + tdist "v" "a" d +
              sdist ("v" + "a"*d) <= ub)
    //\\ ("a" <  0 -->> "y" + sdist ("v") <= ub).
*)

(*
Definition IndInv : Formula :=
    Syntax.Forall R (fun t =>
                       0 <= t <= d - "t" -->>
                       "y" + tdist "v" "a" t +
                       sdist ("v" + "a"*t) <= ub).
*)

(*    Syntax.Forall R (fun t =>
                0 <= t <= d -->>
                "Ymax" + tdist "Vmax" "a" t +
                          sdist ("Vmax" + "a"*t) <= ub).
*)
(*
  Definition IndInv : Formula :=
    ("a" <= 0 -->> "Vmax" <= 0 -->> "y" <= ub) //\\
    Max "a" 0 (fun mx => "Ymax" + tdist "Vmax" mx "t" +
                         sdist ("Vmax" + mx*"t")
                         <= ub).
*)

  Definition I : Formula := IndInv.

  Variable WC : Formula.

  Definition SpecR : SysRec :=
    {| dvars := ("a"::"Y"::"V"::"T"::nil)%list;
       cvars := ("v"::"y"::nil)%list;
       Init := I;
       Prog := Ctrl //\\ History;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Lemma tdist_sdist_incr : forall v1 v2 a1 a2 d1 d2,
      |-- v1 <= v2 -->> a1 <= a2 -->> d1 <= d2 -->>
          0 <= a2 -->> 0 <= d1 -->>
          0 <= v1 + a1*d1 -->>
          tdist v1 a1 d1 + sdist (v1 + a1*d1) <=
          tdist v2 a2 d2 + sdist (v2 + a2*d2).
  Proof.
    breakAbstraction; unfold eval_comp; simpl; intros.
    repeat match goal with
             | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
               => generalize dependent (eval_term t s1 s2)
           end; intros;
    repeat match goal with
             | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
               => generalize dependent (eval_term t s1 s2)
           end; intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin);
      auto.
    rewrite Rminus_0_l.
    apply Rmult_pos_ge_algebra with (r2:=(2)%R);
      solve_linear.
    R_simplify; simpl; solve_linear.
    clear - amin_lt_0 H3 H4 H2 H0 H1 H5.
    solve_nonlinear.
  Qed.

  Lemma tdist_incr : forall v1 v2 a1 a2 d1 d2,
  |-- v1 <= v2 -->> a1 <= a2 -->> d1 <= d2 -->>
     0 <= a2 -->> 0 <= d1 -->>
     0 <= tdist v2 a2 d2 -->>
     tdist v1 a1 d1 <= tdist v2 a2 d2.
Proof.
  clear d_gt_0.
  breakAbstraction; simpl; unfold eval_comp; simpl; intros.
  repeat match goal with
           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
             => generalize dependent (eval_term t s1 s2)
         end; intros;
  repeat match goal with
           | [ _ : context [eval_term ?t ?s1 ?s2] |- _ ]
             => generalize dependent (eval_term t s1 s2)
         end; intros.
  match goal with
      |- (?e <= _)%R
      => destruct (Rle_dec 0 e)
  end; solve_linear.
  destruct H4;
    repeat match goal with
             | [ H : @eq R _ _ |- _ ] =>
               rewrite <- H
           end; solve_linear.
  apply Rle_trans with (r2:=((r3 + /2*r2*r0)*r0)%R);
    solve_linear.
  apply Rle_trans with (r2:=((r1 + /2*r*r4)*r4)%R);
    solve_linear.
  apply Rmult_le_compat; solve_linear.
  - eapply Rmult_le_lt_0; eauto; solve_linear.
  - solve_nonlinear.
Qed.

Lemma tdist_vel_neg : forall v a t,
  |-- 0 <= t -->> v <= 0 -->> v + a*t <= 0 -->>
     tdist v a t <= 0.
Proof. solve_nonlinear. Qed.

Lemma sdist_tdist : forall v t,
    |-- tdist v amin t <= sdist v.
  Proof.
    clear d_gt_0.
    breakAbstraction; simpl; unfold eval_comp; simpl;
    intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin);
      auto.
    apply Rmult_neg_ge_algebra with (r2:=(-4)%R);
      solve_linear.
    R_simplify; solve_linear.
    solve_nonlinear.
  Qed.

Lemma sdist_tdist_tdist : forall v t,
    |-- tdist v amin t + sdist (v + amin*t) <= sdist v.
  Proof.
    clear d_gt_0.
    breakAbstraction; simpl; unfold eval_comp; simpl;
    intros.
    apply Rplus_le_algebra.
    apply Rmult_neg_le_algebra with (r2:=amin);
      auto.
    apply Rmult_neg_ge_algebra with (r2:=(-4)%R);
      solve_linear.
    R_simplify; solve_linear.
  Qed.

Lemma sdist_incr : forall v1 v2,
    |-- 0 <= v1 <= v2 -->>
        sdist v1 <= sdist v2.
  Proof.
    clear d_gt_0.
    breakAbstraction; simpl; unfold eval_comp; simpl;
    intros. do 2 rewrite (Rmult_assoc _ (0 - / 2) (/ amin))%R.
    apply Rmult_le_compat; solve_linear.
    - apply Rmult_0_le; solve_linear.
    - assert (/ amin < 0)%R by solve_linear.
      solve_linear.
    - apply Rmult_le_compat; solve_linear.
  Qed.

  Arguments Stream.Cons {_} _ _.
  Lemma reason_action : forall P Q,
      (forall a b tr,
          eval_formula
            P
            (Stream.Cons a
                         (Stream.Cons b tr)) ->
          eval_formula
            Q (Stream.Cons a (Stream.Cons b tr))) ->
                (P |-- Q).
  Proof. red. red. red. intros. destruct tr.
         destruct tr. auto. Qed.
  Ltac reason_action_tac :=
    eapply reason_action; simpl;
    let pre := fresh "pre" in
    let post := fresh "post" in
    let tr := fresh "tr" in
    intros pre post tr;
      breakAbstraction; simpl; unfold eval_comp;
      simpl; intros.
  
(* A proof that the inductive safety condition
   Inv implies the safety contition
   we actually care about, Safe. *)
  Lemma inv_safe : IndInv //\\ TimeBound d |-- Safe.
  Proof.
    tlaAssert (0 <= tdiff <= d);
    [ solve_linear | tlaIntro ].
    breakAbstraction; simpl; unfold eval_comp; simpl; intros.
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    specialize (H5 (Stream.hd tr "T" - Stream.hd tr "t"))%R.
    destruct (Rle_dec R0 
                      (Stream.hd tr "V"+
                       Stream.hd tr "a"*
                       (Stream.hd tr "T" - Stream.hd tr "t"))%R);
      intuition.
    - eapply Rle_trans; eauto.
      rewrite <- Rplus_0_r with (r:=Stream.hd tr "y").
      apply Rplus_le_compat.
      + solve_linear.
      + rewrite Rmult_assoc.
        apply Rmult_0_le; solve_linear.
        apply pow_0_le.
        clear - amin_lt_0.
        assert (/ amin < 0)%R by solve_linear.
        solve_linear.
    - assert
        ((Stream.hd tr "V" +
          Stream.hd tr "a" *
          (Stream.hd tr "T" - Stream.hd tr "t") < 0)%R)
        by solve_linear.
      eapply Rle_trans; eauto.
      solve_linear.
  Qed.

  Theorem ctrl_safe :
    []"Vmax" >= "v" //\\ []"Ymax" >= "y" |-- Spec -->> []Safe.
  Proof.
    tlaIntro.
    eapply Sys_by_induction
    with (IndInv:=IndInv) (A:="Vmax" >= "v" //\\ "Ymax" >= "y").
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - solve_nonlinear.
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
                         solve_linear ]. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. }
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
          repeat charge_split.
          + tlaIntro; eapply unchanged_continuous;
            [ tlaAssume | 
            solve_linear; rewrite_next_st; solve_linear ].
          + charge_intros. solve_linear.
          + tlaIntro; eapply unchanged_continuous;
            [ tlaAssume | 
            solve_linear; rewrite_next_st; solve_linear ].
          + charge_intros. solve_linear. }
      { match goal with
          |- _ |-- ?GG => eapply diff_ind
                          with (Hyps:=TRUE)
                                 (G:=unnext GG)
        end; try solve [ tlaIntuition |
                         unfold World; tlaAssume |
                         solve_linear ]. }
      { eapply unchanged_continuous;
        [ unfold World; charge_assumption | ].
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
            tlaAssert (tdist "V"! "a"! x + (sdist ("V"! + "a"!*x)) <=
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
              tlaAssert (tdist "V"! "a"! x + (sdist ("V"! + "a"!*x)) <=
                         tdist "Vmax" "A" d + sdist ("Vmax" + "A" * d)).
              *  pose proof (tdist_sdist_incr "V"! "Vmax" "a"! "A" x d).
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
                  breakAbstraction. unfold eval_comp in *; simpl in *.
                  specialize (H19 (Stream.Cons pre (Stream.Cons post tr))).
                  intuition. simpl in *. eapply Rle_trans; eauto.
                  pose proof (sdist_incr "v" ("V" + "a"*tdiff)).
                  breakAbstraction. unfold eval_comp in *; simpl in *.
                  specialize (H19 (Stream.Cons pre (Stream.Cons post tr))).
                  intuition. simpl in *. apply H19; solve_nonlinear. }
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
                  breakAbstraction. unfold eval_comp in *; simpl in *.
                  specialize (H17 (Stream.Cons pre (Stream.Cons post tr))).
                  intuition. simpl in *. eapply Rle_trans; eauto.
                  pose proof (sdist_incr "v" ("V" + "a"*tdiff)).
                  breakAbstraction. unfold eval_comp in *; simpl in *.
                  specialize (H17 (Stream.Cons pre (Stream.Cons post tr))).
                  intuition. simpl in *. apply H17; solve_nonlinear. } }
            { tlaAssert ("y" <= ub).
              - rewrite <- inv_safe. charge_tauto.
              - reason_action_tac. intuition.
                repeat match goal with
                     | [ H : eq (post _) _ |- _ ]
                       => rewrite H in *; clear H
                     end.
                eapply Rle_trans; eauto. clear - H3 amin_lt_0 H2 H6.
                solve_nonlinear. } }
      { solve_linear. }
      { solve_linear. }
  Qed.


(* This was an idea for showing that the system
   is a refinement of another system that does not have
   a continuous evolution but instead replaces the continous
   evolution with the solution to the differential equations.
   This is specified by Evolve. However, I (Dan) couldn't figure out
   how to prove refinement. *)

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

End SecondDerivCtrl.

Close Scope HP_scope.
Close Scope string_scope.