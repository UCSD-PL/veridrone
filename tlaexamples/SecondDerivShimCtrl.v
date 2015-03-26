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

  Definition Safe : Formula :=
    "y" <= ub.

  Definition IndInv : Formula :=
    Syntax.Forall R (fun t =>
                0 <= t <= d -->>
                "y" + tdist "v" "a" t +
                          sdist ("v" + "a"*t) <= ub).
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
    {| dvars := ("a"::"Vmax"::"Ymax"::nil)%list;
       cvars := ("v"::"y"::nil)%list;
       Init := I;
       Prog := Ctrl;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

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
    - (* IndInv -> Safe *)
      admit.
(*      unfold IndInv, Max. unfold Safe. unfold tdist, sdist.
      tlaAssert (("a" <= 0 \\// "a" >= 0) //\\
                 ("Vmax" <= 0 \\// "Vmax" >= 0)).
      + apply forget_prem. solve_linear.
      + breakAbstraction; intros; unfold eval_comp in *;
        simpl in *. destruct H as [? [? ?] ].
        specialize (H1 R0). assert (0 <= 0 <= d)%R by solve_linear.
        specialize (H1 H3). revert H1. rewrite_real_zeros. intro.
        eapply Rle_trans; eauto. rewrite <- Rplus_0_r with (r:=Stream.hd tr "y").
        apply Rplus_le_compat; [solve_linear | ]. apply Rge_le.
        apply Rmult_neg_ge_algebra with (r2:=(-2)%R); [ solve_linear | ].
        apply Rmult_neg_le_algebra with (r2:=amin%R); [ solve_linear | ].
        R_simplify; try solve [solve_linear]. simpl. solve_nonlinear.
(*        * apply Rmult_le_compat_neg_r with (r:=amin) in H3;
          try solve_linear.
          apply Rmult_le_compat_pos_r with (r:=2%R) in H3;
            try solve_linear.
          R_simplify; solve_linear. clear H5.
          solve_nonlinear.
        * apply Rmult_le_compat_neg_r with (r:=amin) in H3;
          try solve_linear.
          apply Rmult_le_compat_pos_r with (r:=2%R) in H3;
            try solve_linear.
          R_simplify; solve_linear.
          clear - amin_lt_0 H0 H4 H6 H H1 H7 H3.
          (* Took 200 seconds originally *)
          solve_nonlinear.*)
*)
    - unfold InvariantUnder, IndInv, Max. simpl.
      restoreAbstraction. unfold tdist, sdist.
      solve_linear; rewrite_next_st; intuition.
    - simpl BasicProofRules.next. restoreAbstraction.
      apply lforallR. intro.
      match goal with
      |- _ |-- ?GG => eapply diff_ind with (Hyps:=TRUE) (G:=unnext GG)
      end.
      + tlaIntuition.
      + tlaIntuition.
      + unfold World. tlaAssume.
      + tlaIntuition.
      + unfold IndInv. simpl unnext. restoreAbstraction.
        solve_linear.
      + tlaIntuition.
      + repeat tlaSplit;
        try solve [solve_linear |
                   tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ].
        simpl unnext_term. simpl deriv_term.
        fold unnext. simpl. restoreAbstraction.
        breakAbstraction; unfold eval_comp; simpl.
        intros. rewrite_real_zeros. rewrite Rminus_0_r.
        rewrite_real_zeros. rewrite Rminus_0_l. repeat  rewrite Rmult_1_r.
        simpl unnext.
        simpl unnext.
    - tlaAssert ("A" <= 0 \\// "A" >= 0); [ solve_linear | ].
      simpl BasicProofRules.next. restoreAbstraction.
      unfold Discr, IndInv, Ctrl.
      
      breakAbstraction. unfold eval_comp. simpl.
      intros. intuition.

      R_simplify. simpl in *.
  Qed.

End VelCtrl.

Close Scope HP_scope.
Close Scope string_scope.