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
    "Y"! = "Ymax" //\\ "V"! = "Vmax" //\\ "T"! = "t"!.

  Definition Safe : Formula :=
    "y" <= ub.

  Definition tdiff : Term :=
    "T" - "t".

  Definition IndInv : Formula :=
    "y" - "Y" <= tdist "V" "a" tdiff //\\
    "v" - "V" <= "a"*tdiff //\\
    Syntax.Forall R
           (fun t =>
              ((0 <= t <= d //\\ 0 <= "V" + "a"*t) -->>
                    "Y" + (tdist "V" "a" t) +
                    (sdist ("V" + "a"*t)) <= ub) //\\
              ((0 <= t <= d //\\ "V" + "a"*t < 0) -->>
                     "Y" + (tdist "V" "a" t) <= ub)).

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
      solve_linear; rewrite_next_st; solve_linear;
      specialize (H4 x); solve_linear.
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
          specialize (H6 x); solve_linear.
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
    - repeat charge_split.
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { solve_linear; rewrite_next_st; R_simplify; solve_linear. }
      { fold BasicProofRules.next. unfold Discr, Ctrl, Max.
        tlaAssert ("A" <= 0 \\// "A" >= 0);
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
        - fold BasicProofRules.next.
          (* STOPPED HERE *)
            apply Rplus_le_compat_l. solve_linear. apply H0.

            solve_nonlinear.
(*            repeat rewrite <- curry in H.
            apply lrevert in H.*)
            breakAbstraction; unfold eval_comp; simpl; intros.
            solve_linear. apply (H tr). specialize (H tr).
            solve_linear.
            rewrite <- H.
            rewrite lrevert in H.
        apply limplAdj_true in H.
        | apply limplAdj ].
            Locate tlaIntros. rewrite curry in H. charge_apply H.

solve_linear.
      + rewrite_next_st. R_simplify. solve_linear.
      + rewrite_next_st. R_simplify. solve_linear.
      + rewrite_next_st. R_simplify; [ | solve_linear].
(* STOPPED HERE *)

tlaAssert ("A" <= 0 \\// "A" >= 0); [ solve_linear | ].
      simpl BasicProofRules.next. restoreAbstraction.
      unfold Discr, IndInv, Ctrl.
      
      breakAbstraction. unfold eval_comp. simpl.
      intros. intuition.

      R_simplify. simpl in *.
  Qed.

(*
  Definition IndInv : Formula :=
         "y" = "Y" + tdist "V" "a" ("T" - "t") 
    //\\ "v" = "V" + "a"*("T" - "t").
*)

  Theorem world_solution :
    |-- Spec -->> []IndInv.
  Proof.
    tlaIntro.
    eapply Sys_by_induction
    with (IndInv:=IndInv) (A:=TRUE).
    - tlaIntuition.
    - unfold Spec, SpecR. tlaAssume.
    - charge_assumption.
    - tlaIntuition.
    - charge_tauto.
    - unfold InvariantUnder, IndInv, Max. simpl.
      restoreAbstraction. solve_linear;
      solve_linear; rewrite_next_st; intuition.
    - eapply diff_ind with (Hyps:="v" = "V" + "a"*("T"-"t")).
      + tlaIntuition.
      + tlaIntuition.
      + unfold World. tlaAssume.
      + eapply diff_ind with (Hyps:=TRUE).
        * tlaIntuition.
        * tlaIntuition.
        * tlaAssume.
        * charge_tauto.
        * charge_tauto.
        * tlaIntuition.
        * solve_linear.
      + charge_tauto.
      + charge_tauto.
      + repeat tlaSplit;
        try solve [solve_linear |
                   tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ].
    - solve_linear; rewrite_next_st; solve_linear.
  Qed.

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
        

End VelCtrl.

Close Scope HP_scope.
Close Scope string_scope.