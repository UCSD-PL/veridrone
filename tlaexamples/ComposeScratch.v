Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
Require Import Examples.System.

Open Scope HP_scope.
Open Scope string_scope.

Section VelCtrl.

  (* Upper bound on velocity. *)
  Variable ub : R.
  (* Max time between executions of the
     controller. *)
  Variable d : R.
  Hypothesis d_gt_0 : (d > 0)%R.
  Variable err : R.

  Inductive dimension := X | Y.
  Definition dim (d : dimension) (s : Var) : Var :=
    (String.append s match d with
                     | X => "_x"
                     | Y => "_y"
                     end).

  (* The continuous dynamics of the system *)
  Definition w : list DiffEq :=
    [(dim X "v")' ::= (dim X "a")
    ,(dim Y "v")' ::= (dim Y "a")].

  Definition dx := dim X.
  Definition dy := dim Y.

  Definition Ctrl_ (dx : Var -> Var)  : Formula :=
    Max (dx "a")! 0 (fun t => t*"d" + dx "v" <= ub).

(* This is not general enough. It doesn't allow enough choices for
   realization. *)
(*
         ((dx "A")*d + (dx "Vmax") <= ub //\\ (dx "a") ! = (dx "A"))
    \\// ((dx "a")! <= 0).
*)

  Definition Realize : Formula :=
    (dx "a")! = "a"!*CosT "theta"! //\\
    (dy "a")! = "a"!*SinT "theta"!.

  Definition Ctrl : Formula :=
    Ctrl_ dx //\\ Ctrl_ dy.

  Definition IndInv_ dx : Formula :=
    Max (dx "a") 0 (fun t => t*"t" + dx "v" <= ub).

  Definition IndInv : Formula := IndInv_ dx //\\ IndInv_ dy.

Require Import TLA.Substitution.

  Lemma enabled_exists : forall A x,
    Exists c : R, Enabled (A[c /! x])%HP -|- Enabled A.
  Admitted.

  Ltac exists_en y t :=
    rewrite <- enabled_exists with (x:=y);
    apply lexistsR with (x:=t).

  Ltac enabled_to_exists :=
    match goal with
    | [ |- context[Enabled ?A] ] =>
      match A with
      | context[VarNextT ?x] =>
        exists_en x
      end
    end.

  Lemma enabled_st_formula : forall P,
    BasicProofRules.is_st_formula P ->
    P -|- Enabled P.
  Admitted.

  Lemma enabled :
    IndInv //\\ TimeBound d |-- Enabled (Ctrl //\\ Realize).
  Proof.
    unfold Ctrl, Ctrl_, Max, Realize, IndInv, IndInv_, dx, dy, dim.
    simpl. restoreAbstraction.
    exists_en "a" R0.
    exists_en (dx "a") R0.
    exists_en (dy "a") R0.
    exists_en "theta" R0.
    rewrite <- enabled_st_formula; [ | tlaIntuition ].
    solve_linear.
    z3_quick.
    z3_quick says this is not true. *)
    solve_nonlinear.
  Qed.
    

  Definition I_ dx : Formula :=
    dx "v" <= ub //\\ dx "v" + dx "a"*d <= ub //\\
    0 <= dx "t" <= d //\\ dx "Vmax" >= dx "v".

  Definition I : Formula :=
    I_ dx //\\ I_ dy.

  Variable WC : Formula.

  Definition SpecR : SysRec :=
    {| dvars := (dx "a"::dy "a"::nil)%list;
       cvars := (dx "v"::dy "v"::nil)%list;
       Init := I;
       Prog := Ctrl //\\ Realize;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Theorem spec_safe :
    |-- SysSafe SpecR.
  Proof.
    unfold SysSafe. charge_intros.
    


  Definition Safe : Formula :=
    dx "v" <= ub //\\ dy "v" <= ub.

  Definition Realizable : Formula :=
    Exists a : R,
               Exists theta : R,
                              dx "a" = a * CosT theta //\\
                              dy "a" = a * SinT theta.

  Definition Env_ dx : Formula :=
    dx "Vmax" >= dx "v".

  Theorem ctrl_safe :
    [](Env //\\ Safe) |-- Spec -->> []Realizable.
  Proof.
    tlaIntro.
    eapply Sys_by_induction
    with (IndInv:=IndInv) (A:=Env //\\ Safe).
    3:unfold Spec, SpecR; tlaAssume.
    - (*SysSafe*) admit.
    - tlaIntuition.
    - solve_nonlinear.
    - charge_tauto.
    - solve_nonlinear.
    - unfold InvariantUnder. solve_linear.
      rewrite_next_st. solve_linear.
    - eapply diff_ind with (Hyps:=TRUE).
      + tlaIntuition.
      + tlaIntuition.
      + unfold World. tlaAssume.
      + tlaIntuition.
      + tlaAssume.
      + tlaIntuition.
      + repeat tlaSplit;
        try solve [solve_linear |
                   tlaIntro; eapply unchanged_continuous;
                     [ tlaAssume | solve_linear ] ].
    - solve_nonlinear.
  Qed.

End VelCtrl.

Close Scope HP_scope.
Close Scope string_scope.