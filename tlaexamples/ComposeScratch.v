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
         ((dx "A")*d + (dx "Vmax") <= ub //\\ (dx "a") ! = (dx "A"))
    \\// ((dx "a")! <= 0).

  Definition Ctrl : Formula := Ctrl_ dx //\\ Ctrl_ dy.

  Definition I_ dx : Formula :=
    dx "v" <= ub //\\ dx "v" + dx "a"*d <= ub //\\
    0 <= dx "t" <= d //\\ dx "Vmax" >= dx "v".

  Definition I : Formula :=
    I_ dx //\\ I_ dy.

  Definition Safe : Formula :=
    dx "v" <= ub //\\ dy "v" <= ub.

  Definition Realizable : Formula :=
    Exists a : R,
               Exists theta : R,
                              dx "a" = a * CosT theta //\\
                              dy "a" = a * SinT theta.

  Definition IndInv_ dx : Formula :=
    Max (dx "a") 0 (fun t => t*"t" + dx "v" <= ub).

  Definition IndInv : Formula := IndInv_ dx //\\ IndInv_ dy.

  Variable WC : Formula.

  Definition SpecR : SysRec :=
    {| dvars := (dx "a"::dy "a"::nil)%list;
       cvars := (dx "v"::dy "v"::nil)%list;
       Init := I;
       Prog := Ctrl;
       world := w;
       WConstraint := WC;
       maxTime := d |}.

  Definition Spec := SysD SpecR.

  Definition Env_ dx : Formula :=
    dx "Vmax" >= dx "v".

  Definition Env : Formula := Env_ dx //\\ Env_ dy.

  Theorem ctrl_safe :
    []Env |-- Spec -->> [](Safe //\\ Realizable).
  Proof.
    tlaIntro.
    eapply Sys_by_induction
    with (IndInv:=IndInv) (A:=Env).
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