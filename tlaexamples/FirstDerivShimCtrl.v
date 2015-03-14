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

  (* The continuous dynamics of the system *)
  Definition world : list DiffEq :=
    ["v"' ::= "a"].

  Definition Ctrl : Formula :=
       ("A"*d + "Vmax" <= ub //\\ "a"! = "A")
    \\// ("a"! <= 0).

  Definition Init : Formula :=
    "v" <= ub //\\ "v" + "a"*d <= ub //\\
    0 <= "t" <= d //\\ "Vmax" >= "v".

  Definition Safe : Formula :=
    "v" <= ub.

  Definition IndInv : Formula :=
       ("a" <  0 -->> Safe)
    //\\ ("a" >= 0 -->> "a"*"t" + "v" <= ub).

  Theorem ctrl_safe : forall WC,
    []"Vmax" >= "v"
    |-- Sys ("a"::nil) ("v"::nil)
            Init Ctrl world WC d -->> []"v" <= ub.
  Proof.
    intro. tlaIntro.
    eapply Sys_by_induction with (IndInv:=IndInv) (A:="Vmax" >= "v").
    - tlaIntuition.
    - tlaAssume.
    - solve_nonlinear.
    - tlaIntuition.
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
                   eapply unchanged_continuous;
                     [ tlaIntro; tlaAssume | solve_linear ] ].
    - solve_nonlinear.
  Qed.

End VelCtrl.

Close Scope HP_scope.
Close Scope string_scope.