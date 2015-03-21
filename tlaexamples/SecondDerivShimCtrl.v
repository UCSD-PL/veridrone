Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Import LibNotations.
Require Import TLA.DifferentialInduction.
Require Import TLA.ContinuousProofRules.
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
  Definition world : list DiffEq :=
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
         (Max "A" 0 (fun mx => "Hmax" + tdist "Vmax" mx d +
                               sdist ("Vmax" + mx*d)
          <= ub) //\\ "a"! = "A")
    \\// ("a"! = amin).

  Definition Safe : Formula :=
    "y" <= ub.

  Definition IndInv : Formula :=
    ("Vmax" <= 0 -->> "y" <= ub) //\\
    Max "a" 0 (fun mx => "Ymax" + tdist "Vmax" mx "t" +
                         sdist ("Vmax" + mx*"t")
                         <= ub).

  Definition Init : Formula := IndInv.

  Theorem ctrl_safe : forall WC,
    []"Vmax" >= "v" //\\ []"Ymax" >= "y"
    |-- Sys ("a"::"Vmax"::"Ymax"::nil)%list ("v"::"y"::nil)%list
            Init Ctrl world WC d -->> []Safe.
  Proof.
    intro. tlaIntro.
    eapply sys_by_induction
    with (IndInv:=IndInv) (A:="Vmax" >= "v" //\\ "Ymax" >= "y").
    - tlaIntuition.
    - tlaAssume.
    - solve_nonlinear.
    - tlaIntuition.
    - unfold IndInv, Max. unfold Safe. unfold tdist, sdist.
      tlaAssert (("a" <= 0 \\// "a" >= 0) //\\
                 ("Vmax" <= 0 \\// "Vmax" >= 0)).
      + apply forget_prem. solve_linear.
      + breakAbstraction; intros; unfold eval_comp in *;
        simpl in *; intuition.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Psatz.
Require Import ArithFacts.
apply Rmult_le_compat_neg_r with (r:=amin) in H3;
  try solve_linear.
apply Rmult_le_compat_pos_r with (r:=2%R) in H3;
  try solve_linear.
R_simplify; solve_linear. clear H5.
solve_nonlinear.

apply Rmult_le_compat_neg_r with (r:=amin) in H3;
  try solve_linear.
apply Rmult_le_compat_pos_r with (r:=2%R) in H3;
  try solve_linear.
R_simplify; solve_linear. clear H8.
Time solve_nonlinear.
    - unfold InvariantUnder, IndInv, Max. simpl.
      restoreAbstraction. unfold tdist, sdist.
      solve_linear; rewrite_next_st; tauto.
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
        simpl. restoreAbstraction.
    - solve_nonlinear.
  Qed.

End VelCtrl.

Close Scope HP_scope.
Close Scope string_scope.