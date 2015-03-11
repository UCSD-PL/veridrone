Require Import Coq.Reals.Rdefinitions.
Require Import TLA.TLA.
Require Import Examples.System.

Open Scope HP_scope.

Section SensorWithError.

  Variable x : Var.
  Variable Xmax : Var.
  Variable Xmin : Var.
  Variable err : R.

  Definition Sense : Formula :=
    Xmax! = Xmin! + err //\\ Xmin! <= x! <= Xmax!.

  Definition SenseSafe : Formula :=
    Xmin <= x <= Xmax.

  Definition Init : Formula := SenseSafe.

  Theorem sense_safe : forall w,
    |-- (Init //\\ [](World nil w //\\ Sense)) -->> []SenseSafe.
  Proof.
    intro. tlaIntro.
    eapply discr_indX.
    - tlaIntuition.
    - tlaAssume.
    - tlaAssume.
    - solve_linear.
  Qed.

End SensorWithError.

Close Scope HP_scope.