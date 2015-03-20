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
    Xmax! <= Xmin! + err //\\ Xmin! <= x! <= Xmax!.

  Definition SenseSafe : Formula :=
    Xmin <= x <= Xmax.

  Definition Init : Formula := SenseSafe.

  Variable w : list DiffEq.
  Variable d : R.

  Theorem sense_safe :
    Sys nil (x::Xmax::Xmin::nil)%list Init ltrue w Sense d |-- []SenseSafe.
  Proof.
    eapply Sys_by_induction with (IndInv := SenseSafe) (A := ltrue).
    + tlaIntuition.
    + tlaAssume.
    + tlaAssume.
    + eapply BasicProofRules.always_tauto. charge_tauto.
    + tlaAssume.
    + red. solve_linear.
    + solve_linear.
    + solve_linear.
  Qed.

End SensorWithError.

Close Scope HP_scope.