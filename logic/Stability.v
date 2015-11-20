Require Import Logic.Logic.
Require Import Coq.Reals.Rdefinitions.
Require Import Rbasic_fun.

Open Scope HP_scope.

Definition Abs (x : Term) : Term :=
  MAX(x,--x).

Definition LyapunovStable (x : Var) : Formula :=
  Forall a : R, a > 0 -->>
  Exists b : R, b > 0 //\\
    (Abs x < b -->> []Abs x < a).

Definition AsymptoticallyStable (x : Var) : Formula :=
  Forall e : R, <>[]Abs x < e.

Definition ExponentiallyStable (a : R) (x t : Var) : Formula :=
  Exists x0 : R, x = x0 //\\
  Exists M : R, M > 0 //\\
    []Abs x <= M * Abs x0 * exp(--(a/2) * t).

Close Scope HP_scope.
