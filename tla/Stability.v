Require Import TLA.TLA.
Require Import TLA.DifferentialInduction.
Require Import Coq.Reals.Rdefinitions.

Open Scope HP_scope.

Notation "x <> y" := (Imp (Comp x y Eq) FALSE) : HP_scope.

Definition Abs (x : Term) : Term :=
  MAX(x,--x).

Lemma lyapunov_fun_stability :
  forall (x:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula),
    deriv_term V = Some V' ->
    G |-- [](Continuous cp \\// x! = x) ->
      |-- Forall st, cp st -->> x <> 0 -->> V' st < 0 ->
      |-- Forall st, cp st -->> x = 0 -->> V' st = 0 ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- Forall a : R, a > 0 -->>
          Exists b : R, b > 0 //\\
            (Abs x < b -->> []Abs x < a).
Admitted.

Lemma lyapunov_fun_asymptotic_stability :
  forall (x:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula),
    deriv_term V = Some V' ->
    G |-- [](Continuous cp \\// x! = x) ->
      |-- Forall st, cp st -->> x <> 0 -->> V' st < 0 ->
      |-- Forall st, cp st -->> x = 0 -->> V' st = 0 ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- Forall e : R, <>[]Abs x < e.
Admitted.

Lemma lyapunov_fun_exponential_stability :
  forall (x t:Var) (V:Term) (V':state->Term)
         (cp : Evolution) (G:Formula),
    deriv_term V = Some V' ->
    (forall st', |-- cp st' -->> st' t = 1) ->
    G |-- [](Continuous cp \\// x! = x) ->
      |-- Forall st, cp st -->> x <> 0 -->> V' st < 0 ->
      |-- Forall st, cp st -->> x = 0 -->> V' st = 0 ->
      |-- x <> 0 -->> V > 0 ->
      |-- x = 0 -->> V = 0 ->
    G |-- Exists x0 : R, x = x0 //\\
          Exists a : R, a > 0 //\\
          Exists b : R, b > 0 //\\
            []Abs x <= a * Abs x0 * exp(--b * t).
Admitted.