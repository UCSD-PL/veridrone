Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.

Open Scope HP_scope.
Open Scope string_scope.

Fixpoint Unchanged (xs:list Var) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = x) /\ (Unchanged xs)
  end.

Fixpoint VarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x = st x) /\ (VarsAgree xs st)
  end.

Fixpoint AVarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = st x) /\ (AVarsAgree xs st)
  end.

Inductive DiffEq :=
| DiffEqC : Var -> Term -> DiffEq.

Definition get_var (d:DiffEq) :=
  match d with
    | DiffEqC x _ => x
  end.

Definition get_term (d:DiffEq) :=
  match d with
    | DiffEqC _ t => t
  end.

(* Expresses the property that a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
Definition solves_diffeqs (f : R -> state)
           (diffeqs : list DiffEq) (r : R)
           (is_derivable : forall x, derivable (fun t => f t x)) :=
  forall x d,
    List.In (DiffEqC x d) diffeqs ->
    forall z, (R0 <= z <= r)%R ->
              derive (fun t => f t x) (is_derivable x) z =
              eval_term d (f z).

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (f : R -> state)
           (diffeqs : list DiffEq) (r : R) :=
  exists is_derivable,
    (* f is a solution to diffeqs *)
    solves_diffeqs f diffeqs r is_derivable.

Definition time := nonnegreal.

Definition TimeC (t:time) : Term :=
  RealT t.
Coercion TimeC : time >-> Term.

Definition Continuous (cp:list DiffEq) (b:Term) (t:Var) : Formula :=
  let xs := List.map get_var cp in
  Exists R
         (fun r =>
            Exists (R -> state)
                   (fun f =>
                         (r > 0)
                      /\ (PropF (is_solution f cp r))
                      /\ (VarsAgree xs (f R0))
                      /\ (AVarsAgree xs (f r))
                      /\ (t + r <= b)
                      (*/\ (t! = t + r)*))).

Close Scope string_scope.
Close Scope HP_scope.

Notation "x ' ::= t" := (DiffEqC x t) (at level 60) : HP_scope.
Notation "[ x1 , .. , xn ]" := (cons x1 .. (cons xn nil) .. )
    (at level 60) : HP_scope.
