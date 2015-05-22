Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.BasicProofRules.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.

(* A library of useful TLA formulas, built
   from TLA primitives. *)

Open Scope HP_scope.
Open Scope string_scope.

(* Action formula expressing that all variables
   in xs are unchanged. *)
Fixpoint Unchanged (xs:list Var) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = x) //\\ (Unchanged xs)
  end.

Fixpoint UnchangedT (xs:list Term) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (next_term x = x) //\\ (UnchangedT xs)
  end.

(* Formula taking the maximum of two terms. *)
Definition Max (a b : Term)
           (c : Term -> Formula) : Formula :=
  (a >= b -->> (c a)) //\\ (a <= b -->> c b).

(* State formula expressing that the values of all
   variables in xs in the current state are equal
   to their value in st. *)
Fixpoint VarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x = st x) //\\ (VarsAgree xs st)
  end.

(* Action formula expressing that the values of all
   variables in xs in the next state are equal to
   their value in st. *)
Fixpoint AVarsAgree (xs:list Var) (st:state) : Formula :=
  match xs with
    | nil => TRUE
    | cons x xs =>
      (x! = st x) //\\ (AVarsAgree xs st)
  end.

(* A type representing a differential equation.
   (DiffEqC x t) represents (x' = t).
   We now have a more general type for
   differential equations, but we use this and
   a coercion to maintain compatibility. *)
(*
Inductive DiffEq :=
| DiffEqC : Var -> Term -> DiffEq.

Definition get_var (d:DiffEq) :=
  match d with
    | DiffEqC x _ => x
  end.

(* Gets the term of the differential equation. *)
Definition get_term (d:DiffEq) :=
  match d with
    | DiffEqC _ t => t
  end.
*)

(* Our shallow encoding of continuous evolutions. *)
Definition Evolution := state->Formula.

(* Expresses the property that a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
Definition solves_diffeqs (f : R -> state)
           (cp : Evolution) (r : R)
           (is_derivable : forall x, derivable (fun t => f t x)) :=
    forall z, (R0 <= z <= r)%R ->
              eval_formula (cp (fun x => derive (fun t => f t x) (is_derivable x) z))
                           (Stream.forever (f z)).

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (f : R -> state)
           (cp:Evolution) (r : R) :=
  exists is_derivable,
    (* f is a solution to diffeqs *)
    solves_diffeqs f cp r is_derivable.

(* Action formula expressing that a transition
   is consistent with the system of differential
   equations represented by cp. *)
Definition Continuous (cp:Evolution) : Formula :=
  Exists r : R,
  Exists f : R -> state,
         (r > 0)
    //\\ (PropF (is_solution f cp r))
    //\\ (Embed (fun st st' => f R0 = st /\ f r = st')).

(* Some notation *)
(* In a module to avoid conflicts. *)
(*
Module LibNotations.
Notation "x ' ::= t" := (DiffEqC x t) (at level 60) : HP_scope.
Notation "[ x1 , .. , xn ]" := (cons x1 .. (cons xn nil) .. )
    (at level 60) : HP_scope.
End LibNotations.
*)

Close Scope string_scope.
Close Scope HP_scope.
