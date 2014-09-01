Require Import String.
Require Import List.
Require Import Coq.Reals.Rdefinitions.

(************************************************)
(* The syntax of differential dynamic logic.    *)
(************************************************)
Definition Var := string.
(* All variables are real-valued. *)
Definition state := Var -> R.

(* Real-valued terms built using variables, constants
   and arithmetic. *)
Inductive Term :=
| VarT : Var -> Term
| RealT : R -> Term
| PlusT : Term -> Term -> Term
| MinusT : Term -> Term -> Term
| MultT : Term -> Term -> Term.

Class Evaluable (T : Set) : Type :=
{ evaluate : T -> state -> Prop }.

(* Atoms of formulas. *)
(*Inductive Atom :=
| Gt : Term -> Term -> Atom
| Eq : Term -> Term -> Atom.*)

(* Conditionals *)
Inductive Cond :=
| GtC : Term -> Term -> Cond
| EqC : Term -> Term -> Cond
| AndC : Cond -> Cond -> Cond
| OrC : Cond -> Cond -> Cond.

(* Programs containing discrete and continuous parts. *)
Inductive HybridProg :=
(* No-op *)
| Skip : HybridProg
(* A discrete progam constructor for assignment *)
| Assign : Var -> Term -> HybridProg
(* A continuous program constructor that takes a list
   of differential equations and a time bound. Each
   differential equation is a pair of a variable and
   a real valued term. For example, if variables are
   strings, then the system of differential equations

    x' = 4
    y' = x

   would be represented as

    DiffEq [ ("x", RealT 4); ("y", VarT "x") ]

   The time bound specifies the maximum time for which
   the system evolves according to the differential
   equations.
 *)
| DiffEq : list (Var * Term) -> R -> HybridProg
(* Sequencing programs *)
| Seq : HybridProg -> HybridProg -> HybridProg
(* If-then-else *)
| Branch : Cond -> HybridProg -> HybridProg -> HybridProg
(* While loop *)
| While : Cond -> HybridProg -> HybridProg.

(* Formulas expressing correctness properties of hybrid
   programs. *)
Inductive Formula :=
| GtF : Term -> Term -> Formula
| EqF : Term -> Term -> Formula
| AndF : Formula -> Formula -> Formula
| OrF : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula
| ForallState : HybridProg -> Formula -> Formula.

(************************************************)
(* Some notation for the logic.                 *)
(************************************************)
(*Term notation *)
Notation " ` a " := (VarT a) (at level 10) : HP_scope.
Notation "0" := (RealT 0) (at level 10) : HP_scope.
Notation "1" := (RealT 1) (at level 10) : HP_scope.
Notation "2" := (RealT 2) (at level 10) : HP_scope.
Notation "3" := (RealT 3) (at level 10) : HP_scope.
Notation "4" := (RealT 4) (at level 10) : HP_scope.
Notation "5" := (RealT 5) (at level 10) : HP_scope.
Notation "6" := (RealT 6) (at level 10) : HP_scope.
Infix "+" := (PlusT) : HP_scope.
Infix "-" := (MinusT) : HP_scope.
Notation "-- x" := (MinusT (RealT R0) x)
                     (at level 9) : HP_scope.
Infix "*" := (MultT) : HP_scope.
Fixpoint pow (t : Term) (n : nat) :=
  match n with
  | O => RealT 1
  | S n => MultT t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : HP_scope.

(* This type class allows us to define a single notation
   for comparison operators and logical connectives in
   the context of a formula and conditionals. *)
Class LogicEq (T : Type) : Type :=
{ Gt : Term -> Term -> T;
  Eq : Term -> Term -> T;
  And : T -> T -> T;
  Or : T -> T -> T }.

Infix ">" := (Gt) : HP_scope.
Infix "=" := (Eq) : HP_scope.
Definition Gte {T I} x y :=
  @Or T I (@Gt T I x y) (@Eq T I x y).
Infix ">=" := (Gte) : HP_scope.
Definition Lte {T I} x y := @Gte T I y x.
Infix "<=" := (Lte) : HP_scope.
Definition Lt {T I} x y := @Gt T I y x.
Infix "<" := (Lt) : HP_scope.
Infix "/\" := (And) : HP_scope.
Infix "\/" := (Or) : HP_scope.

Instance FormulaLogicEq : LogicEq Formula :=
{ Gt := GtF;
  Eq := EqF;
  And := AndF;
  Or := OrF }.

Instance CondLogicEq : LogicEq Cond :=
{ Gt := GtC;
  Eq := EqC;
  And := AndC;
  Or := OrC }.

(* HybridProg notation *)
Notation "x ::= t" := (Assign x t)
                        (at level 10) : HP_scope.
Notation "x ' ::= t" := (x, t) (at level 10) : HP_scope.
Notation "| x1 , .. , xn |" := (cons x1 .. (cons xn nil) .. )
    (at level 10) : HP_scope.
Notation "[ diffeqs & b ]" :=
  (DiffEq diffeqs b)
    (at level 10) : HP_scope.
Notation "p1 ; p2" := (Seq p1 p2)
                        (at level 11) : HP_scope.
Notation "'IF' c 'THEN' p1 'ELSE' p2" :=
  (Branch c p1 p2) (at level 11) : HP_scope.
Notation "'WHILE' c p" :=
  (While c p) (at level 11) : HP_scope.

(* Formula notation *)
Notation "f1 --> f2" := (Imp f1 f2)
                          (at level 11) : HP_scope.
Notation "[ p ] f" := (ForallState p f)
                        (at level 10) : HP_scope.

Delimit Scope HP_scope with HP.
