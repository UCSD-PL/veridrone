Require Import String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

(************************************************)
(* The syntax of differential dynamic logic.    *)
(************************************************)
Definition Var := string.

(* Real-valued terms built using variables, constants
   and arithmetic. *)
Inductive Term :=
| VarT : Var -> Term
| RealT : R -> Term
| PlusT : Term -> Term -> Term
| MinusT : Term -> Term -> Term
| MultT : Term -> Term -> Term.

(* Terms taking on the value of the next state. *)
Inductive ActionTerm :=
| TermNow : Term -> ActionTerm
| TermNext : Term -> ActionTerm.

Inductive CompOp :=
| Gt : CompOp
| Ge : CompOp
| Lt : CompOp
| Le : CompOp
| Eq : CompOp.

Inductive Formula :=
| TRUE : Formula
| FALSE : Formula
| Comp : ActionTerm -> ActionTerm -> CompOp -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula
| PropF : Prop -> Formula
| Exists : forall T, (T -> Formula) -> Formula
| Always : Formula -> Formula
| Eventually : Formula -> Formula.

(************************************************)
(* Some notation for the logic.                 *)
(************************************************)
Delimit Scope HP_scope with HP.

(*Term notation *)
Definition NatC (n:nat) : R :=
  INR n.
Coercion NatC : nat >-> R.
Definition ConstC (c:R) : Term :=
  RealT c.
Coercion ConstC : R >-> Term.
Definition VarC (x:string) : Term :=
  VarT x.
Coercion VarC : string >-> Term.
Definition TermC (t:Term) : ActionTerm :=
  TermNow t.
Coercion TermC : Term >-> ActionTerm.
Notation "x !" := (TermNext x) (at level 0) : HP_scope.
Infix "+" := (PlusT) : HP_scope.
Infix "-" := (MinusT) : HP_scope.
Notation "-- x" := (MinusT (RealT R0) x)
                     (at level 0) : HP_scope.
Infix "*" := (MultT) : HP_scope.
Fixpoint pow (t : Term) (n : nat) :=
  match n with
  | O => RealT 1
  | S n => MultT t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : HP_scope.

(* Comparisons *)
Notation "t1 > t2" := (Comp t1 t2 Gt) : HP_scope.
Notation "t1 >= t2" := (Comp t1 t2 Ge) : HP_scope.
Notation "t1 < t2" := (Comp t1 t2 Lt) : HP_scope.
Notation "t1 <= t2" := (Comp t1 t2 Le) : HP_scope.
Notation "t1 = t2" := (Comp t1 t2 Eq) : HP_scope.
Notation "x <= y <= z" :=
  (And (Comp x y Le) (Comp y z Le)) : HP_scope.

(* Propositional Logic *)
Infix "/\" := (And) : HP_scope.
Infix "\/" := (Or) : HP_scope.
Notation "f1 --> f2" := (Imp f1 f2)
                          (at level 97) : HP_scope.

(* Formula notation *)
(*Notation "'Exists' x .. y , p" :=
  (Exists (fun x => .. (Exists (fun y => p)) ..))
    (at level 100, x binder, y binder) : HP_scope.*)

Notation "[] f" := (Always f)
                     (at level 95) : HP_scope.
Notation "<> f" := (Eventually f)
                     (at level 95) : HP_scope.