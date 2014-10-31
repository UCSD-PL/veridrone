Require Import String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

(************************************************)
(* The syntax of differential dynamic logic.    *)
(************************************************)
Definition Var := string.

Inductive VarOrNext :=
| VarNow : Var -> VarOrNext
| VarNext : Var -> VarOrNext.

(* Real-valued terms built using variables, constants
   and arithmetic. *)
Inductive Term V :=
| VarT : V -> Term V
| NatT : nat -> Term V
| RealT : R -> Term V
| PlusT : Term V -> Term V -> Term V
| MinusT : Term V -> Term V -> Term V
| MultT : Term V -> Term V -> Term V.

Definition TermNow := Term Var.
Definition TermNext := Term VarOrNext.

(* Terms taking on the value of the next state. *)
(*Inductive ActionTerm :=
| TermNow : Term -> ActionTerm
| TermNext : Term -> ActionTerm.*)

Inductive CompOp :=
| Gt : CompOp
| Ge : CompOp
| Lt : CompOp
| Le : CompOp
| Eq : CompOp.

Inductive Formula :=
| TRUE : Formula
| FALSE : Formula
(*| Comp : ActionTerm -> ActionTerm -> CompOp -> Formula*)
| Comp : TermNext -> TermNext -> CompOp -> Formula
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
(*Definition NatC (n:nat) : R :=
  INR n.
Coercion NatC : nat >-> R.*)
Definition NatC (n:nat) : TermNow :=
  NatT _ n.
Coercion NatC : nat >-> TermNow.
Definition NatNextC (n:nat) : TermNext :=
  NatT _ n.
Coercion NatNextC : nat >-> TermNext.
Definition ConstC (c:R) : TermNow :=
  RealT _ c.
Coercion ConstC : R >-> TermNow.
Definition ConstNextC (c:R) : TermNext :=
  RealT _ c.
Coercion ConstNextC : R >-> TermNext.
Definition StringC (s:string) : Var :=
  s.
Coercion StringC : string >-> Var.
Definition VarC (x:Var) : TermNow :=
  VarT _ x.
Coercion VarC : Var >-> TermNow.
Definition VarNextC (x:Var) : TermNext :=
  VarT _ (VarNow x).
Coercion VarNextC : Var >-> TermNext.
(*Definition TermC (t:Term) : ActionTerm :=
  TermNow t.
Coercion TermC : Term >-> ActionTerm.*)
(*Notation "x !" := (TermNext x) (at level 0) : HP_scope.*)
Notation "x !" :=
  (VarT VarOrNext (VarNext x)) (at level 0) : HP_scope.
Infix "+" := (PlusT _) : HP_scope.
Infix "-" := (MinusT _) : HP_scope.
Notation "-- x" := (MinusT _ (RealT _ R0) x)
                     (at level 0) : HP_scope.
Infix "*" := (MultT _) : HP_scope.
Fixpoint pow {V} (t : Term V) (n : nat) :=
  match n with
  | O => RealT _ 1
  | S n => MultT _ t (pow t n)
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