Require Import Z3.Tactic.

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Section test.

  Variable A B C D G Y Z: Prop.
  Variable d:R.
  Variable p:R.
  Hypothesis H2 : (d+p=R0)%R.
  Hypothesis H1 :  3+2=5.

Require Import String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
(************************************************)
(* The syntax of differential dynamic logic. *)
(************************************************)
Definition Var := string.
(* Real-valued terms built using variables, constants
and arithmetic. *)
Inductive Term :=
| VarNowT : Var -> Term
| VarNextT : Var -> Term
| NatT : nat -> Term
| RealT : R -> Term
| PlusT : Term -> Term -> Term
| MinusT : Term -> Term -> Term
| MultT : Term -> Term -> Term.
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
| Comp : Term -> Term -> CompOp -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula
| PropF : Prop -> Formula
| Exists : forall T, (T -> Formula) -> Formula
| Forall : forall T, (T -> Formula) -> Formula
| Always : Formula -> Formula
| Eventually : Formula -> Formula.
(************************************************)
(* Some notation for the logic. *)
(************************************************)
Delimit Scope HP_scope with HP.
(*Term notation *)
Definition NatC (n:nat) : Term :=
NatT n.
Coercion NatC : nat >-> Term.
Definition ConstC (c:R) : Term :=
RealT c.
Coercion ConstC : R >-> Term.
Definition VarC (x:string) : Term :=
VarNowT x.
Coercion VarC : string >-> Term.
Notation "x !" :=
(VarNextT x) (at level 0) : HP_scope.
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
Notation "'\E' ( x : T ) , p" :=
(Exists T (fun x => p))
(at level 100) : HP_scope.
Notation "'\A' ( x : T ) , p" :=
(Forall T (fun x => p))
(at level 100) : HP_scope.
(*Notation "'Exists' x .. y , p" :=
(Exists (fun x => .. (Exists (fun y => p)) ..))
(at level 100, x binder, y binder) : HP_scope.*)
Notation "[] f" := (Always f)
(at level 95) : HP_scope.
Notation "<> f" := (Eventually f)
(at level 95) : HP_scope.

Require Import Syntax.
Require Import Coq.Reals.Rdefinitions.
CoInductive stream (A:Type) :=
| Cons : A -> stream A -> stream A.
Definition hd {A} (s:stream A) : A :=
match s with
| Cons a _ => a
end.
Definition tl {A} (s:stream A) : stream A :=
match s with
| Cons _ s' => s'
end.
Fixpoint nth_suf {A} (n:nat) (s:stream A) : stream A :=
match n with
| O => s
| S n => nth_suf n (tl s)
end.
(* All variables are real-valued. *)
Definition state := Var -> R.
Definition trace := stream state.
(* Semantics of real valued terms *)
Fixpoint eval_term (t:Term) (s1 s2:state) : R :=
(match t with
| VarNowT x => s1 x
| VarNextT x => s2 x
| NatT n => Raxioms.INR n
| RealT r => r
| PlusT t1 t2 => (eval_term t1 s1 s2) + (eval_term t2 s1 s2)
| MinusT t1 t2 => (eval_term t1 s1 s2) - (eval_term t2 s1 s2)
| MultT t1 t2 => (eval_term t1 s1 s2) * (eval_term t2 s1 s2)
end)%R.
(* Semantics of comparison operators *)
Definition eval_comp (t1 t2:Term) (op:CompOp) (s1 s2:state) :
Prop :=
let (e1, e2) := (eval_term t1 s1 s2, eval_term t2 s1 s2) in
let op := match op with
| Gt => Rgt
| Ge => Rge
| Lt => Rlt
| Le => Rle
| Eq => eq
end in
op e1 e2.
Fixpoint eval_formula (F:Formula) (tr:trace) :=
match F with
| TRUE => True
| FALSE => False
| Comp t1 t2 op => eval_comp t1 t2 op (hd tr) (hd (tl tr))
| And F1 F2 => eval_formula F1 tr /\
eval_formula F2 tr
| Or F1 F2 => eval_formula F1 tr \/
eval_formula F2 tr
| Imp F1 F2 => eval_formula F1 tr ->
eval_formula F2 tr
| PropF P => P
| Exists _ F => exists x, eval_formula (F x) tr
| Forall _ F => forall x, eval_formula (F x) tr
| Always F => forall n, eval_formula F (nth_suf n tr)
| Eventually F => exists n, eval_formula F (nth_suf n tr)
end.
Notation "|- F" := (forall tr, eval_formula F tr)
(at level 100) : HP_scope.
Open Scope string_scope.
Open Scope HP_scope.


Definition Init :Formula := "h" <= 0 /\ "b" >0.
Definition Hyp1:Formula := (0 <= "t" - "T").
Parameter d1:R.
Definition Hyp2:Formula := ("t"-"T"<=d1).

Definition Ind:Formula := "h" <= 0.
Variable v:R.
Variable c:R.

Hypothesis H4: (v + c)%R=4%R.
Definition H5:Formula := ("t" * (/2 )%R) <= 4%R.
Definition Hyp4:Formula := Forall R (fun t=> t <=d).
Definition Init1:Formula:= H5.

Definition Ind1:Formula := ("t" <= (8%R)).
Lemma ind_inv_init : |- Init1 --> Ind1.
simpl  in *. intros. Check hd. unfold eval_comp in *.
simpl in *. decompose [and] H.
z3 solve.
Require Import Coq.micromega.Psatz.
psatz R.

Qed.

End test.
