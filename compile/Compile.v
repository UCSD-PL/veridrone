Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import TLA.Syntax.
Require Import TLA.Lib.
Require Import TLA.Tactics.
Require Import String.
Require Import List.
Import ListNotations.
Print Formula.

Local Open Scope string_scope.

(* List of pairs of assignments and conditions *)
Definition tla_ir := list (Formula * Formula).

(* Input must be in disjunctive normal form,
   With first disjunct in each conjunct being an
   assignment. *)

Fixpoint no_nexts (tlat : Term) : bool :=
  match tlat with
    | VarNowT _ => true
    | VarNextT _ => false
    | NatT _ => true
    | RealT _ => true
    | PlusT a b => andb (no_nexts a) (no_nexts b)
    | MinusT a b => andb (no_nexts a) (no_nexts b)
    | MultT a b => andb (no_nexts a) (no_nexts b)
  end.


Definition is_assn (tla : Formula) : bool :=
  match tla with
    | (Comp (VarNextT upd) rhs Eq) => no_nexts rhs
    | _ => false
  end.

Fixpoint is_cond (tla : Formula) : bool :=
  match tla with
    | TRUE => true
    | FALSE => true
    | Comp t1 t2 op =>
      andb (no_nexts t1) (no_nexts t2)
    | And f1 f2 => andb (is_cond f1) (is_cond f2)
    | Or f1 f2 => andb (is_cond f1) (is_cond f2)
    | Imp f1 f2 => andb (is_cond f1) (is_cond f2)
    (* we can't handle the remaining cases *)
    | PropF _ => false
    | Syntax.Exists _ _ => false
    | Always _ => false
    | Eventually _ => false
  end.

Fixpoint tla2ir (tla : Formula) : (tla_ir + string) :=
  match tla with
    (* Or = outermost level *)
    | Or f1 f2 =>
      match ((tla2ir f1), (tla2ir f2)) with
        | (inl ir1, inl ir2) =>  inl (List.app ir1 ir2)
        | (inr s, _) => inr s
        | (_, inr s) => inr s
      end
    | And f1 f2 =>
      if is_assn f1 then
        if is_cond f2 then
           inl [(f1, f2)]
        else inr "invalid condition"%string
      else inr "invalid assignment"%string
    | _ => inr "malformed formula"%string
  end.

(* Returns the correct formula, or an explanation for why it failed to generate *)
Fixpoint ir2clight (ir : tla_ir) : (expr + string) :=
  match tla_ir with
    | _ => inr "Invalid formula constructor"%string
  end.

(* if-statement normal form: (cond /\ statement) \/ (cond2 /\ statement *)
