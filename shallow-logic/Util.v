Require Import Coq.Lists.List.
Require Import Charge.Logics.ILogic.
Require Import SLogic.Logic.
Require Import SLogic.LTLNotation.

Local Open Scope LTL_scope.

(* Is there a simple way to make this heterogenous? *)
(* Specifies that a list of [StateVal]s don't change
   during a transition. *)
Fixpoint Unchanged {st T : Type} (xs : list (StateVal st T))
  : ActionProp st :=
  match xs with
  | nil => ltrue
  | x :: xs =>
    x! `= !x //\\ Unchanged xs
  end.
