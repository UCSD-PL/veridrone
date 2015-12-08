Require Import ExtLib.Structures.Applicative.
Require Import SLogic.Logic.
Require Import SLogic.Instances.

Delimit Scope HP_scope with HP.


(* Notation for state functions. *)
Definition lift1 {T U : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U) (x : F T) : F U :=
  Applicative.ap (Applicative.pure f) x.

Definition lift2 {T U V : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U -> V) (x : F T) (y : F U) : F V :=
  Applicative.ap (lift1 (F:=F) f x) y.

Notation "x [=] y" := (lift2 eq x y)
                        (at level 20) : HP_scope.

(* Coercions so that formulas don't become
   cluttered with currently and starts. *)
Coercion currently : StateProp >-> ActionProp.
Coercion starts : ActionProp >-> TraceProp.

(* Standard temporal logic notation. *)
Notation "[] f" := (always f)
                     (at level 72) : HP_scope.
Notation "<> f" := (eventually f)
                     (at level 72) : HP_scope.

(* Some test cases. *)

Record State : Type :=
{ x : nat }.

Open Scope HP_scope.

Notation "x #" := (pure x) (at level 5) : HP_scope.

Definition test_st : StateProp State :=
  x [=] 1#.

Definition test_act : ActionProp State :=
  pre x [=] post x.

Definition test_tr1 : TraceProp State :=
  []test_st.

Definition test_tr2 : TraceProp State :=
  []test_act.

(* The following test cases don't work. *)
(*
Definition test_tr3 : TraceProp State :=
  [](x [=] 1#).

Definition test_tr4 : TraceProp State :=
  [](pre x [=] post x).
*)

(* We also still need notation for arithmetic operations. *)

Close Scope HP_scope.