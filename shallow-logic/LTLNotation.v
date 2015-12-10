Require Import Coq.Reals.Rdefinitions.
Require Import ExtLib.Structures.Applicative.
Require Import SLogic.Logic.
Require Import SLogic.Instances.

Delimit Scope LTL_scope with LTL.

(* The following allows us to define one binop
   notation for StateVals, ActionVals, and TraceVals. *)
Definition lift1 {T U : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U) (x : F T) : F U :=
  Applicative.ap (Applicative.pure f) x.

Definition lift2 {T U V : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U -> V) (x : F T) (y : F U) : F V :=
  Applicative.ap (lift1 (F:=F) f x) y.

Notation "x `= y" := (lift2 eq x y)
                        (at level 20, no associativity)
                      : LTL_scope.
Notation "x `<= y" := (lift2 Rle x y)
                        (at level 20) : LTL_scope.
Notation "x `+ y" := (lift2 Rplus x y)
                        (at level 19, left associativity)
                      : LTL_scope.
Notation "x `- y" := (lift2 Rminus x y)
                        (at level 19, left associativity)
                      : LTL_scope.
Notation "x `* y" := (lift2 Rmult x y)
                        (at level 18, left associativity)
                      : LTL_scope.
Notation "x `/ y" := (lift2 Rdiv x y)
                        (at level 18, left associativity)
                      : LTL_scope.
Notation "`- x" := (lift1 Ropp x)
                      (at level 17, right associativity)
                    : LTL_scope.
Notation "`/ x" := (lift1 Rinv x)
                      (at level 17, right associativity)
                    : LTL_scope.

(* Notation for constants. *)
Notation "x #" := (pure x) (at level 5) : LTL_scope.

(* Some notation for pre and post states. *)
Notation "! x" := (pre x)
                    (at level 9, right associativity)
                  : LTL_scope.

Notation "x !" := (post x)
                    (at level 8, left associativity)
                  : LTL_scope.

(* Arithmetic notation *)
(* The following conflicts with the notation for R and for
   nat, so it becomes annoying when you have both scopes
   open. For now, we shouldn't use it. *)
(*
Class Arith (T : Type) : Type :=
  { plus  : T -> T -> T;
    minus : T -> T -> T;
    mult  : T -> T -> T;
    inv   : T -> T
  }.

Notation "x + y" := (plus x y) : LTL_scope.
Notation "x - y" := (minus x y) : LTL_scope.
Notation "x * y" := (mult x y) : LTL_scope.
Notation "/ x"   := (inv x) : LTL_scope.

Instance Arith_R : Arith R :=
{ plus  := Rplus;
  minus := Rminus;
  mult  := Rmult;
  inv   := Rinv
}.

Instance Arith_lift {T U} {A : Arith T} : Arith (U -> T) :=
{ plus  := fun a b x => plus (a x) (b x);
  minus := fun a b x => minus (a x) (b x);
  mult  := fun a b x => mult (a x) (b x);
  inv   := fun a x   => inv (a x)
}.
*)

(* Notation to "cast" between different types
   of formulas. *)
Notation "[ F ]" := (starts F) : LTL_scope.

(* Standard temporal logic notation. *)
Notation "[] f" := (always f)
                     (at level 72) : LTL_scope.
Notation "<> f" := (eventually f)
                     (at level 72) : LTL_scope.

(* Some test cases. *)

Record TestState : Type :=
{ x : R }.

Local Open Scope R_scope.
Local Open Scope LTL_scope.

Definition test_st1 : StateProp TestState :=
  x `= 1#.

Definition test_st2 : StateProp TestState :=
  x `+ 3# `= 1%R#.

Definition test_act : ActionProp TestState :=
  !x `= x!.

Definition test_tr1 : TraceProp TestState :=
  [][!test_st1].

Definition test_tr2 : TraceProp TestState :=
  [][test_act].

Definition test_tr3 : TraceProp TestState :=
  [][!(x `= 1#)].

Definition test_tr4 : TraceProp TestState :=
  [][(x `= 1#)!].

Definition test_tr5 : TraceProp TestState :=
  [][!x `= x!].

Close Scope LTL_scope.
Close Scope R_scope.