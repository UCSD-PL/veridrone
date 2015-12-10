Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.PreFun.
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

Definition lift3 {T U V W : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U -> V -> W) (x : F T) (y : F U) (z : F V) : F W :=
  Applicative.ap (lift2 (F:=F) f x y) z.

Notation "x `= y" := (lift2 eq x y)
                        (at level 70, no associativity)
                      : LTL_scope.
Notation "x `<= y" := (lift2 Rle x y)
                        (at level 70) : LTL_scope.
Notation "x `> y" := (lift2 Rge x y)
                        (at level 70) : LTL_scope.
Notation "x `< y" := (lift2 Rlt x y)
                        (at level 70) : LTL_scope.
Notation "x `> y" := (lift2 Rgt x y)
                        (at level 70) : LTL_scope.

Notation "x `+ y" := (lift2 Rplus x y)
                        (at level 50, left associativity)
                      : LTL_scope.
Notation "x `- y" := (lift2 Rminus x y)
                        (at level 50, left associativity)
                      : LTL_scope.
Notation "x `* y" := (lift2 Rmult x y)
                        (at level 40, left associativity)
                      : LTL_scope.
Notation "x `/ y" := (lift2 Rdiv x y)
                        (at level 40, left associativity)
                      : LTL_scope.
Notation "`- x" := (lift1 Ropp x)
                      (at level 35, right associativity)
                    : LTL_scope.
Notation "`/ x" := (lift1 Rinv x)
                      (at level 35, right associativity)
                    : LTL_scope.

Notation "x `:: y" := (lift2 List.cons x y)
                        (at level 60, right associativity)
                      : LTL_scope.


(* Notation for constants. *)
(* Notation "# x" := (pure x) (at level 5) : LTL_scope. *)

(* Notation for fields *)
Notation "x # y" := (PreFun.compose y x) (at level 0).


(* Some notation for pre and post states. *)
Notation "! x" := (pre x)
                    (at level 9, right associativity)
                  : LTL_scope.

Notation "x !" := (post x)
                    (at level 8, left associativity)
                  : LTL_scope.

Arguments texists _ {_} _ _.

Notation "'TExists' T , F" :=
  (@texists T _ F) (at level 78, T at level 200).

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


(** n-ary lifting **)
Fixpoint arrows (ls : list Type) (r : Type) : Type :=
  match ls with
  | nil => r
  | l :: ls => l -> arrows ls r
  end.

Structure arrows_for : Type :=
{ af_type   :> Type
; af_arrows : list Type
; af_ret    : Type
; af_cast   : af_type -> arrows af_arrows af_ret
}.

Arguments af_cast {_} _.

Canonical Structure arrows_for_Fun {A : Type} (l : arrows_for) : arrows_for :=
{| af_type   := A -> af_type l
 ; af_arrows := A :: af_arrows l
 ; af_ret    := af_ret l
 ; af_cast   := fun f x => af_cast (f x)
 |}.

Canonical Structure arrows_for_Else {A} : arrows_for :=
{| af_type   := A
 ; af_arrows := nil
 ; af_ret    := A
 ; af_cast   := fun x => x
 |}.

Section _liftn.
  Context {F : Type -> Type}.
  Context {ApF : Applicative F}.

  Fixpoint _liftn' {ls : list Type} {T : Type} {struct ls}
  : F (arrows ls T) -> arrows (List.map F ls) (F T) :=
    match ls as ls return F (arrows ls T) -> arrows (List.map F ls) (F T) with
    | nil => fun x => x
    | l :: ls => fun Ff Fx => @_liftn' _ _ (ap Ff Fx)
    end.

  Definition _liftn {af : arrows_for} (val : af.(af_type))
  : arrows (List.map F af.(af_arrows)) (F af.(af_ret)) :=
    _liftn' (pure (af_cast val)).
End _liftn.

Notation "'`' x" := (@_liftn _ _ _ x) (at level 0).
(*
Structure Lifter : Type :=
{ lift_type :> Type
; lift_to   : Type
; liftn : lift_type -> lift_to
}.

Canonical Structure Lifter0 {F} {ApF : Applicative F} (A : Type) : Lifter :=
{| lift_type := A
 ; lift_to   := F A
 ; liftn     := pure
 |}.

Canonical Structure Lifter1 {F} {ApF : Applicative F} (A B : Type) : Lifter :=
{| lift_type := A -> B
 ; lift_to   := F A -> F B
 ; liftn := _liftn
 |}.

Canonical Structure Lifter2 {F} {ApF : Applicative F} (A B C : Type) : Lifter :=
{| lift_type := A -> B -> C
 ; lift_to   := F A -> F B -> F C
 ; liftn := _liftn
 |}.

Canonical Structure Lifter3 {F} {ApF : Applicative F} (A B C D : Type) : Lifter :=
{| lift_type := A -> B -> C -> D
 ; lift_to   := F A -> F B -> F C -> F D
 ; liftn     := _liftn
 |}.

Canonical Structure Lifter4 {F} {ApF : Applicative F} (A B C D E : Type) : Lifter :=
{| lift_type := A -> B -> C -> D -> E
 ; lift_to   := F A -> F B -> F C -> F D -> F E
 ; liftn     := _liftn
 |}.

Canonical Structure Lifter5 {F} {ApF : Applicative F} (A B C D E X : Type) : Lifter :=
{| lift_type := A -> B -> C -> D -> E -> X
 ; lift_to   := F A -> F B -> F C -> F D -> F E -> F X
 ; liftn     := _liftn
 |}.

Canonical Structure Lifter6 {F} {ApF : Applicative F} (A B C D E X Y : Type) : Lifter :=
{| lift_type := A -> B -> C -> D -> E -> X -> Y
 ; lift_to   := F A -> F B -> F C -> F D -> F E -> F X -> F Y
 ; liftn     := _liftn
 |}.
Notation "'`' x" := (@liftn _ x) (at level 0).
*)

(* Some test cases. *)

Record TestState : Type :=
{ x : R }.

Local Open Scope R_scope.
Local Open Scope LTL_scope.

Definition test_st1 : StateProp TestState :=
  x `= pure 1.

Definition test_st2 : StateProp TestState :=
  x `+ pure 3 `= pure 1%R.

Definition test_act : ActionProp TestState :=
  !x `= x!.

Definition test_tr1 : TraceProp TestState :=
  [][!test_st1].

Definition test_tr2 : TraceProp TestState :=
  [][test_act].

Definition test_tr3 : TraceProp TestState :=
  [][!(x `= pure 1)].

Definition test_tr4 : TraceProp TestState :=
  [][(x `= pure 1)!].

Definition test_tr5 : TraceProp TestState :=
  [][!x `= x!].
