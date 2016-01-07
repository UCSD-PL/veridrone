Require Import ExtLib.Structures.Applicative.

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
