Require Import Coq.Vectors.VectorDef.

(* Copying the vector notations. *)
Local Notation "[]" := (nil _).
Local Notation "h :: t" := (cons _ h _ t)
  (at level 60, right associativity).

(* Real numbers *)

(* We need to figure out what formalization of real numbers
to use. A constructive formalization would probably be best
so that we can compute approximations. This suggests we
should use the CoRN library. *)

Parameter real : Type.
Parameter mult : real -> real -> real.
Parameter add  : real -> real -> real.
Parameter r1 : real.
Parameter r2 : real.
Parameter r3 : real.
Parameter r4 : real.
Parameter r5 : real.
Parameter r6 : real.
Parameter r7 : real.
Parameter r8 : real.

(* Inductive DSL definition *)
Definition DSL (In Out State : Type) : Type :=
  In -> State -> (Out * State).

Definition rstate n := t real n.

Definition P (kP : real) : DSL real real (rstate 0) :=
  fun err st => (mult kP err, st).

Definition PI (kP kI : real) : DSL real real (rstate 1) :=
  fun err st =>
    let i := add err (hd st) in
    (add (mult kP err) (mult kI i), i :: []).

(* Composing two DSLs *)
Definition compose {In Out1 Out2 State1 State2}
  (p1 : DSL In Out1 State1) (p2 : DSL Out1 Out2 State2) :
  DSL In Out2 (State1*State2) :=
  fun x st =>
    let (st1, st2) := st in
    let (out1, st1') := p1 x st1 in
    let (out2, st2') := p2 out1 st2 in
    (out2, (st1', st2')).

(* I have no idea how to set the level for notation. *)
Notation "p1 ;; p2" := (compose p1 p2) (at level 10).

Definition partial_compose {In1 In2 Out1 Out2 State1 State2}
  (p1 : DSL In1 Out1 State1)
  (p2 : DSL (In2 * Out1) Out2 State2) :
  DSL (In1 * In2) Out2 (State1 * State2) :=
  fun (x : In1 * In2) st =>
    let (x1, x2) := x in
    let (st1, st2) := st in
    let (out1, st1') := p1 x1 st1 in
    let (out2, st2') := p2 (x2, out1) st2 in
    (out2, (st1', st2')).

Notation "p1 ;;; p2" := (partial_compose p1 p2) (at level 10).

(* Simulating a DSL. Its output type must be the same
   as its input type. *)
Fixpoint simulate {State In1 In2}
  (p:DSL (In1 * In2) In1 State) steps init :
  t In2 steps -> t (In1 * State) steps :=
  match steps with
  | O => fun _ => []
  | S steps => fun stream =>
    let (out, st) := p (fst init, hd stream) (snd init) in
    (out, st) :: simulate p steps (out, st) (tl stream)
  end.

(* A DSL that consists of a sensor, a single PI controller,
   and a world. *)

(* The world just has one variable. It really should be
   defined as a system of differential equations. *)
Definition world :
  DSL (real * real) real (rstate 1) :=
  fun x st =>
    let (act, dT) := x in
    let st' := add (mult act dT) (hd st) :: [] in
    (hd st', st').

Definition sensor : DSL real real (rstate 0) :=
  fun height _ =>
    (height, []).

Definition controller : DSL real real (rstate 1) := PI r1 r2.

Definition system := sensor;; controller;;; world.

Definition init_wstate := r4 :: [].
Definition init_pistate := r5 :: [].

Eval vm_compute in simulate system 5
  (r6, (nil _, init_pistate, init_wstate))
  (r8 :: r8 :: r8 :: r8 :: r8 :: []).