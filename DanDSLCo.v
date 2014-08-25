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

(* Co-inductive DSL definitions *)
CoInductive DSL (In Out : Type) : Type :=
| C : (In -> (Out * DSL In Out)) -> DSL In Out.

Arguments C {In Out} _.

CoFixpoint P (kP : real) : DSL real real :=
  C (fun err => (mult kP err, P kP)).

CoFixpoint PI (kP kI i : real) : DSL real real :=
  C (fun err =>
       let i := add err i in
       (add (mult kP err) (mult kI i), PI kP kI i)).

CoFixpoint compose {In Out1 Out2}
  (p1 : DSL In Out1) (p2 : DSL Out1 Out2) : DSL In Out2 :=
  C (fun x =>
       match p1, p2 with
         | C f1, C f2 =>
           let (out1, p1') := f1 x in
           let (out2, p2') := f2 out1 in
           (out2, compose p1' p2')
       end).

(* I have no idea how to set the level for notation.
   Since 10 is my favorite number, it seems as good
   a choice as any. *)
Notation "p1 ;; p2" := (compose p1 p2) (at level 10).

CoFixpoint partial_compose {In1 In2 Out1 Out2}
  (p1 : DSL In1 Out1) (p2 : DSL (In2 * Out1) Out2) :
  DSL (In1 * In2) Out2 :=
  C (fun x : In1 * In2 =>
       let (x1, x2) := x in
       match p1, p2 with
         | C f1, C f2 =>
           let (out1, p1') := f1 x1 in
           let (out2, p2') := f2 (x2, out1) in
           (out2, partial_compose p1' p2')
       end).

Notation "p1 ;;; p2" := (partial_compose p1 p2) (at level 10).

Fixpoint simulate {In1 In2} (p:DSL (In1 * In2) In1)
  steps init : t In2 steps -> t In1 steps :=
  match steps with
    | O => fun _ => []
    | S steps => fun stream =>
      match p with
        | C f => let (o, p) := f (init, hd stream) in
                 o :: simulate p steps o (tl stream)
      end
  end.

(* The world just has one variable. It really should be
   defined as a system of differential equations. *)
CoFixpoint world (height : real) :
  DSL (real*real) real :=
  C (fun x : real * real =>
       let (act, dT) := x in
       let height := add (mult act dT) height in
       (height, world height)).

CoFixpoint sensor : DSL real real :=
  C (fun height => (height, sensor)).

Definition controller : DSL real real := PI r1 r2 r3.

Definition system := sensor;; controller;;; (world r4).

Eval vm_compute in simulate system 5 r7 
  (r8 :: r8 :: r8 :: r8 :: r8 :: []).