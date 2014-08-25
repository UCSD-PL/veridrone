Require Import ZArith.
Require Import List.

Local Open Scope Z_scope.

(** Numbers **)
(*************)
(** We'll think of this in terms of 1000s **)
Definition real : Type := Z.
Definition mult (a b : real) : real :=
  Z.div (Z.mul a b) 1000.
Definition div (a b : real) : real :=
  Z.div (Z.mul a 1000) b.
Definition plus (a b : real) : real :=
  Z.add a b.
Definition lt (a b : real) : bool :=
  if Z_lt_dec a b then true else false.

(* Time *)
Definition time := real.

(** The "DSL" is just a Coq data type **)
(***************************************)

(** The simplest DSL is just a function space, it doesn't allow
 ** for any local state
 **)
Definition DSL (In Out : Type) : Type :=
  In -> Out.
Definition const {T U : Type} (val : U) : DSL T U :=
  fun _ => val.

(** Some simple DSL "functions" **)

(** The simplest version of a Pid which just has P **)
Definition P (n : real) : DSL (real * real) real :=
  fun a => mult (fst a) (snd a).

(** This returns [-1 or 0 or 0] based on the relationship
 ** between the first and second value
 **)
Definition I : DSL (real * real) real :=
  fun a => if lt (fst a) (snd a) then -1000
           else if lt (snd a) (fst a) then 1000
                else 0.

(** The program for the quad-coptor **)
(*************************************)

(** We'll interpret this as a percentage of thrust **)
Definition Actuator : Type := real.

(** A trivial controller **)
Module TrivialController.
  (* The input to the controller *)
  Record HeightInput : Type :=
  { Desired : real (* m *)
  ; Current : real (* m *)
  }.

  (** The best that we can do without knowing what our current thrust
   ** is to simply move in the desired direction.
   ** We need to create some sort of feedback to do better.
   **)
  Definition HeightCtrl : DSL HeightInput Actuator :=
    fun a => mult 500 (I (a.(Desired), a.(Current))).
End TrivialController.

(** A slightly more comlex controller that also knows
 ** how fast it is going
 **)
Module AwareController.
  (* The input to the controller *)
  Record HeightInput : Type :=
  { Desired : real (* m *)
  ; Current : real (* m *)
  ; Current_speed : real (* m *)
  }.

  (** The best that we can do without knowing what our current thrust
   ** is to simply move in the desired direction.
   ** We need to create some sort of feedback to do better.
   **)
  Definition HeightCtrl (dT : time (* s *)) : DSL HeightInput Actuator :=
    fun a =>
      (* determine where we will be *)
      let final :=
          plus a.(Current) (mult a.(Current_speed) dT)
      in
      mult 500 (I (a.(Desired), final)).
End AwareController.

(** The world **)
(* The state of the world *)
Record WorldState : Type :=
{ Height : real
; dHeight : real
}.

(** lift is a force:  [kg * m/s^2]
 ** weight is a mass: [kg]
 **)
Definition world (dT : time) (max_lift : real) (weight : real)
: DSL (Actuator * WorldState) WorldState :=
  fun act_world =>
    let '(act,world) := act_world in
    {| Height  := plus world.(Height) (mult world.(dHeight) dT)
     ; dHeight :=
         (** TODO: This model should at least factor in gravity! **)
         (* plus world.(dHeight) ( *) mult (div (mult max_lift act) weight) dT
     |}.

(** A simulator to see how we're doing **)

Section driver.
  Variable TworldState : Type.
  Variable Tactuator : Type.
  Variable Tsensor : Type.

  Variable world : DSL (Tactuator * TworldState) (TworldState).
  Variable sensor : DSL TworldState Tsensor.
  Variable client : DSL Tsensor Tactuator.

  (** The driver is a simulator that combines the world and
   ** the code.
   **)
  Fixpoint driver (initial : TworldState) (steps : nat) : list TworldState :=
    match steps with
      | O => nil
      | S steps =>
        (** sense **)
        let sense := sensor initial in
        (** react **)
        let act := client sense in
        (** update the world **)
        let world' := world (act, initial) in
        world' :: driver world' steps
    end.

End driver.

Notation "[ x , .. , y ]" := ((cons x (.. (cons y nil) ..))).

(** The TrivialController doesn't converge **)
Eval vm_compute in
    let goal     := 5000 (* 5   m *) in
    let initial  := {| Height  := 3000 (* 3 m *)
                     ; dHeight := 0    (* 0 m/s *)
                     |} in
    let dT       := 1000 (* 1   s *) in
    let max_lift := 1000 (* 1   kg *m/s^ *) in
    let weight   := 1000 (* 1 kg *) in
    let HeightCtrl : DSL real Actuator :=
        fun sense =>
          TrivialController.HeightCtrl
            {| TrivialController.Desired := goal
             ; TrivialController.Current := sense
             |}
    in
    @driver _ _ _ (world dT max_lift weight) (Height) HeightCtrl initial 15.

(** The AwareController does coverge **)
Eval vm_compute in
    let goal     := 5000 (* 5   m *) in
    let initial  := {| Height  := 3000 (* 3 m *)
                     ; dHeight := 0    (* 0 m/s *)
                     |} in
    let dT       := 1000 (* 1   s *) in
    let max_lift := 1000 (* 1   kg *m/s^ *) in
    let weight   := 1000 (* 1 kg *) in
    let sensor   : DSL WorldState WorldState :=
        fun x => x
    in
    let HeightCtrl : DSL WorldState Actuator :=
        fun sense =>
          AwareController.HeightCtrl dT
            {| AwareController.Desired := goal
             ; AwareController.Current := sense.(Height)
             ; AwareController.Current_speed := sense.(dHeight)
             |}
    in
    @driver _ _ _ (world dT max_lift weight) sensor HeightCtrl initial 15.


(** Compiling it **)
(******************)
Require Import String.
(** Note that this is very naive **)
Inductive Verilog :=
| vLET   : nat -> Verilog -> Verilog -> Verilog
| vMULT  : Verilog -> Verilog -> Verilog
| vPLUS  : Verilog -> Verilog -> Verilog
| vDELAY : real -> Verilog -> Verilog
| vCONST : real -> Verilog
| vIF    : Verilog -> Verilog -> Verilog -> Verilog
| vLT    : Verilog -> Verilog -> Verilog
| vGET   : nat -> Verilog
| vEXPLODE : Verilog.

(** TODO: Need a semantics for Verilog, possibly/probably with timing **)
Axiom VStep : list real -> Verilog -> time -> real -> Prop.

(** The correctness of a compiler specifies a correspondence between a
 ** DSL program and Verilog program
 ** This very simple definition is cleary not compositional!
 **)
Definition DSL_to_V (prg : DSL (list real) real) (v : Verilog) (t : time) : Prop :=
  forall input : list real,
    let output := prg input in
    VStep input v t output.


(** The compilation of [I] is parameterized by the
 ** Verilog expressions that represent the inputs
 **)
Definition I_V (a b : Verilog) : Verilog :=
  vIF (vLT a b) (vCONST 1000) (vIF (vLT b a) (vCONST (-1000)) (vCONST 0)).

(** The compilation of [TrivialController.HeightCtrl] uses
 ** [I_V]
 **)
Definition HeightCtrl_V : Verilog :=
  vMULT (vCONST 500) (I_V (vGET 0) (vGET 1)).

Axiom junk : real.

Axiom HeightCtrl_Ok : exists dT : time,
                        DSL_to_V (fun ls => (** we can avoid/derive this kind of casting with stronger types **)
                                    match ls with
                                      | a :: b :: nil =>
                                        TrivialController.HeightCtrl
                                          {| TrivialController.Desired := a
                                           ; TrivialController.Current := b
                                           |}
                                      | _ => junk
                                    end)
                                 HeightCtrl_V
                                 dT.

(** You need to define combinators that reason about VStep **)


(** If the shallow embedding doesn't work out, then we can always convert our
 ** language to a deep embedding by doing
 **)
Inductive DDSL :=
| DP (r : real)
| DI
(** etc.,, **)
.

(** obviously we need to track better information about types
 ** in order to do composition.
 **)
Fixpoint denote_DDSL (d : DDSL) : DSL (real * real) real :=
  match d with
    | DP r => P r
    | DI => I
  end.
