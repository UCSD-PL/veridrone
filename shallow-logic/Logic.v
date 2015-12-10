Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Tactics.
Require Import Charge.Logics.ILogic.
Require Charge.Logics.ILInsts.
Require Import SLogic.Stream.

Section with_state.

  Variable state : Type.

  (* Functions over states, pairs of states, and traces. *)
  Definition StateVal (T : Type) : Type :=
    state -> T.
  Definition ActionVal (T : Type) : Type :=
    state -> state -> T.
  Definition TraceVal (T : Type) :=
    trace state -> T.

  (* Predicates over states. *)
  Definition StateProp := StateVal Prop.

  (* Relations over states, specifying transitions. *)
  Definition ActionProp := ActionVal Prop.

  (* Predicates over traces. *)
  Definition TraceProp := TraceVal Prop.

  (* Useful functions for expressing action values. *)
  (* Can also be used to coerce a StateProp to an
     ActionProp. *)
  Definition pre {T} (f : StateVal T) : ActionVal T :=
    fun st _ => f st.

  Definition post {T} (f : StateVal T) : ActionVal T :=
    fun _ st' => f st'.

  (* Coercion from an action prop to a trace prop. *)
  Definition starts (P : ActionProp) : TraceProp :=
    fun tr => P (hd tr) (hd (tl tr)).

  (* Expresses that a state property holds on the
     next state. *)
  Definition next (P : TraceProp) : TraceProp :=
    fun tr => P (tl tr).

  (* Expresses that transition that the action property
     allows. *)
  Definition enabled (ap : ActionProp) : StateProp :=
    Exists st', fun st => ap st st'.

  (* Standard always modality from temporal logic *)
  Definition always (P : TraceProp) : TraceProp :=
    fun tr => forall n, P (nth_suf tr n).

  (* Standard eventually modality from temporal logic *)
  Definition eventually (P : TraceProp) : TraceProp :=
    fun tr => exists n, P (nth_suf tr n).

  (* Stuttering steps. *)
  Definition stutter {T} (f : state -> T) : ActionProp :=
    fun st st' => f st = f st'.

End with_state.

Arguments pre {_ _} _ _ _.
Arguments post {_ _} _ _ _.
Arguments always {_} _ _.
Arguments eventually {_} _ _.
Arguments starts {_} _ _.
Arguments stutter {_ _} _ _ _.

Section simulations.
  Context {T U : Type}.
  Variable f : U -> T.
  Context {V : Type}.

  Definition focusT (P : TraceVal T V) : TraceVal U V :=
    fun tu => P (fmap f tu).

  Definition focusS (P : StateVal T V) : StateVal U V :=
    fun tu => P (f tu).

  Definition focusA (P : ActionVal T V) : ActionVal U V :=
    fun st st' => P (f st) (f st').

End simulations.

(* Temporal Existential Quantification *)
Section temporal_exists.

  Context {T U : Type}.

  Definition texists (P : TraceProp (T * U)) : TraceProp U :=
    fun tr : trace U => exists tr' : trace T,
                       P (trace_zip pair tr' tr).

End temporal_exists.