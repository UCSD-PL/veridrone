Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import SLogic.Logic.
Require Import SLogic.Instances.
Require Import SLogic.LTLNotation.

(* A library of useful formulas, built
   from logic primitives. *)

Local Open Scope LTL_scope.

Section Lib.

  Variable state : Type.

  (** Both [ContProp] and [DiffProp] are ILogics **)

  (** Predicates over continuous transitions *)
  Definition ContProp : Type :=
    (R -> state) -> R -> Prop.

  (** Predicates over a state function using its derivative
   ** - [V] is an index for the differential variables
   ** - [Dv] interprets these into the state
   **)
  Definition DiffVal (V : Type) (Dv : V -> state -> R) (T : Type) : Type :=
    (V -> R) ->      (* the derivative *)
    StateVal state T. (* the current state *)

  Definition DiffProp (V : Type) (Dv : _) : Type :=
    DiffVal V Dv Prop.

  (** The derivative of [g] is [g'] on the interval [from, to] **)
  Definition D_is_on (from to : R) (g g' : R -> R) : Prop :=
    exists is_derivable : forall t', derivable_pt g t',
      (forall t', from <= t' <= to ->
                  derive_pt g t' (is_derivable t') = g' t')%R.

  (** [DiffProp]s can be used as predicates over continuous
   ** transitions.
   **)
  Definition DiffToCont {V} {Dv} (P : DiffProp V Dv) : ContProp :=
    fun f last =>
      exists f' : V -> R -> R,
        (forall x : V, D_is_on 0 last (fun t => Dv x (f t)) (f' x)) /\
        (forall x : V, forall t : R,
              0 <= t <= last ->
              P (fun z => f' z t) (f t))%R.

  (** An easy way to build a finite set of functions is
   ** to use a list. This predicate is just like [In]
   **)
  Inductive member {T} : list T -> Type :=
  | MO : forall t ls, member (t :: ls)
  | MS : forall t' ls, member ls -> member (t' :: ls).

  (** Get the element corresponding to a [member] **)
  Fixpoint list_get {T} {l : list T} (m : member l) : T :=
    match m with
    | @MO val _ => val
    | @MS _ _ m => list_get m
    end.

  (** Using [member] for a simple differential **)
  Definition SimpleDiffVal (ls : list (StateVal state R)) (T : Type) : Type :=
    DiffVal (member ls) (fun m st => list_get m st) T.

  Class find_member {T} (t : T) (ls : list T) : Type :=
  { the_member : member ls }.
  Global Instance find_member_here {T} (t : T) (ls : list T) : find_member t (t :: ls) :=
  {| the_member := MO _ _ |}.
  Global Instance find_member_next {T} (t t' : T) (ls : list T) (f : find_member t ls)
  : find_member t (t' :: ls) :=
  {| the_member := MS _ _ f.(@the_member _ _ _ ) |}.

  Definition D {ls : list (StateVal state R)} (x : StateVal state R) {f : find_member x ls}
  : SimpleDiffVal ls R :=
    fun f' _ => f' f.(@the_member _ _ _).


(*
  Definition trial (A B : StateVal state R) : SimpleDiffVal (A :: B :: nil) R :=
    D (ls := A :: B :: nil) A.

  Print trial.


  (* ActionProp expressing that all StateVals
     in xs are unchanged. *)
  (* Is there an easy way to implement Unchanged
     for heterogenous lists? *)
  Fixpoint Unchanged {T} (xs:list (StateVal state T)) :
    ActionProp state :=
    match xs with
    | nil => ltrue
    | cons x xs =>
      (x! `= !x) //\\ (Unchanged xs)
    end.
*)

  (* Now we specify continuous transitions. *)
  (* The following is from one of Gregory's attempts
     at a continuous logic. Can we use something
     similar here? *)
(*

  Definition deriv (g : R -> R)
             (P : (R -> R) -> EvolveProp) : EvolveProp :=
    Exists g', embed (D_is g g') //\\ P g'.
*)

(* Here's an attempt at continuous that gets a bit
   messy. *)
(*
  Definition derivatives (xs : list (StateVal state R))
    : Type :=
    forall (x : StateVal state R), In x xs -> R.

  Definition Evolution (xs : list (StateVal state R))
    : Type :=
    derivatives xs -> StateProp state.

  Definition deriv_stateF
           (f : R -> state)
           (xs : list (StateVal state R))
           (is_derivable : forall x, In x xs ->
               derivable (fun t => x (f t))) :
    R -> derivatives xs :=
    fun r x H => derive (fun t => x (f t))
                        (is_derivable x H) r.

  (* Expresses the property that a differentiable function
     is a solution to a list of differential equations
     in the range 0 to r. *)
  Definition solves_diffeqs (f : R -> state) (r : R)
             (xs : list (StateVal state R))
             (cp : Evolution xs)
             (is_derivable : forall x, In x xs ->
                 derivable (fun t => x (f t))) : Prop :=
    forall z, (R0 <= z <= r)%R ->
              (cp (deriv_stateF f xs is_derivable z))
                (f z).

  (* Prop expressing that f is a solution to cp in
     [0,r]. *)
  Definition is_solution (f : R -> state) (r : R)
             (xs : list (StateVal state R))
             (cp:Evolution xs) : Prop :=
    exists is_derivable,
      (* f is a solution to diffeqs *)
      solves_diffeqs f r xs cp is_derivable.

  (* ActionProp expressing that a transition
     is consistent with the system of differential
     equations represented by cp. *)
  Definition Continuous (xs : list (StateVal state R))
             (cp:Evolution xs) : ActionProp state :=
    Exists r : R,
    Exists f : R -> state,
      embed (r > 0)%R //\\
      embed (is_solution f r xs cp) //\\
      (fun st st' => f 0%R = st /\ f r = st').
*)

End Lib.

Close Scope LTL_scope.