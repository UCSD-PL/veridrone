Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require Import SLogic.Logic.
Require Import SLogic.Instances.

(* A library of useful formulas, built
   from logic primitives. *)

Section Continuous.

  Variable state : Type.

  (** Both [ContProp] and [DiffProp] are ILogics **)

  (** Predicates over continuous transitions *)
  Definition ContProp : Type :=
    (R -> state) -> R -> Prop.

  (** Predicates over a state function using its derivative
   ** - [V] is an index for the differential variables
   ** - [Dv] interprets these into the state
   **)
  Definition DiffVal (V : Type) (Dv : V -> state -> R)
             (T : Type) : Type :=
    (V -> R) ->      (* the derivative *)
    StateVal state T. (* the current state *)

  Definition DiffProp (V : Type) (Dv : _) : Type :=
    DiffVal V Dv Prop.

  (** The derivative of [g] is [g'] on the interval
      [from, to] **)
  Definition D_is_on (from to : R) (g g' : R -> R) : Prop :=
    exists is_derivable : forall t', derivable_pt g t',
      (forall t', from <= t' <= to ->
                  derive_pt g t' (is_derivable t') = g' t')%R.

  (** [DiffProp]s can be used as predicates over continuous
   ** transitions.
   **)
  Definition DiffToCont {V} {Dv} (P : DiffProp V Dv)
    : ContProp :=
    fun f last =>
      exists f' : V -> R -> R,
        (forall x : V,
            D_is_on 0 last (fun t => Dv x (f t)) (f' x)) /\
        (forall x : V, forall t : R,
              0 <= t <= last ->
              P (fun z => f' z t) (f t))%R.
  
  (* [ContProp]s can be embeded as [ActionProp]s. *)
  Definition ContToAction (P : ContProp) : ActionProp state :=
    Exists r : R,
    Exists f : R -> state,
      embed (r > 0)%R //\\
      embed (P f r) //\\
      (fun st st' => f 0%R = st /\ f r = st').

  (* And finally, our definition of continuous transitions. *)
  Definition Continuous {V} {Dv} (P : DiffProp V Dv)
    : ActionProp state :=
    ContToAction (DiffToCont P).

  (* Now we write some definitions to make it easy
     to build [DiffProp]s. *)

  (** An easy way to build a finite set of functions is
   ** to use a list. This predicate is just like [In]
   **)
  Inductive member {T} : list T -> Type :=
  | MO : forall t ls, member (t :: ls)
  | MS : forall t' ls, member ls -> member (t' :: ls).

  (** Get the element corresponding to a [member] **)
  Fixpoint list_get {T} {l : list T} (m : member l) : T :=
    match m with
    | @MO _ val _ => val
    | @MS _ _ _ m => list_get m
    end.

  (** Using [member] for a simple differential **)
  Definition SimpleDiffVal (ls : list (StateVal state R))
             (T : Type) : Type :=
    DiffVal (member ls) (fun m st => list_get m st) T.

  Class find_member {T} (t : T) (ls : list T) : Type :=
  { the_member : member ls }.
  Global Instance find_member_here {T} (t : T)
         (ls : list T) : find_member t (t :: ls) :=
  {| the_member := MO _ _ |}.
  Global Instance find_member_next {T} (t t' : T)
         (ls : list T) (f : find_member t ls)
  : find_member t (t' :: ls) :=
  {| the_member := MS _ _ f.(@the_member _ _ _ ) |}.

  Definition D {ls : list (StateVal state R)}
             (x : StateVal state R) {f : find_member x ls}
  : SimpleDiffVal ls R :=
    fun f' _ => f' f.(@the_member _ _ _).

  Definition SimpleDiffProp (ls : list (StateVal state R))
    : Type := SimpleDiffVal ls Prop.

  Definition SimpleContinuous {ls} (P : SimpleDiffProp ls) :=
    Continuous (Dv:=fun m st => list_get m st) P.

End Continuous.

Arguments D {_ _} _ {_ _} _.