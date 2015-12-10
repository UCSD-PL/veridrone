Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import SLogic.Logic.
Require Import SLogic.LTLNotation.

Definition strict_increasing_pos (f : R -> R) :=
  forall x y, (0 <= x < y -> f x < f y)%R.

Definition strict_decreasing_pos (f : R -> R) :=
  forall x y, (0 <= x < y -> f y < f x)%R.

Definition K_fun (f : R -> R) :=
  continuity f /\ strict_increasing_pos f.

Definition L_fun (f : R -> R) :=
  continuity f /\ strict_decreasing_pos f.

Definition KL_fun (f : R -> R -> R) :=
  (forall t, K_fun (fun c => f c t)) /\
  (forall c, L_fun (fun t => f c t)).

Definition KLD_fun (f : R -> R -> R) :=
  KL_fun f /\
  forall (c s t : R),
    (f c 0 = c /\ f c (s + t) = f (f c s) t)%R.

Section Robustness.

  Variable state : Type.
  (* Input cost - this quantifies the disturbance. *)
  Variable IC : StateVal state R.
  (* Output cost - this quantifies the deviation
     from the nominal behavior. *)
  Variable OC : StateVal state R.
  (* The StateVal tracking time. *)
  Variable t : StateVal state R.

  Record dist_state : Type :=
    { ds : list (R * R) }.

  Local Open Scope LTL_scope.

  Notation "x `:: y" := (lift2 cons x y)
                          (at level 60, right associativity)
                        : LTL_scope.

  Definition acc_dist (gamma : R -> R)
    : ActionProp (dist_state * state) :=
    (focusS fst ds)! `=
    !((focusS snd (lift2 pair t (lift1 gamma IC))) `::
      (focusS fst ds)).

  Require Import Coq.Lists.List.
  Fixpoint max_of_list {T} (comp : T -> T -> bool)
           (xs : list T) (default : T) : T :=
    match xs with
    | nil => default
    | x :: xs =>
      let m := max_of_list comp xs default in
      if comp m x then x else m
    end.

  Definition max_R (default : R) (xs : list R) :=
    max_of_list (fun r1 r2 => if RIneq.Rle_dec r1 r2
                              then true else false)
                xs default.

  Definition bounded (mu : R -> R -> R) (rho : R)
    : StateProp (dist_state * state) :=
    focusS snd OC `<=
    lift1 (max_R R0)
    (lift2 (F:=StateVal (dist_state * state)) (@map (R * R) R)
           (fun st p => mu (fst p) ((t (snd st)) - (snd p))%R)
           (focusS fst ds))
    `+ rho#.

  Definition robust : TraceProp state :=
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      @texists dist_state state
               ([][acc_dist gamma //\\ !(bounded mu rho)]).

  Close Scope LTL_scope.

End Robustness.