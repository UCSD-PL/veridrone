Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import ExtLib.Data.Fun.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import ExtLib.Structures.Applicative.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import SLogic.Logic.
Require Import SLogic.LTLNotation.
Require Import SLogic.Instances.

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

  Definition acc_dist (gamma : R -> R)
  : ActionProp (dist_state * state) :=
    `eq (post fst#ds)
        (pre ((`pair snd#t (`gamma snd#IC)) `:: fst#ds)).

  Definition max_R : list R -> R :=
    fold_right Rmax 0%R.

  Definition flip {A B C} (f : A -> StateVal B C) : StateVal B (A -> C) :=
    fun b a => f a b.

  Definition bounded (mu : R -> R -> R) (rho : R)
  : StateProp (dist_state * state) :=
    snd#OC `<=
    `max_R
    (lift2 (F:=StateVal (dist_state * state))
           (@map (R * R) R)
           (flip (fun p => (`mu (pure (fst p)) (snd#t `- (pure (snd p)))%R)))
           fst#ds)
    `+ `rho.

  Definition robust : TraceProp state :=
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists dist_state , [][acc_dist gamma //\\ !(bounded mu rho)].

End Robustness.