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
Require Import SLogic.BasicProofRules.

Definition strict_increasing_bound
           (f : R -> R) (bound : R) : Prop :=
  forall x y, (bound <= x < y -> f x < f y)%R.

Definition decreasing_bound
           (f : R -> R) (bound : R) : Prop :=
  forall x y, (bound <= x <= y -> f y <= f x)%R.

Definition K_fun (f : R -> R) : Prop :=
  continuity f /\ strict_increasing_bound f R0 /\ f R0 = R0.

(* I couldn't find a definition in the standard library
   for the limit at infinity. *)
Definition limit_pos_inf (f : R -> R) (l : R) : Prop :=
  forall epsilon, (epsilon > 0)%R ->
    exists M, (M > 0)%R /\
      (forall x, x > M -> Rabs (f x - l) < epsilon)%R.

(* This is not the same as the definition of L functions
   from the Tabuada paper. In particular, we only require
   that the function be decreasing, not strictly decreasing.
   I think that if you require the function to be strictly
   decreasing, then there are no KLD functions. Moreover,
   I think that our definition of L function is the
   standard one from control theory. *)
Definition L_fun (f : R -> R) : Prop :=
  continuity f /\ decreasing_bound f R0 /\
  limit_pos_inf f R0.

Definition KL_fun (f : R -> R -> R) : Prop :=
  (forall t, (0 <= t)%R -> K_fun (fun c => f c t)) /\
  (forall c, (0 <= c)%R -> L_fun (fun t => f c t)).

Definition KLD_fun (f : R -> R -> R) : Prop :=
  KL_fun f /\
  forall (c s t : R),
    (0 <= c)%R -> (0 <= s)%R -> (0 <= t)%R ->
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
    (fst#ds)! `=
    !((`pair snd#t (`gamma snd#IC)) `:: fst#ds).

  Definition max_R : list R -> R :=
    fold_right Rmax 0%R.

  Definition flip {A B C} (f : A -> StateVal B C)
    : StateVal B (A -> C) :=
    fun b a => f a b.

  Definition bounded (mu : R -> R -> R) (rho : R)
    : StateProp (dist_state * state) :=
    snd#OC `<=
    `max_R
    (lift2 (@map (R * R) R)
           (flip (fun p =>
                    (`mu (pure (fst p))
                      (snd#t `- (pure (snd p)))%R)))
           fst#ds)
    `+ `rho.

  (* This is the definition of robustness from the
     Tabuada paper. *)
  Definition robust : TraceProp state :=
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists dist_state ,
                 [][acc_dist gamma //\\ !(bounded mu rho)].

  (* Now we write a definition of robustness that is
     equivalent to the Tabuada one, but easier to
     work with. *)

  (* For the equivalent definition of robustness,
     we only need to store a single pair of disturbance
     and time rather than a list of pairs. *)
  Record dist_state2 : Type :=
    { d : R;
      td : R }.

  Definition acc_dist2 (mu : R -> R -> R) (gamma : R -> R)
    : ActionProp (dist_state2 * state) :=
    let prev := `mu (!(fst#d)) (!((snd#t) `- (fst#td))) in
    let new := `mu (`gamma (!(snd#IC))) (pure R0) in
    (new `<= prev -->>
       ((fst#d)! `= prev //\\ (fst#td)! `= !(fst#td))) //\\
    (prev `< new -->>
       ((fst#d)! `= new //\\ (fst#td)! `= !(snd#t))).

  Definition bounded2 (rho : R)
    : StateProp (dist_state2 * state) :=
    snd#OC `<= fst#d `+ `rho.

  Definition robust2 : TraceProp state :=
    Exists gamma : R -> R,   embed (K_fun gamma) //\\
    Exists mu : R -> R -> R, embed (KLD_fun mu)  //\\
    Exists rho : R,          embed (0 <= rho)%R  //\\
      TExists dist_state2 ,
                 [][acc_dist2 mu gamma //\\ !(bounded2 rho)].

  Theorem robust2_robust :
    robust2 -|- robust.
  Proof.
    do 3 (apply lexists_lequiv_m; red; intros;
          apply land_lequiv_m; [ reflexivity | ]).
    split.
    { (*eapply refinement_mapping.
      unfold acc_dist, bounded. rewrite_focus.*)
      admit. }
    { admit. }
  Admitted.

End Robustness.