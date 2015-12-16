Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Rbasic_fun.

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


(* Now some useful properties of these functions. *)

Lemma K_fun_pos :
  forall f, K_fun f ->
            forall r, (0 <= r)%R ->
                      (0 <= f r)%R.
Proof.
  unfold K_fun, strict_increasing_bound. intros.
  destruct H as [? [Hincr HR0]].
  rewrite <- HR0. destruct H0.
  { specialize (Hincr R0 r). psatzl R. }
  { rewrite H0. psatzl R. }
Qed.

Lemma KL_fun_pos :
  forall f, KL_fun f ->
            forall r1 r2,
              (0 <= r1)%R -> (0 <= r2)%R ->
              (0 <= f r1 r2)%R.
Proof.
  unfold KL_fun. intros.
  destruct H as [HK ?].
  specialize (HK r2 H1).
  eapply K_fun_pos in HK; eauto.
Qed.

Lemma KLD_fun_pos :
  forall f, KLD_fun f ->
            forall r1 r2,
              (0 <= r1)%R -> (0 <= r2)%R ->
              (0 <= f r1 r2)%R.
Proof.
  unfold KLD_fun. intros.
  apply KL_fun_pos; tauto.
Qed.
