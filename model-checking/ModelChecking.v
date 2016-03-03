Require Import Coq.Lists.List.
Require Import Coq.Reals.RIneq.
Require Import Coquelicot.Coquelicot.

Section HybridAutomata.

  (* Hybrid automaton definition *)
  Variable vars : Type.
  Definition state := vars -> R.
  Variable mode : Type.

  Record HybridAutomaton : Type :=
    { flow : mode -> state -> (* derivatives *) state -> Prop;
      inv : mode -> state -> Prop;
      init : mode -> state -> Prop;
      jump : mode -> mode -> state -> state -> Prop;
    }.

  Definition trajectory : Type := list (mode * state).

  Definition open_invariant (l r : R) (f : R -> state)
             (inv : state -> Prop) :=
    forall t, (l < t < r)%R -> inv (f t).

  Definition valid_flow (l r : R) (f : R -> state)
             (flow : state -> state -> Prop) :=
    (* We use strict inequalities here because the HyTech paper does. *)
    forall t, l < t < r ->
              exists ds,
                (forall x, is_derive (fun r => f r x) t (ds x)) /\
                flow (f t) ds.

  Inductive step (A : HybridAutomaton)
    : mode -> state -> mode -> state -> Prop :=
  | Jump : forall m m' s s',
      A.(jump) m m' s s' ->
      step A m s m' s'
  | Flow : forall (d : nonnegreal) (f : R -> state)
                  (m : mode),
      open_invariant 0 d f (A.(inv) m) ->
      valid_flow 0 d f (A.(flow) m) ->
      step A m (f R0) m (f d).

  Inductive valid (A : HybridAutomaton) : trajectory -> Prop :=
  | Initial : forall m s, A.(init) m s -> valid A ((m, s) :: nil)
  | Step : forall m s m' s' tr, valid A ((m,s) :: tr) ->
                                step A m s m' s' ->
                                valid A ((m',s') :: (m,s) :: tr).

  Definition ModeStateProp : Type := mode -> state -> Prop.

  Definition reachable (A : HybridAutomaton) : ModeStateProp :=
    fun m s => exists tr, valid A ((m,s) :: tr).

  (* Model checking hybrid automata *)
  Record Post (A : HybridAutomaton) : Type :=
    { next : ModeStateProp -> ModeStateProp;
      correct : forall (P : ModeStateProp) m s m' s',
          P m s -> step A m s m' s' ->
          next P m' s' }.

  Arguments next {_} _ _ _ _.

  Require Import Coq.Program.Equality.
  Lemma model_check_done :
    forall (A : HybridAutomaton) (P : Post A),
      (forall m s, P.(next) A.(init) m s -> A.(init) m s) ->
      forall m s, reachable A m s -> A.(init) m s.
  Proof.
    intros A P Hdone m s Hreach. unfold reachable in Hreach.
    destruct Hreach as [tr Hreach].
    dependent induction Hreach generalizing m s tr.
    { assumption. }
    { eapply Hdone. destruct P as [P HP]. simpl in *.
      eapply HP.
      { eapply IHHreach. reflexivity. }
      { assumption. } }
  Qed.

  Definition nonneg_0 : nonnegreal :=
    mknonnegreal R0 (Rle_refl _).

  Require Import Coq.micromega.Psatz.
  Lemma step_reflexive :
    forall (A : HybridAutomaton) m s,
      step A m s m s.
  Proof.
    intros A m s. pose proof (Flow A nonneg_0 (fun _ => s)) as HFlow.
    simpl in *. apply HFlow.
    { unfold open_invariant. intros. psatzl R. }
    { unfold valid_flow. intros. psatzl R. }
  Qed.

  Lemma post_abstracts :
    forall (A : HybridAutomaton) (P : Post A) (Q : ModeStateProp) m s,
      Q m s -> P.(next) Q m s.
  Proof.
    intros A P Q m s HQ. destruct P as [P HP].
    simpl. eapply HP; eauto. apply step_reflexive.
  Qed.

  Lemma model_check_step :
    forall (A : HybridAutomaton) (P : Post A) (Q : ModeStateProp),
      (forall m s, reachable {| flow:=A.(flow);
                                inv:=A.(inv);
                                init:=P.(next) A.(init);
                                jump:=A.(jump) |} m s -> Q m s) ->
      forall m s, reachable A m s -> Q m s.
  Proof.
    intros A P Q Hstep m s Hreach. apply Hstep. clear Hstep.
    unfold reachable in *. destruct Hreach as [tr Hreach].
    exists tr.
    dependent induction Hreach generalizing m s tr.
    { constructor. simpl.
      apply post_abstracts; assumption. }
    { constructor.
      { apply IHHreach. reflexivity. }
      { inversion H; subst.
        { apply Jump; auto. }
        { apply Flow; auto. } } }
  Qed.

(*
  Definition PostFlow (P : ModeStateProp)
             (flow : mode -> state -> state -> Prop)
             (sol : state -> state -> nonnegreal -> state -> Prop)
             (inv : mode -> state -> Prop) : ModeStateProp :=
    fun m s' =>
      exists (s ds : state) d,
        P m s /\ flow m s ds /\ sol s ds d s' /\ inv m s'.

  Definition PostJump (P : ModeStateProp)
             (jump : mode -> mode -> state -> state -> Prop)
    : ModeStateProp :=
    fun m' s' => exists m s, P m s /\ jump m m' s s'.

  Definition Post (A : HybridAutomaton) (P : ModeStateProp)
    : ModeStateProp :=
    fun m' s' => (exists f, PostFlow P A.(flow) f A.(inv) m' s')
                 \/ PostJump P A.(jump) m' s'.
*)

End HybridAutomata.

(* Thermostat for HyTech paper*)
Inductive var : Type :=
| x : var (* Temperature *)
| y : var (* Global clock *)
| z : var (* Clock capturing time spent in on state *)
.

Inductive mode : Type :=
| on : mode
| off : mode.

Definition Thermostat : HybridAutomaton var mode :=
{| flow := fun m s ds =>
             match m with
             | on => 2 <= ds x <= 4 /\ ds y = 1 /\ ds z = 1
             | off => -3 <= ds x <= -1 /\ ds y = 1 /\ ds z = 0
             end;
   inv := fun m s =>
            match m with
            | on => 1 <= s x <= 3
            | off => 1 <= s x <= 3
            end;
   init := fun m s =>
             match m with
             | on => s x = 2
             | off => False
             end;
   jump := fun m m' s s' =>
             match m, m' with
             | on, off => s x = 3 /\ s' x = s x
             | off, on => s x = 1 /\ s' x = s x
             | _, _ => False
             end;
|}.

