Require Import ExtLib.Tactics.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import FunctionalExtensionality.

Axiom float : Type.

Definition state : Type := nat -> float.

Axiom expr : Type.
Axiom exprD : expr -> state -> option float.


Definition update {T} (s : nat -> T) (v : nat) (val : T) : nat -> T :=
  fun x =>
    if v ?[ eq ] x then val else s x.


Inductive cmd :=
| Seq (_ _ : cmd)
| Skip
| Asn (_ : nat) (_ : expr)
| Fail.

Inductive eval : state -> cmd -> state -> Prop :=
| ESkip : forall s, eval s Skip s
| ESeq : forall s s' s'' a b,
    eval s a s' ->
    eval s' b s'' ->
    eval s (Seq a b) s''
| EAsn : forall s v e val,
    exprD e s = Some val ->
    eval s (Asn v e) (update s v val).

Section Hoare.

  Variables (P : state -> Prop) (c : cmd) (Q : state -> Prop).

  Definition HoareProgress : Prop :=
    forall s, P s -> (exists s', eval s c s').

  Definition HoarePreservation : Prop :=
    forall s, P s ->
              forall s', eval s c s' ->
                         Q s'.

  Definition Hoare' : Prop :=
    HoareProgress /\ HoarePreservation.

  Definition Hoare : Prop :=
    forall s, P s ->
              (exists s', eval s c s') /\
              forall s', eval s c s' ->
                         Q s'.

  Theorem Hoare_Hoare' : Hoare <-> Hoare'.
  Proof.
    unfold Hoare, Hoare', HoareProgress, HoarePreservation.
    intros.
    intuition.
    { eapply H in H0. tauto. }
    { eapply H in H0. intuition. }
    { eapply H1 in H2; intuition. }
  Qed.

End Hoare.

Theorem SeqR_preservation : forall a b P Q R,
    HoarePreservation P a Q ->
    HoarePreservation Q b R ->
    HoarePreservation P (Seq a b) R.
Proof.
  unfold HoarePreservation. intros.
  inversion H2; clear H2; subst. eauto.
Qed.

Theorem SeqR_progress : forall a b P Q,
    HoareProgress P a ->
    HoareProgress Q b ->
    HoareProgress P (Seq a b).
Proof.
  unfold HoareProgress. intros.
  eapply H in H1. forward_reason; intuition.
  (** Not provable **)
Abort.

Theorem SeqR : forall a b P Q R,
    Hoare P a Q ->
    Hoare Q b R ->
    Hoare P (Seq a b) R.
Proof.
  unfold Hoare. intros.
  split.
  { eapply H in H1.
    forward_reason.
    specialize (H2 _ H1). eapply H0 in H2.
    forward_reason. eexists; econstructor; eauto. }
  { intros. inversion H2; subst.
    eapply H in H1.
    forward_reason.
    eapply H3 in H6. eapply H0 in H6.
    forward_reason. auto. }
Qed.

Theorem AssR : forall v e (P : state -> Prop),
    (forall st, P st -> exprD e st <> None) ->
    Hoare P (Asn v e)
          (fun st' =>
             exists st : state,
               (forall v', v' <> v -> st v' = st' v') /\
               Some (st' v) = exprD e st /\ P st).
Proof.
  intros. red. intros.
  specialize (H _ H0).
  destruct (exprD e s) eqn:Heq; try congruence.
  split.
  { eexists. econstructor. eauto. }
  { intros. inversion H1; clear H1; subst.
    exists s.
    intuition.
    { unfold update. rewrite rel_dec_neq_false by eauto with typeclass_instances.
      reflexivity. }
    { unfold update. rewrite rel_dec_eq_true by eauto with typeclass_instances.
      auto. } }
Qed.

Theorem AssR_post : forall v e (P : state -> Prop),
    Hoare P (Asn v e)
          (fun st' =>
             exists st : state,
               (forall v', v' <> v -> st v' = st' v') /\
               Some (st' v) = exprD e st /\ P st).
Proof.
  intros. red. intros.
Abort.

Theorem AssR_preservation : forall v e (P : state -> Prop),
    HoarePreservation
      P (Asn v e)
      (fun st' =>
         exists st : state,
           (forall v', v' <> v -> st v' = st' v') /\
           Some (st' v) = exprD e st /\ P st).
Proof.
  intros. red. intros.
  inversion H0; clear H0; subst.
  exists s; split.
  { unfold update. intros.
    rewrite rel_dec_neq_false; eauto with typeclass_instances. }
  { unfold update.
    rewrite rel_dec_eq_true; eauto with typeclass_instances. }
Qed.

Theorem AssR_preservation_pre : forall v e (P : state -> Prop),
    HoarePreservation
      (fun s : state =>
         exists val : float, exprD e s = Some val /\ P (update s v val))
      (Asn v e) P.
Proof.
  red. intros.
  forward_reason.
  inversion H0; clear H0; subst.
  rewrite H in H6. inversion H6; clear H6; subst. assumption.
Qed.

Theorem Fail_preservation : forall P,
    HoarePreservation P Fail (fun _ => False).
Proof.
  red. intros.
  forward_reason.
  inversion H0; clear H0; subst.
Qed.

Theorem Fail_preservation_pre : forall P,
    HoarePreservation (fun _ => True) Fail P.
Proof.
  red. intros.
  forward_reason.
  inversion H0; clear H0; subst.
Qed.


Theorem WeakenR : forall c (P Q R S : state -> Prop),
    (forall st, P st -> Q st) ->
    (forall st, R st -> S st) ->
    Hoare Q c R ->
    Hoare P c S.
Proof.
Admitted.

Theorem WeakenR_preservation : forall c (P Q R S : state -> Prop),
    (forall st, P st -> Q st) ->
    (forall st, R st -> S st) ->
    HoarePreservation Q c R ->
    HoarePreservation P c S.
Proof.
Admitted.


(*
Axiom AssR_pre : forall v e (P : state -> Prop),
    Hoare (fun st => P st /\ exprD e st <> None)
          (Asn v e)
          (fun st' =>
             exists st : state,
               (forall v', v' <> v -> st v' = st' v') /\
               Some (st' v) = exprD e st /\ P st).



Theorem AssR' : forall v e (P : state -> Prop),
    (forall st, P st -> exprD e st <> None) ->
    Hoare P (Asn v e) (fun st' =>
                         exists val,
                           let s := update st' v val in
                           Some (st' v) = exprD e s /\ P s).
Proof.
  intros.
  eapply WeakenR.
  exact (fun _ x => x).
  2: eapply AssR; auto.
  simpl. intros.
  destruct H0. specialize (H x).
  exists (x v).
  intuition. rewrite H0. admit.
  admit.
Qed.
*)

Fixpoint sp_pres (c : cmd) (P : state -> Prop) : state -> Prop :=
  match c with
  | Skip => P
  | Seq a b => sp_pres b (sp_pres a P)
  | Asn v e => fun s' =>
                 (forall st, P st -> exprD e st <> None) ->
                 exists val,
                   let s := update s' v val in
                   Some (s' v) = exprD e s /\ P s
  | Fail => fun _ => False
  end.

Theorem sp_sound_preservation : forall c P,
    HoarePreservation P c (sp_pres c P).
Proof.
  induction c.
  { simpl; intros.
    eapply SeqR_preservation. eapply IHc1.
    eapply IHc2. }
  { simpl. admit. }
  { simpl.
    intros.
    eapply WeakenR_preservation.
    3: eapply AssR_preservation.
    exact (fun _ pf => pf).
    simpl.
    intros.
    destruct H. forward_reason.
    exists (x n).
    cutrewrite (update st n (x n) = x).
    auto. unfold update.
    apply functional_extensionality.
    clear - H.
    intros. consider (n ?[ eq ] x0); subst; auto.
    symmetry; auto. }
  { simpl. intros. eapply Fail_preservation. }
Qed.


(*
(** THIS DOES NOT WORK **)
Fixpoint sp (c : cmd) (P : state -> Prop) : state -> Prop :=
  match c with
  | Skip => P
  | Seq a b => sp b (sp a P)
  | Asn v e => fun s' =>
                 (forall st, P st -> exprD e st <> None) ->
                 exists val,
                   let s := update s' v val in
                   Some (s' v) = exprD e s /\ P s
  | Fail => fun _ => True
  end.

Theorem sp_sound : forall c P,
    Hoare P c (sp c P).
Proof.
  induction c.
  { simpl; intros.
    eapply SeqR. eapply IHc1. eapply IHc2. }
  { simpl. admit. }
  { simpl.
    intros.
    eapply WeakenR.
    3: eapply AssR.
    exact (fun 
    instantiate (1 := fun st => P st /\ (forall st, P st -> exprD e st <> None)).
    simpl.
    firstorder.
      simpl. firstorder. }
*)

Fixpoint wp_pres (c : cmd) (P : state -> Prop) : state -> Prop :=
  match c with
  | Skip => P
  | Seq a b => wp_pres a (wp_pres b P)
  | Asn v e => fun s =>
                 exists val, exprD e s = Some val /\
                             let s' := update s v val in
                             P s'
  | Fail => fun s => True
  end.

Theorem wp_pres_sound : forall c P,
    HoarePreservation (wp_pres c P) c P.
Proof.
  induction c; intros.
  { simpl. eapply SeqR_preservation; eauto. }
  { simpl. admit. }
  { simpl. eapply AssR_preservation_pre. }
  { simpl. eapply Fail_preservation_pre. }
Qed.

Fixpoint wp (c : cmd) (P : state -> Prop) : state -> Prop :=
  match c with
  | Skip => P
  | Seq a b => wp a (wp b P)
  | Asn v e => fun s =>
                 exists val, exprD e s = Some val /\
                             let s' := update s v val in
                             P s'
  | Fail => fun s => False
  end.

Lemma FailR_pre : forall P, Hoare (fun _ => False) Fail P.
Proof.
  simpl. red. inversion 1.
Qed.

Lemma AssR_pre : forall P n e,
  Hoare
     (fun s : state =>
        exists val : float, exprD e s = Some val /\ P (update s n val)) 
     (Asn n e) P.
Proof.
  red; intros.
  forward_reason.
  split.
  { eexists. econstructor. eauto. }
  { intros. inversion H1; clear H1; subst.
    rewrite H6 in *. inversion H; clear H; subst.
    assumption. }
Qed.

Theorem wp_sound : forall c P,
    Hoare (wp c P) c P.
Proof.
  induction c; intros.
  { simpl. eapply SeqR; eauto. }
  { simpl. admit. }
  { simpl. apply AssR_pre. }
  { simpl. eapply FailR_pre. }
Qed.

(** Proposal
 ** - [forall P, wp c P st -> P st'] <---
 ** - [forall P, P st -> sp c P st']
 **)

Eval simpl in fun BAD GOOD =>
    let c := Seq (Asn 0 BAD) (Asn 0 GOOD) in
    (fun st st' =>
       forall P, wp c P st -> P st').

Axiom real : Type.

Definition astate : Type := nat -> real.

Axiom val_real : float -> real -> Prop.

Definition state_astate (s : state) (a : astate) : Prop :=
  forall x, val_real (s x) (a x).

Definition HoareA (P : astate -> Prop) (c : cmd) (Q : astate -> Prop) : Prop :=
  Hoare (fun st => exists ast : astate, state_astate st ast /\ P ast)
        c
        (fun st => exists ast : astate, state_astate st ast /\ Q ast).

Definition HoarePreservationA (P : astate -> Prop) (c : cmd) (Q : astate -> Prop) : Prop :=
  HoarePreservation
    (fun st => exists ast : astate, state_astate st ast /\ P ast)
    c
    (fun st => exists ast : astate, state_astate st ast /\ Q ast).


Definition HoarePreservationA2 (P : astate -> Prop) (c : cmd) (Q : astate -> Prop) : Prop :=
  HoarePreservation
    (fun st => forall ast : astate, state_astate st ast -> P ast)
    c
    (fun st => forall ast : astate, state_astate st ast -> Q ast).

Axiom bound : expr -> (astate -> Prop) * (astate -> real -> Prop).


(*
Axiom bound_sound' : forall e P Q,
    bound e = (P,Q) ->
    forall ast, P ast ->
                (forall st, state_astate st ast ->
                            exists v av,
                              exprD e st = Some v /\
                              val_real v av /\
                              Q av).
*)


Axiom bound_sound : forall e P Q,
    bound e = (P,Q) ->
    forall ast, P ast ->
                (forall st, state_astate st ast ->
                            forall v av,
                              exprD e st = Some v ->
                              val_real v av ->
                              Q ast av).

Lemma FailRA_pre : forall P, HoareA (fun _ => False) Fail P.
Proof.
  simpl. red. red. intros.
  forward_reason. destruct H0.
Qed.

Lemma SeqRA_pre : forall P Q R a b,
    HoareA P a Q ->
    HoareA Q b R ->
    HoareA P (Seq a b) R.
Proof.
  intros. eapply SeqR; eauto.
Qed.

Lemma AssRA_pre : forall (P : astate -> Prop) n e,
  HoareA
    (fun s : astate =>
       let (prem,assn) := bound e in
       prem s /\
       exists (val : real),
         (assn s val /\ P (update s n val)) /\
         (exists (v : float), val_real v val /\
                            (forall st, state_astate st s ->
                                        exists (v : float),
                                          val_real v val /\ exprD e st = Some v)))
     (Asn n e) P.
Proof.
  red; red; intros.
  forward_reason.
  destruct (bound e) eqn:Hbound.
  forward_reason.
  specialize (bound_sound _ _ _ Hbound); clear Hbound; intro.
  specialize (H5 _ H0 _ H).
  split.
  { specialize (H3 _ H).
    destruct (exprD e s) eqn:HexprD; try congruence.
    eexists. econstructor. eauto.
    forward_reason; congruence. }
  { intros.
    inversion H6; clear H6; subst.
    exists (update x n x0). split; auto.
    specialize (H3 _ H). forward_reason.
    rewrite H11 in *. inversion H6; clear H6; subst.
    red. intros.
    unfold update.
    consider (n ?[ eq ] x3); intros; subst; eauto. }
Qed.

Fixpoint wpA (c : cmd) (P : astate -> Prop) : astate -> Prop :=
  match c with
  | Skip => P
  | Seq a b => wpA a (wpA b P)
  | Asn v e => fun s : astate =>
       let (prem,assn) := bound e in
       prem s /\
       exists (val : real),
         (assn s val /\ P (update s v val)) /\
         (exists (v : float), val_real v val /\
                            (forall st, state_astate st s ->
                                        exists (v : float),
                                          val_real v val /\ exprD e st = Some v))
  | Fail => fun s => False
  end.



Theorem wpA_sound : forall c P,
    HoareA (wpA c P) c P.
Proof.
  induction c; intros.
  { simpl. eapply SeqRA_pre; eauto. }
  { simpl. admit. }
  { simpl. apply AssRA_pre. }
  { simpl. eapply FailRA_pre. }
Qed.

Eval simpl in fun BAD =>
    let c := Asn 0 BAD in
    (fun st st' =>
       forall P, wpA c P st -> P st').

Eval simpl in fun BAD GOOD =>
    let c := Seq (Asn 0 BAD) (Asn 0 GOOD) in
    (fun st st' =>
       forall P',
         let P := fun st => exists ast, state_astate st ast /\ P' ast in
         wp c P st -> P st').

Definition holds_on (P : astate -> Prop) (st : state) :=
  exists ast, state_astate st ast /\ P ast.



(* astate = TLA state *)
(* state  = C state *)
Theorem wpA_wp : forall c st st',

    (forall P : astate -> Prop,
        (exists ast, state_astate st ast /\ wpA c P ast) ->
        (exists ast', state_astate st' ast' /\ P ast')) ->
    (* the same as
     * forall P, holds_on (wpA c P) st ->
     *           holds_on P st'
     *)

    (forall P' : astate -> Prop,
        let P := fun st => exists ast, state_astate st ast /\ P' ast in
        wp c P st -> P st')
    (* forall P,
     *   wp c (holds_on P) st -> holds_on P st'
     *).
Proof.
  intros c st st'.
  change ((forall P, holds_on (wpA c P) st -> holds_on P st') ->
          (forall P, wp c (holds_on P) st -> holds_on P st')).
Abort.
Proof.
  red; red; intros.
  forward_reason.
  destruct (bound e) eqn:Hbound.
  forward_reason.
  specialize (bound_sound' _ _ _ Hbound); clear Hbound; intro.
  inversion H0; clear H0; subst.
  specialize (H4 _ H1 _ H).
  forward_reason.
  eexists; split; eauto.
  rewrite H9 in *. inversion H0; clear H0; subst.
  (* Not True *)
Abort.

Lemma AssRA2_preservation_pre : forall (P : astate -> Prop) n e,
  HoarePreservationA2
    (fun s : astate =>
       let (prem,assn) := bound e in
       prem s /\
       forall (val : real),
         (assn val -> P (update s n val)) (* /\
         (exists (v : nat), val_real v val /\
                            (forall st, state_astate st s ->
                                        exists (v : nat),
                                          val_real v val /\ exprD e st = Some v))) *) )
     (Asn n e) P.
Proof.
  red; red; intros.
  inversion H0; clear H0; subst.
  destruct (bound e) eqn:Hbound.
  specialize (bound_sound' _ _ _ Hbound); clear Hbound; intro.
  specialize (fun ast H H' av =>
                H0 ast H _ H' _ av H6).
  (* Not True *)
Abort.


Fixpoint wpA_pres (c : cmd) (P : astate -> Prop) : astate -> Prop :=
  match c with
  | Skip => P
  | Seq a b => wpA_pres a (wpA_pres b P)
  | Asn v e => fun s =>
                 exists (val : real) (cv : nat),
                   val_real cv val /\
                   exprD e s = Some cv /\
                   let s' := update s v val in
                   P s'
  | Fail => fun s => False
  end.
*)
