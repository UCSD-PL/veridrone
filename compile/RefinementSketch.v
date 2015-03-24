Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.ProofRules.
Require Import String.
Open Local Scope string_scope.
Open Local Scope HP.

Definition program : Formula :=
  "x" = 0 /\ [] ("x"! = "x").

Lemma program_fact :
  |- (program --> [] "x" = 0).
Proof.
eapply inv_discr_ind.
- simpl; tauto.
- simpl; unfold eval_comp; simpl.
  intros. inversion H.
  rewrite H1. auto.
Qed.

Require Import Embed.
Check embedStep.
Require Import List.
Require Import Strings.String.
Import ListNotations.

Check embedStep.

Definition embed_coq : (state -> state) -> Formula :=
  embedStep string (Syntax.state -> Syntax.state) Syntax.state
            (fun st p st' => st' = p st)%type
            (fun st v => Some (st v))
            [("x","x")] [("x","x")].

Definition prog2 : state -> state :=
  id.

Lemma prog2_refines_prog : 
  |- embed_coq prog2 --> ("x"! = "x").
Proof.
  unfold embedStep, embed_coq.
  simpl.
  intros.
  unfold eval_comp.
  simpl.
  specialize (H (Semantics.hd tr)).
  specialize (H (conj eq_refl I)).
  destruct H.
  destruct H.
  destruct H0.
  unfold prog2, id in H; simpl in H.
  inversion H0.
  subst. auto.
Qed.
  

Lemma prog2_fact :
  |- ("x" = 0 /\ [] (embed_coq prog2)) --> [] "x" = 0.
Proof.
  eapply imp_trans.
  Focus 2.
  apply program_fact.
  unfold program.
  apply and_right.
  apply and_left1.
  compute; tauto.
  apply and_left2.
  apply always_imp.
  apply prog2_refines_prog.
Qed.

(* try conditionals, though embedding coq first
   look at implementing shims in coq and showing
   they are refinements of shims we defined.
   eg. function that flip flops between 0 and 1
   

   define interpreter like in simple.v
   get a handle on refinement proofs
  *)
Require Import RelDec.
Require Import Coq.Reals.Rbase.

Axiom my_req_dec : forall (a b : R),
                     {a = b} + {a <> b}.

Print state.
SearchAbout (Rdefinitions.R -> Rdefinitions.R -> _).

Definition coq_prog3 (st : state) : state :=
  fun (v : Var) =>
    if (v ?[ eq ] "x"%string)
    then
      if (my_req_dec (st "x") 0%R)
      then 1%R
      else 0%R
    else
      st v.

Definition init_prog3 : Formula :=
  "x" = 0 \/ "x" = 1.

Definition tla_prog3 : Formula :=
  init_prog3 /\
  [] (("x" = 0 --> "x"! = 1) /\
      ("x" = 1 --> "x"! = 0)).

Require Import micromega.Psatz.

Lemma prog3_tla_fact :
  |- (tla_prog3 --> [] init_prog3).
Proof.
apply inv_discr_ind.
- simpl. tauto.
- simpl. unfold eval_comp. simpl.
  intros.
  destruct H.
  destruct H.
  + right.
    simpl.
    destruct H0.
    * intuition.
      Admitted.
(*
    * destruct H0.
      rewrite H0 in H.
      assert (1%R = 0%R -> False).
      psatz R. apply H2 in H. elimtype False. auto.
  + left.
    destruct H0.
    * destruct H0.
      rewrite H0 in H.
      assert (0%R = 1%R -> False).
      psatz R. apply H2 in H. elimtype False. auto.
    * intuition.
Qed.
*)

Lemma fun_eq_fact :
  forall {A B : Type} (f g : A -> B),
    f = g ->
    forall (a : A), f a = g a.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma prog3_refines_prog : 
  |- embed_coq coq_prog3 --> 
     ("x" = 0 --> "x"! = 1) /\
     ("x" = 1 --> "x"! = 0).
Proof.
  unfold embed_coq, embedStep.
  simpl. intros.
  unfold eval_comp. simpl.
  specialize (H _ (conj eq_refl I)).
  destruct H as [ ? [ ? ?  ] ].
  unfold coq_prog3 in H.
  apply fun_eq_fact with (a := "x") in H.
  simpl in H.
  destruct H0. clear H1. inversion H0. clear H0.
  rewrite H2 in *.
  destruct (my_req_dec (Semantics.hd tr "x") 0).
  - rewrite e. rewrite H. split; intuition.
  - rewrite H in *. split; auto.
    intro. congruence. 
Qed.

Check embedStep.

(* Next: try embedding a different language
   need an eval and models relation. First for a language that
   directly works on reals.
   Partial state (list Real rather than function to real) - then var is nat.
   Also test a program where two lists are different.
   *)
