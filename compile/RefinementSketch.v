Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.ProofRules.
Require Import String.
Local Open Scope string_scope.
Local Open Scope HP.

(*******************************************************************
   In this file, we explore various approaches to embedding programs.
   We discuss how each one falls short of our needs, and end with a summary
   of what our options seem to be for overcoming them.
   TODO add a note to Trello
 ********************************************************************)


(* A simple example of refinement - first, a TLA formula refining another TLA formula *)
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

Require Import List.
Require Import Strings.String.
Import ListNotations.

(* These embedding functions (for embedding a program into TLA) can also be found in
   Embed.v. As we will see below, they all have problems. Of these four, we do not consider
   embedStep_ex, which we already knew to be wrong (by existentially quantifying both initial and final
   states, it treats nondeterminism very unrealistically) *)

Require Import Rdefinitions.

(* lifted from Embed.v *)
Section embedding.

  Variable var : Type.   (** Programming language variables **)
  Variable ast : Type.   (** Programs **)
  Variable state : Type. (** Programming language states **)

  (** The standard evaluation relation for the language **)
  Variable eval : state -> ast -> state -> Prop.

  (** In the TLA state, the variable is represented as the returned real **)
  Variable asReal : state -> var -> option R.

  (** This states that the value in the TLA state is exactly
   ** equal to the value in the program state.
   **)
  Fixpoint models (vars : list (Syntax.Var * var))
           (tla_st : Syntax.state) (st : state) : Prop :=
    match vars with
      | nil => True
      | (v,v') :: vars =>
        (Some (tla_st v) = asReal st v' /\ models vars tla_st st)%type
    end.

  (** This version supports predicated refinement, e.g. we can compile
   **   [x = y /\ x! = 3]
   ** as an [if] statement. The problem with it is that it does not
   ** correctly capture the behavior of non-deterministic programs.
   ** I.e. it has angelic non-determinism which is not realistic.
   **
   **)
  Definition embedStep_ex (vars : list (Syntax.Var * var)) (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state post_state : state,
                      models vars pre init_state /\
                      eval init_state prg post_state /\
                      models vars post post_state)%type.

  (** This embeds with a more demonic form of non-determinism,
   ** which is more realistic in practice. However, it does not enjoy
   ** the same expressivity as TLA because it is required to have a
   ** safe step in all instances where it can be run.
   **)
  Definition embedStep (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      exists post_state : state,
                        eval init_state prg post_state /\
                        models post_vars post post_state)%type.

  (** This the the full (progress & preservation) embedding of programs.
   ** It says both that the program terminates and that the result
   ** has the property
   **)
  Definition embedStep_full (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      (exists post_state : state,
                          eval init_state prg post_state) /\
                      (forall post_state : state,
                          eval init_state prg post_state ->
                          models post_vars post post_state)).

  (** This is a version of embedStep that does not make use of existential quantifiers.
   ** This gives some advantages in terms of being able to embed programs that may
   ** "go wrong", but it still cannot handle nondeterminism appropriately, as we will see.
   **)
  Definition embedStep_noex (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      forall post_state : state,
                        eval init_state prg post_state ->
                        models post_vars post post_state).


  (** This is an improvement over previous versions, as it is able to handle
      both nondeterministic programs and programs that fail. However, it is
      not able to handle programs that fail nondeterministically (i.e.,
      take many paths nondeterministically, at least one of which Fails)
   **)
  Definition embedStep_maybenot (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      models pre_vars pre init_state /\
                      (~(exists post_state : state, eval init_state prg post_state) \/
                        (exists post_state : state, eval init_state prg post_state /\
                                                    models post_vars post post_state)))%type.


  (** Inspired by embedStep_maybenot, I was trying to build one that would work on
      nondeterministically failing programs. However, this version is clearly wrong
      (as it is equivalent to False when trying to embed nondeterministic or failing programs
   **)
  Definition embedStep_allpost (pre_vars post_vars : list (Syntax.Var * var)) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      models pre_vars pre init_state /\
                      forall (post_state : state),
                        eval init_state prg post_state ->
                        models post_vars post post_state)%type.

  (** An attempt to rewrite embedStep_maybenot to add a case for "there exists an invalid post state"
      Does not work because the second OR'd clause doesn't provide enough information
   **)
  Definition embedStep_allpost_maybenot (pre_vars post_vars : list (Syntax.Var * var)) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      models pre_vars pre init_state /\
                      (~(exists post_state : state, eval init_state prg post_state) \/
                        (exists post_state : state, eval init_state prg post_state /\
                                                    ~(models post_vars post post_state)) \/
                        (exists post_state : state, eval init_state prg post_state /\
                                                    forall post_state : state, eval init_state prg post_state ->
                                                                               models post_vars post post_state)))%type.

End embedding.

(* First, we consider embedStep, embedding programs represented as state-transformers
   (written in Gallina) *)
Definition embed_coq : (state -> state) -> Formula :=
  embedStep string (Syntax.state -> Syntax.state) Syntax.state
            (fun st p st' => st' = p st)%type
            (fun st v => Some (st v))
            [("x","x")] [("x","x")].

(* here is a particularly trivial function *)
Definition prog2 : state -> state :=
  id.

(* Showing that we can prove a simple refinement fact *)
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

(* Example of proving an invariant for prog2 *)
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

Require Import RelDec.
Require Import Coq.Reals.Rbase.

(* Next, we move to programs that operate on real numbers.
   We need to add an (axiomatized) decider for the reals, since the one in
   the standard library returns a value that cannot be matched on *)
Axiom my_req_dec : forall (a b : R),
                     {a = b} + {a <> b}.

(* This program "alternates" between 0 and 1.
   We will use this alternating program as something of a running example,
   because it requires slightly more advanced features (e.g. if-then-else) *)
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

(* TLA version of the same program *)
Definition tla_prog3 : Formula :=
  init_prog3 /\
  [] (("x" = 0 --> "x"! = 1) /\
      ("x" = 1 --> "x"! = 0)).

(* When all you have is a hammer... *)
Require Import micromega.Psatz.

(* Correctness of our TLA program for prog3 *)
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
  + left.
    destruct H0.
    intuition.
Qed.

Lemma fun_eq_fact :
  forall {A B : Type} (f g : A -> B),
    f = g ->
    forall (a : A), f a = g a.
Proof.
intros. rewrite H. reflexivity.
Qed.

(* Under this definition of embed, we can indeed prove that coq_prog3
   refines the corresponding TLA program *)
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

Require Import FunctionalExtensionality.

Definition state : Type := nat -> option R.

(* Next, we define an imperative language similar to our source language.
   Like our source language, it has if-then-else but not loops.
   We also include a notion of nondeterministically setting a variable to any
   real value (using Havoc), so that we can explore how well our embedding
   implementations work in the presence of nondeterminism *)

(* Expressions in our language *)
Inductive cexpr :=
| CVar : nat -> cexpr
| CConst : R -> cexpr
| CPlus : cexpr -> cexpr -> cexpr
| CNone : cexpr.

Fixpoint cexprD (cx : cexpr) (st : state) : option R :=
  match cx with
    | CVar n => st n
    | CConst r => Some r
    | CPlus cx1 cx2 =>
      match cexprD cx1 st, cexprD cx2 st with
        | Some res1, Some res2 => Some (res1 + res2)%R
        | _, _ => None
      end
    | CNone => None
  end.

Definition update {T} (s : nat -> T) (v : nat) (val : T) : nat -> T :=
  fun x =>
    if v ?[ eq ] x then val else s x.

(* Language syntax *)
Inductive cmd :=
| Seq (_ _ : cmd)
| Skip
| Asn (_ : nat) (_ : cexpr)
| Ite (_ : cexpr) (_ _ : cmd)
| Havoc (_ : nat)
| Fail.

(* Language (operational) semantics *)
Inductive eval : state -> cmd -> state -> Prop :=
| ESkip : forall s, eval s Skip s
| ESeq : forall s s' s'' a b,
    eval s a s' ->
    eval s' b s'' ->
    eval s (Seq a b) s''
| EAsn : forall s v e val,
    cexprD e s = Some val ->
    eval s (Asn v e) (update s v (Some val))
| EIteTrue :
    forall s s' ex c1 c2,
      cexprD ex s = Some 0%R ->
      eval s c1 s' ->
      eval s (Ite ex c1 c2) s'
| EIteFalse:
    forall s s' ex c1 c2 r,
      cexprD ex s = Some r ->
      r <> 0%R ->
      eval s c2 s' ->
      eval s (Ite ex c1 c2) s'
| EHavoc : forall s v val,
             eval s (Havoc v) (update s v (Some val)).

(* First notion of embedding for our imperative language.
   Uses embedStep *)
Definition embed_cmd : cmd -> Syntax.Formula :=
  embedStep nat cmd state
            eval
            (fun st v => st v)
            [("x",0)] [("x",0)].

(* Very simple program *)
Definition cmd1 : cmd :=
  Asn 0 (CVar 0).

Require Import ExtLib.Tactics.

(* Simple refinement proof for an embedded imperative program *)
Lemma cmd1_refines_prog :
  |- embed_cmd cmd1 --> ("x"! = "x").
Proof.
  unfold embed_cmd, embedStep. simpl.
  intros. unfold eval_comp. simpl.
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  specialize (H (conj eq_refl I)).
  forward_reason.
  inversion H; clear H; subst.
  simpl in H6. inversion H6; clear H6.
  rewrite H2.
  unfold update in H0. simpl in H0.
  inversion H0; clear H0.
  reflexivity.
Qed.

(* Less trivial imperative program, with an if-then-else.
   Implements the same alternating behavior as coq_prog3, hence the name *)
Definition cmd3 : cmd :=
  Ite (CVar 0) (Asn 0 (CConst 1%R)) (Asn 0 (CConst 0%R)).

(* Example of proving a refinement with this notion of embedding imperative programs (embedStep).
 * We are able to prove that cmd3 refines its corresponding TLA program, which is good.
 *)
Lemma cmd3_refines_prog3 :
  |- embed_cmd cmd3 -->
               (("x" = 0 --> "x"! = 1) /\
                ("x" = 1 --> "x"! = 0)).
Proof.
  unfold embed_cmd, embedStep. simpl.
  intros.
  unfold eval_comp. simpl.
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H. destruct H.
  - intuition.
  - forward_reason.
    unfold cmd3 in H.
    inversion H; subst; clear H.
    + simpl in H7.
      inversion H8; subst; clear H8.
      simpl in H5. inversion H5; subst; clear H5.
      inversion H7; subst; clear H7.
      unfold update in H0. simpl in H0.
      split.
      * inversion H0. auto.
      * intro. congruence.
    + simpl in H6. inversion H6; subst; clear H6.
      split.
      * intro. congruence.
      * inversion H9; subst; clear H9.
        intro. unfold update in H0. simpl in H0.
        inversion H0; subst; clear H0.
        simpl in H5. inversion H5; subst; clear H5.
        reflexivity.
Qed.

(* Here, we attempt (and succeed) to prove that Fail (a program that cannot
   take a step; i.e., one which "goes wrong") is a valid refinement
   of tla prog3, which is well-behaved (is the "alternating" program).
   This is bad.

   This shows that embedStep is insufficient for the purposes of our
   abstractor. It is important that programs that "go wrong" not be
   treated as refinements of TLA formulas.
 *)
Lemma fail_refines_prog2 :
  |- embed_cmd Fail -->
                (("x" = 0 --> "x"! = 1) /\
                 ("x" = 1 --> "x"! = 0)).
Proof.
  unfold embed_cmd, embedStep.
  simpl. intros.
  unfold eval_comp; simpl.
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  destruct H.
  - tauto.
  - destruct H. inversion H.
Qed.

(* Having seen that embedStep is not quite what we want, we next turn to embedStep_full,
   Which basically adds an additional conjunct to embedStep. While embedStep captures that
   there exists a valid next state, embedStep_full also stipulates that all states that we could
   step to must be valid. *)
Definition embed_cmd' : cmd -> Syntax.Formula :=
  embedStep_full nat cmd state
            eval
            (fun st v => st v)
            [("x",0)] [("x",0)].

(* embedStep_full shares the same problem as embedStep: that is,
   when we try to treat programs that have no valid transitions (like Fail),
   we derive a contradiction that allows us to show that such programs
   refine anything. This is not the behavior that we want (we want such
   programs to not be valid refinements of anything)

   Here, as before, we are able to prove that Fail refines the alternating TLA program.
   We do not want this to be provable.
 *)
Lemma fail_refines_prog2' :
  |- embed_cmd' Fail -->
                (("x" = 0 --> "x"! = 1) /\
                 ("x" = 1 --> "x"! = 0)).
Proof.
  unfold embed_cmd', embedStep_full.
  simpl. intros.
  unfold eval_comp; simpl.
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  destruct H.
  - tauto.
  - destruct H. inversion H.
Qed.

(* Finally, we define an embedding that uses embedStep_noex.
   By not making use of existential quantifiers, embedStep_noex should avoid
   the contradiction that was at the heart of the previous examples.

   The contradiction, to repeat, is this: to the left of
   the --> arrow we have a contradictory fact; namely,
   embed_cmd' Fail. embed_cmd' requires the existence of a post-state that we
   can step to in the evaluation relation; since there isn't one, we have
   a contradiction so we can prove whatever we want on the right side of the arrow.

   That is to say, we can prove Fail refines anything.
 *)
Definition embed_cmd'' : cmd -> Syntax.Formula :=
  embedStep_noex nat cmd state
            eval
            (fun st v => st v)
            [("x",0)] [("x",0)].

(* Using embedStep_noex, we find that Fail can't be proven to refine things.
   That's good. *)
Lemma fail_refines_prog2'' :
  |- embed_cmd'' Fail -->
                (("x" = 0 --> "x"! = 1) /\
                 ("x" = 1 --> "x"! = 0)).
Proof.
  unfold embedStep_noex, embed_cmd''.
  simpl; intros.
  unfold eval_comp; simpl.
  Abort.

Require Import ExtLib.Data.Option.

Lemma eval_respects_eq :
  forall si sf si' sf' cmd,
    si = si' ->
    sf = sf' ->
    (eval si cmd sf <-> eval si' cmd sf').
Proof.
  intros.
  subst; reflexivity.
Qed.

(* This demonstrates that under embed_cmd''/embedStep_full a valid program does indeed
   refine a TLA program (of which it actually is a refinement)
   This is another promising sanity-check for this notion of embedding. *)
Lemma cmd1_refines_prog'' :
  |- embed_cmd'' cmd1 --> ("x"! = "x").
Proof.
  unfold embed_cmd'', embedStep_noex.
  simpl; intros.
  unfold eval_comp; simpl.
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  specialize (H (conj eq_refl I)).
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  match goal with
    | [H: ?P -> _ |- _] =>
      cut P; [let x := fresh in intro x; specialize (H x) | clear H]
  end.
  forward_reason; inv_all. assumption.
  eapply eval_respects_eq.
  reflexivity. Focus 2.
  econstructor. simpl. reflexivity.
  apply functional_extensionality.
  intros. unfold update.
  rewrite rel_dec_sym.
  destruct (0 ?[eq] x); reflexivity.
  eauto with typeclass_instances.
  eauto with typeclass_instances.
Qed.

(* Here, we have a nondeterministic program that will not in all cases
   be a refinement of the deterministic program represented by the TLA formula.
   However, under embed_cmd''/embedStep_full, we can prove that the refinement holds.

   This is bad and shows that embedStep_noex is not sufficient for our purposes either. *)
Lemma havoc_refines_prog'' :
  |- embed_cmd'' (Havoc 0) --> ("x"! = "x").
Proof.
  unfold embed_cmd'', embedStep_noex.
  simpl; intros.
  unfold eval_comp; simpl.
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  specialize (H (conj eq_refl I)).
  specialize (H (fun v => if v ?[eq] 0 then Some (Semantics.hd tr "x") else None)).
  simpl in H.
  match goal with
    | [H: ?P -> _ |- _] =>
      cut P; [let x := fresh in intro x; specialize (H x) | clear H]
  end.
  forward_reason; inv_all. assumption.
  eapply eval_respects_eq.
  reflexivity. 2: econstructor.
  unfold update.
  apply functional_extensionality; intro.
  rewrite rel_dec_sym by eauto with typeclass_instances.
  destruct (0 ?[ eq ] x); reflexivity.
Qed.

(* So, in conclusion, deterministic programs appear to be embeddable with embedStep_noex,
   but nondeterministic programs are not.

   - One option might be to express (e.g. with SP/WP calculation)  whether a program is embeddable (deterministic).
   - We could also require that the language itself not admit nondeterminism, though this might interact badly
     with certain TLA conventions (e.g. often in TLA an invalid variable is havoc)
   - However, this doesn't help us if we decide we do want to embed nondeterministic programs...

   It could be that this problem is something fundamental about linear temporal logics (of which TLA is one)
   Perhaps a branching-time-based formalism would enable us to handle embedding nondeterministic programs
   in a natural way.

   Another question is whether it might actually be (or if we could make it be) acceptable for nondeterministic
   programs to refine deterministic ones (as in the Havoc examples above). This behavior seems to us right now to be
   troubling, though, and it's not clear how useful refinements of nondeterministic programs would be in this case.
*)

(* Example of an embedding for multiple input variables but single output variable
   We didn't end up using it. *)
Definition embed_cmd2 : cmd -> Syntax.Formula :=
  embedStep nat cmd state
            eval
            (fun st v => st v)
            [("x",0); ("y",1)] [("x",0)].

(* Using embedStep_maybenot *)
Definition embed_cmd''' : cmd -> Syntax.Formula :=
  embedStep_maybenot nat cmd state
            eval
            (fun st v => st v)
            [("x",0)] [("x",0)].

(* Under embedStep_maybenot we cannot prove embedded Fail refines valid programs,
   as desired *)
Lemma fail_refines_prog2''' :
  |- embed_cmd''' Fail -->
                ("x"! = "x").
Proof.
  intros.
  simpl. intros.
  unfold eval_comp. simpl.
  destruct H. destruct H. destruct H.
Abort.

(* We can also prove valid refinements *)
Lemma cmd1_refines_prog''' :
  |- embed_cmd''' cmd1 --> ("x"! = "x").
Proof.
  unfold embed_cmd''', embedStep_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. constructor. simpl. eauto.
  - forward_reason. inversion H0. subst. clear H0.
    simpl in H8. unfold update in H2. simpl in H2.
    congruence.
Qed.

(* And, we cannot prove that nondeterministic programs
   refine deterministic ones *)
Lemma havoc_refines_prog''' :
  |- embed_cmd''' (Havoc 0) --> ("x"! = "x").
Proof.
  unfold embed_cmd''', embedStep_maybenot.
  simpl; intros.
  red; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. econstructor.
  - forward_reason. inversion H0. subst. clear H0.
    unfold update in H2. simpl in H2.
Abort.

Print cmd.
Print cexpr.

Definition prog_havoc_crash : cmd :=
  Seq (Havoc 1) (Ite (CVar 1) (Fail) (Skip)).

(* However, we can prove that a program that nondeterministically crashes
   (prog_havoc_crash) is a refinement of a program that is fully deterministic.
   We want this not to be provable. *)
Lemma havoc_crash_refines_prog''' :
  |- embed_cmd''' prog_havoc_crash --> ("x"! = "x").
Proof.
  unfold embed_cmd''', embedStep_maybenot.
  simpl; intros.
  red; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. econstructor.
    constructor. eapply EIteFalse.
    simpl. unfold update. simpl. reflexivity.
    instantiate (1:=1%R). clear. intro. psatz R.
    constructor.
  - forward_reason.
    inversion H0; subst; simpl; clear H0.
    inversion H9; subst; simpl; clear H9.
    + inversion H11.
    + inversion H7; subst; simpl; clear H7.
      inversion H12; subst; simpl; clear H12.
      simpl in H8. unfold update in H8. simpl in H8.
      inversion H8; subst; simpl; clear H8.
      unfold update in H2; simpl in H2.
      rewrite <- H in H2. inversion H2.
      reflexivity.
Qed.

(* Using embedStep_allpost *)
Definition embed_cmd_4 : cmd -> Syntax.Formula :=
  embedStep_allpost nat cmd state
            eval
            (fun st v => st v)
            [("x",0)] [("x",0)].

(* Under embedStep_allpost we cannot prove embedded Fail refines valid programs,
   as desired *)
Lemma fail_refines_prog2_4 :
  |- embed_cmd_4 Fail -->
                ("x"! = "x").
Proof.
  intros.
  simpl. intros.
  unfold eval_comp. simpl.
  destruct H. destruct H. destruct H.
Abort.

(* We can also prove valid refinements *)
Lemma cmd1_refines_prog2_4 :
  |- embed_cmd_4 cmd1 --> ("x"! = "x").
Proof.
  unfold embed_cmd_4, embedStep_allpost.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  Print EAsn.
  specialize (H0 (update x 0 (Some (Semantics.hd tr "x")))).
  unfold cmd1 in H0.
  assert (eval x (Asn 0 (CVar 0)) (update x 0 (Some (Semantics.hd tr "x")))).
  - apply EAsn. simpl. symmetry. assumption.
  - apply H0 in H2.
    forward_reason. unfold update in H2. simpl in H2.
    congruence.
Qed.


(* However, we _can_ prove that nondeterministic programs refine deterministic ones
   So that rules out this definition *)
Lemma havoc_refines_prog2_4 :
  |- embed_cmd_4 (Havoc 0) --> ("x"! = "x").
Proof.
  unfold embed_cmd_4, embedStep_allpost.
  simpl; intros.
  red; simpl.
  forward_reason.
  edestruct H0.
  econstructor.
  unfold update in H2. simpl in H2. inversion H2.
  rewrite H5. reflexivity.
Qed.

Lemma havoc_crash_refines_prog2_4 :
  |- embed_cmd_4 prog_havoc_crash --> ("x"! = "x").
Proof.
  unfold embed_cmd_4, embedStep_allpost.
  simpl; intros.
  red; simpl.
  forward_reason.
  unfold prog_havoc_crash in H0.
  edestruct H0.
Abort.

(* Using embedStep_allpost_maybenot *)
Definition embed_cmd_5 : cmd -> Syntax.Formula :=
  embedStep_allpost_maybenot nat cmd state
            eval
            (fun st v => st v)
            [("x",0)] [("x",0)].

(* Under embedStep_allpost_maybenot we cannot prove embedded Fail refines valid programs,
   as desired *)
Lemma fail_refines_prog2_5 :
  |- embed_cmd_5 Fail -->
                ("x"! = "x").
Proof.
  intros.
  simpl. intros.
  unfold eval_comp. simpl.
  forward_reason.
  destruct H0.
Abort.

(* However, we are unable to prove valid refinements *)
Lemma cmd1_refines_prog2_5 :
  |- embed_cmd_5 cmd1 --> ("x"! = "x").
Proof.
  unfold embed_cmd_5, embedStep_allpost_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - unfold cmd1 in H0. exfalso. apply H0.
    eexists. econstructor. simpl. rewrite <- H. reflexivity.
  - destruct H0.
    + forward_reason. unfold cmd1 in H0.
      inversion H0; subst; simpl. clear H0.
      simpl in H7. unfold update in H2. simpl in H2.
      rewrite H7 in H.
 inversion H; subst; clear H.
      exfalso. apply H2.
      subst.
Abort.

(* New idea: have eval return an option
   Failing and looping are distinct (plus also nondeterminism)
   We believe that these capture all the pathological behaviors
   that we need to deal with *)

(* Now we will change the definition of our embedding functions so that
   we distinguish between nontermination and failure. *)
Section embedding2.
  Variable var : Type.   (** Programming language variables **)
  Variable ast : Type.   (** Programs **)
  Variable state : Type. (** Programming language states **)

  (** The standard evaluation relation for the language **)
  Variable eval : state -> ast -> option state -> Prop.

  (** In the TLA state, the variable is represented as the returned real **)
  Variable asReal : state -> var -> option R.

  (** This states that the value in the TLA state is exactly
   ** equal to the value in the program state.
   **)
  Fixpoint omodels (vars : list (Syntax.Var * var))
           (tla_st : Syntax.state) (st : state) : Prop :=
    match vars with
      | nil => True
      | (v,v') :: vars =>
        (Some (tla_st v) = asReal st v' /\ omodels vars tla_st st)%type
    end.

  (** Based on embedStep_maybenot, this definition succeeds on all cases except
      (like embedStep_maybenot)
      for programs that fail nondeterministically (i.e.,
      take many paths nondeterministically, at least one of which Fails)
      It isn't quite what we need because it's not really adapted to our new
      semantics. oembedStep_maybenone fixes the problem, it seems.
   **)
  Definition oembedStep_maybenot (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      omodels pre_vars pre init_state /\
                      (~(exists post_state : state, eval init_state prg (Some post_state)) \/
                       (exists post_state : state, eval init_state prg (Some post_state) /\
                                                   omodels post_vars post post_state)))%type.

  (** This version of embed appears to work for all the test cases we have come up
      with so far: it allows valid refinements, but does not permit proving
      refinements of pathological programs (ones that crash and/or exhibit nondeterminism)
      from TLA formulas that do not exhibit these.
      It represents a slight change from oembedStep_maybenot (and, hence, from
      embedStep_maybenot) by taking advantage of the extra information supplied
      by the "optional-final-state" semantics.
   **)
  Definition oembedStep_maybenone (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      omodels pre_vars pre init_state /\
                      ((eval init_state prg None) \/
                       (exists post_state : state, eval init_state prg (Some post_state) /\
                                                   omodels post_vars post post_state)))%type.


  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : state -> Prop) (c : ast) (Q : state -> Prop).

    Definition HoareProgress : Prop :=
      forall s, P s -> exists s', eval s c (Some s').

    Definition HoareSafety : Prop :=
      forall s, P s -> ~ eval s c None.

    Definition HoarePreservation : Prop :=
      forall s, P s ->
                forall s', eval s c (Some s') ->
                           Q s'.

    Definition Hoare' : Prop :=
      (HoareProgress /\ HoareSafety /\ HoarePreservation)%type.

    Definition Hoare : Prop :=
      (forall s, P s ->
                (exists s', eval s c s') /\
                (~ eval s c None) /\
                forall s', eval s c (Some s') ->
                           Q s')%type.

    Theorem Hoare_Hoare' : Hoare <-> Hoare'.
    Proof.
      unfold Hoare, Hoare', HoareProgress, HoareSafety, HoarePreservation.
      intuition; forward_reason; specialize (H s); try (apply H in H0); forward_reason; auto.
      {
        destruct x.
        - eexists. eapply H0.
        - exfalso; auto.
      }
      {
        specialize (H0 s H1). forward_reason.
        eexists. eassumption.
      }
      {
        eapply H2; eassumption.
      }
    Qed.
  End Hoare.
End embedding2.

(* Language syntax (for new language with eval "stepping" to option state) *)
(*
Inductive ocmd :=
| OSeq (_ _ : cmd)
| OSkip
| OAsn (_ : nat) (_ : cexpr)
| OIte (_ : cexpr) (_ _ : cmd)
| OHavoc (_ : nat)
| OFail.
*)

(* Language (operational) semantics (for new language) - no loops still *)
Inductive oeval : state -> cmd -> option state -> Prop :=
| OESkip : forall s, oeval s Skip (Some s)
| OESeqS : forall s s' os'' a b,
    oeval s a (Some s') ->
    oeval s' b os'' ->
    oeval s (Seq a b) os''
| OESeqN : forall s a b,
    oeval s a None ->
    oeval s (Seq a b) None
| OEAsnS : forall s v e val,
    cexprD e s = Some val ->
    oeval s (Asn v e) (Some (update s v (Some val)))
| OEAsnN : forall s v e,
    cexprD e s = None ->
    oeval s (Asn v e) None
| OEIteT :
    forall s os' ex c1 c2,
      cexprD ex s = Some 0%R ->
      oeval s c1 os' ->
      oeval s (Ite ex c1 c2) os'
| OEIteF:
    forall s os' ex c1 c2 r,
      cexprD ex s = Some r ->
      r <> 0%R ->
      oeval s c2 os' ->
      oeval s (Ite ex c1 c2) os'
| OEIteN :
    forall s ex c1 c2,
      cexprD ex s = None ->
      oeval s (Ite ex c1 c2) None
| OEHavoc : forall s v val,
      oeval s (Havoc v) (Some (update s v (Some val)))
| OEFail : forall s, oeval s Fail None
.

(* First notion of embedding for our imperative language
   With new semantics distinguishing failure from looping
   Uses oembedStep_maybenot *)
Definition oembed_cmd : _ -> _ -> cmd -> Syntax.Formula :=
  oembedStep_maybenot nat cmd state
                      oeval
                      (fun st v => st v).

(* Making sure we can still handle deterministic, failing,
   and nondeterministic programs *)

(* We cannot prove Fail is a refinement of a deterministic,
   nonfailing program. Good. *)
Lemma fail_refines_prog2_6 :
  |- oembed_cmd [("x",0)] [("x",0)] Fail -->
                ("x"! = "x").
Proof.
  unfold oembed_cmd, oembedStep_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
Abort.

(* A valid refinement, which is ineed provable. Good. *)
Lemma cmd1_refines_prog2_6 :
  |- oembed_cmd [("x",0)] [("x",0)] cmd1 --> ("x"! = "x").
Proof.
  unfold oembed_cmd, oembedStep_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. constructor.
    simpl. rewrite <- H. reflexivity.
  - forward_reason. inversion H0; subst; simpl; clear H0.
    simpl in H6. unfold update in H2. simpl in H2. inversion H2; clear H2.
    subst. rewrite H6 in H. inversion H. reflexivity.
Qed.

(* Nondeterministic refinements should not be provable.
   They are not. Good. *)
Lemma havoc_refines_prog2_6 :
  |- oembed_cmd [("x",0)] [("x",0)] (Havoc 0) --> ("x"! = "x").
Proof.
  unfold oembed_cmd, oembedStep_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. constructor.
  - forward_reason.
    inversion H0; subst; simpl; clear H0.
    unfold update in H2; simpl in H2.
    inversion H2; subst; simpl.
Abort.

(* Finally, programs that nondeterministically crash.
   Unfortunately, we are still able to prove refinements with
   these that we should not be able to ... *)
Lemma havoc_crash_refines_prog2_6 :
  |- oembed_cmd [("x",0)] [("x",0)] prog_havoc_crash --> ("x"! = "x").
Proof.
  unfold oembed_cmd, oembedStep_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. unfold prog_havoc_crash.
    econstructor.
    + constructor.
    + eapply OEIteF.
      * simpl. unfold update. simpl. reflexivity.
      * instantiate (1:=1%R). intro. psatz R.
      * constructor.
  - forward_reason.
    inversion H0; subst; simpl; clear H0.
    inversion H7; subst; simpl; clear H7.
    inversion H9; subst; simpl; clear H9.
    + inversion H10.
    + inversion H11; subst; simpl; clear H11.
      unfold update in H2. simpl in H2.
      rewrite <- H2 in H. symmetry in H.
      inversion H. reflexivity.
Qed.

(* A second attempt at embedding with our "optional ending-state"
   semantics that distinguishes crashes from loops.
   This attempt makes better use of the additional information. *)
Definition oembed_cmd' : _ -> _ -> cmd -> Syntax.Formula :=
  oembedStep_maybenone nat cmd state
                       oeval
                       (fun st v => st v).

(* With this formulation we are still able to prove
   this simple valid refinement *)
Lemma cmd1_refines_prog2_7 :
  |- oembed_cmd' [("x",0)] [("x",0)] cmd1 --> ("x"! = "x").
Proof.
  unfold oembed_cmd', oembedStep_maybenone.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - inversion H0; subst; clear H0. simpl in H4. congruence.
  - forward_reason.
    inversion H0; subst; clear H0.
    simpl in H6. unfold update in H2; simpl in H2.
    rewrite <- H6 in H2. rewrite <- H in H2.
    inversion H2. reflexivity.
Qed.

(* We are still unable to prove this invalid refinement
   (a crashing program cannot be shown to refine a non-crashing one) *)
Lemma fail_refines_prog2_7 :
  |- oembed_cmd' [("x",0)] [("x",0)] Fail -->
                ("x"! = "x").
Proof.
  unfold oembed_cmd', oembedStep_maybenone.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - inversion H0; subst.
Abort.

(* We also still cannot prove that a nondeterministic program
   refines a deterministic one *)
Lemma havoc_refines_prog2_7 :
  |- oembed_cmd' [("x",0)] [("x",0)] (Havoc 0) --> ("x"! = "x").
Proof.
  unfold oembed_cmd', oembedStep_maybenone.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - inversion H0.
  - forward_reason.
    inversion H0; subst; clear H0.
    unfold update in H2; simpl in H2.
Abort.

(* Let's see if we can deal with the "havoc-crash" case.
   Indeed, this appears to be unprovable, as desired. *)
Lemma havoc_crash_refines_prog2_7 :
  |- oembed_cmd' [("x",0)] [("x",0)] prog_havoc_crash --> ("x"! = "x").
Proof.
  unfold oembed_cmd', oembedStep_maybenone.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - inversion H0; subst; clear H0.
    inversion H5; subst; clear H5.
    inversion H7; subst; clear H7.
    + inversion H8; subst; clear H8.
      simpl in H6. unfold update in H6. simpl in H6.
      inversion H6.
Abort.

Definition prog_inc : cmd :=
  Asn 0 (CPlus (CConst 1) (CVar 0)).

(* As an additional test, let's see if we can prove a refinement
   that should be true about a nondeterministic program *)
Lemma good_nondet_refines_7 :
  |- oembed_cmd' [("x",0)] [("x",0)] prog_inc --> ("x"! > "x").
Proof.
  unfold oembed_cmd', oembedStep_maybenone.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - inversion H0; subst; clear H0. simpl in H4.
    rewrite <- H in H4. congruence.
  - forward_reason.
    inversion H0; subst; clear H0.
    unfold update in H2; simpl in H2.
    inversion H2; subst; clear H2.
    simpl in H6. rewrite <- H in H6.
    inversion H6; subst; clear H6.
    clear. red.
    psatzl R.
Qed.

(* Next: we want to do a WP calculation so that we can build an abstracted
   formula without using embed. Show that "embed version" --> "wp-version" *)

(* We make use of the primitives defined in the Hoare section (within embedding2) above *)

(* "concrete Hoare" - instantiated with what we need for cmd language *)
Definition CHoare := Hoare cmd state oeval.

(* Hoare Sequencing rule *)
Theorem SeqR : forall a b P Q R,
    CHoare P a Q ->
    CHoare Q b R ->
    CHoare P (Seq a b) R.
Proof.
  unfold CHoare, Hoare. intros.
  split; [| split].
  { eapply H in H1. forward_reason.
    destruct x eqn:Hx; try congruence.
    generalize H1. intro H1'.
    apply H3 in H1. apply H0 in H1.
    forward_reason.
    eexists. econstructor. apply H1'. apply H1.
  }
  { intro. inversion H2; subst; clear H2.
    - apply H in H1. forward_reason.
      apply H3 in H6. apply H0 in H6. forward_reason.
      congruence.
    - apply H in H1. forward_reason.
      congruence.
  }
  { intros. inversion H2; subst; clear H2.
    apply H in H1. forward_reason.
    apply H3 in H6. apply H0 in H6. forward_reason.
    auto.
  }
Qed.

(* Hoare Skip rule *)
Theorem SkipR :
  forall P,
    CHoare P Skip P.
Proof.
  intros; red; red.
  intros. split; [|split].
  { eexists. econstructor. }
  { intro. inversion H0. }
  { intros. inversion H0; subst. assumption. }
Qed.

(* Hoare Assignment rule; for use in weakest-precondition calculation *)
Lemma AssR_pre : forall P n e,
  CHoare
     (fun s : state =>
        exists val : R, cexprD e s = Some val /\ P (update s n (Some val)))%type
     (Asn n e) P.
Proof.
  red; red; intros.
  forward_reason.
  split; [|split].
  { eexists. econstructor. eauto. }
  { intro. inversion H1; subst; clear H1. congruence. }
  { intros. inversion H1; clear H1; subst.
    rewrite H4 in H. inversion H; subst; clear H. assumption. }
Qed.

(* Hoare rule for havoc *)
Lemma HavocR_pre :
  forall (P : state -> Prop) (n : nat),
    CHoare
      (fun s : state =>
         forall (val : R), P (update s n (Some val)))
      (Havoc n) P.
Proof.
  red; red; intros.
  split; [|split].
  { exists (Some (update s n (Some 0%R))). constructor. }
  { intro. inversion H0. }
  { intros. inversion H0; subst. apply H. }
Qed.

Print eval.

(* Hoare rule for if-then-else - TODO *)
Lemma IteR_pre :
  forall (P Q : state -> Prop) ex c1 c2,
    (forall s, P s -> exists (r : R), cexprD ex s = Some r)%type ->
    CHoare
      (fun s => cexprD ex s = Some 0%R /\ P s)%type
      c1 Q ->
    CHoare
      (fun s => exists (r : R), r <> 0%R /\ cexprD ex s = Some r /\ P s)%type
      c2 Q ->
    CHoare P (Ite ex c1 c2) Q.
Proof.
  intros. unfold CHoare, Hoare in *.
  intros.
  split; [|split].
  { destruct (cexprD ex s) eqn:HcexprD.
    - destruct (my_req_dec r 0).
      + rewrite e in HcexprD. specialize (H0 s (conj HcexprD H2)).
        forward_reason. eexists. apply OEIteT; eauto.
      + specialize (H1 s).
        forward_reason. eexists. eapply OEIteF; eauto.
    - eexists. apply OEIteN. assumption. }
  { intro.
    inversion H3; subst; clear H3.
    - specialize (H0 s (conj H9 H2)).
      forward_reason. auto.
    - specialize (H1 s).
      forward_reason. auto.
    - specialize (H _ H2). inversion H. congruence. }
  { intros.
    inversion H3; subst; clear H3.
    - specialize (H0 s (conj H9 H2)).
      forward_reason. auto.
    - specialize (H1 s).
      forward_reason. auto. }
Qed.

(* Hoare rule for Fail; for use in weakest-precondition calculation *)
Lemma FailR_pre : forall P, CHoare (fun _ => False) Fail P.
Proof.
  simpl. red. inversion 1.
Qed.

Lemma conseqR :
  forall (P P' Q Q' : state -> Prop) c,
    (forall st, P  st -> P' st) ->
    (forall st, Q' st -> Q  st) ->
    CHoare P' c Q' ->
    CHoare P  c Q.
Proof.
  intros.
  unfold CHoare, Hoare in *.
  intros.
  edestruct H1; eauto.
  forward_reason.
  split; eauto.
Qed.

Lemma IteR_pre' :
  forall P Q Q' ex c1 c2,
    CHoare Q  c1 P ->
    CHoare Q' c2 P ->
    CHoare
      (fun s =>
         (cexprD ex s = Some 0%R /\ Q s) \/
         (exists (r : R), r <> 0%R /\ cexprD ex s = Some r /\ Q' s))%type
      (Ite ex c1 c2) P.
Proof.
  intros.
  apply IteR_pre.
  - intros. destruct H1; forward_reason; eexists; eassumption.
  - eapply conseqR; try eassumption; eauto.
    intros. forward_reason.
    destruct H2.
    + tauto.
    + forward_reason. congruence.
  - eapply conseqR; try eassumption; eauto.
    intros. forward_reason.
    destruct H3.
    + forward_reason. congruence.
    + forward_reason. assumption.
Qed.

(* Weakest-precondition calcluation function *)
Fixpoint wp (c : cmd) (P : state -> Prop) : state -> Prop :=
  match c with
  | Skip => P
  | Seq c1 c2 => wp c1 (wp c2 P)
  | Asn v e => (fun s =>
                 exists val, cexprD e s = Some val /\
                             let s' := update s v (Some val) in
                             P s')%type
  | Fail => fun s => False
  | Havoc v => (fun s =>
                  forall val, let s' := update s v (Some val) in
                              P s')%type
  | Ite ex c1 c2 => (fun s =>
                       (cexprD ex s = Some 0%R /\ wp c1 P s) \/
                       (exists (r : R), r <> 0%R /\ cexprD ex s = Some r /\ wp c2 P s))%type
  end.

Theorem wp_sound :
  forall c P,
    CHoare (wp c P) c P.
Proof.
  induction c; intros.
  { eapply SeqR; eauto. }
  { apply SkipR. }
  { apply AssR_pre. }
  { eapply IteR_pre'; eauto. }
  { eapply HavocR_pre. }
  { apply FailR_pre. }
Qed.

(* Function for embedding Coq relations into TLA *)
Definition embed_coq_rel : _ -> _ -> (state -> option state -> Prop) -> Syntax.Formula :=
  oembedStep_maybenone nat (state -> option state -> Prop) state
                       (fun st p st' => p st st')%type
                       (fun st v => st v).


(* The correctness lemma that we ultimately want to prove will look
   something like this *)
Lemma hoare_embed :
  forall P c Q vs1 vs2,
    CHoare P c Q ->
    (|- oembed_cmd' vs1 vs2 c -->
                    embed_coq_rel vs1 vs2
                    (fun x y => P x ->
                                (exists y', y = Some y' /\ Q y'))%type).
Proof.
  intros.
  red; simpl.
  intros. forward_reason.
  exists x.
  split; auto.
  destruct H1.
  - left. intros.
    unfold CHoare, Hoare in H.
    specialize (H _ H2). forward_reason.
    contradiction.
  - right. forward_reason.
    exists x0. unfold CHoare, Hoare in H. split.
    + intros.
      specialize (H _ H3). forward_reason.
      eexists. split; try reflexivity.
      auto.
    + assumption.
Qed.

(***********************************************************************)
(* Next, we repeat this process for a language that operates on floats *)
(***********************************************************************)
Require Import source.

Definition statef : Type := Var -> option float.

Inductive fexpr :=
| FVar : Var -> fexpr
| FConst : source.float -> fexpr
| FPlus : fexpr -> fexpr -> fexpr
. (* TODO do we need FNone? *)

Definition fplus : source.float -> source.float -> source.float :=
  Fappli_IEEE.Bplus custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Fixpoint fexprD (fx : fexpr) (sf : statef) : option source.float :=
  match fx with
    | FVar s        => sf s
    | FConst f      => Some f
    | FPlus fx1 fx2 =>
      match fexprD fx1 sf, fexprD fx2 sf with
        | Some f1, Some f2 => Some (fplus f1 f2)
        | _, _             => None
      end
  end.

Inductive fcmd : Type :=
| FSeq   : fcmd -> fcmd -> fcmd
| FSkip  : fcmd
| FAsn   : Var -> fexpr -> fcmd
| FIte   : fexpr -> fcmd -> fcmd -> fcmd
| FHavoc : Var -> fcmd
| FFail  : fcmd
.

Print update.

Definition fupdate {T : Type} (s : Var -> T) (v : Var) (val : T) : Var -> T :=
  fun x =>
    if v ?[eq] x then val else s x.

Definition fzero := Eval compute in (nat_to_float 0).

Inductive feval : statef -> fcmd -> option statef -> Prop :=
| FESkip : forall s, feval s FSkip (Some s)
| FESeqS : forall s s' os'' a b,
    feval s a (Some s') ->
    feval s' b os'' ->
    feval s (FSeq a b) os''
| FESeqN : forall s a b,
    feval s a None ->
    feval s (FSeq a b) None
| FEAsnS : forall s v e val,
    fexprD e s = Some val ->
    feval s (FAsn v e) (Some (fupdate s v (Some val)))
| FEAsnN : forall s v e,
    fexprD e s = None ->
    feval s (FAsn v e) None
| FEIteT :
    forall s os' ex c1 c2,
      fexprD ex s = Some fzero ->
      feval s c1 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteF:
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      f <> fzero ->
      feval s c2 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteN :
    forall s ex c1 c2,
      fexprD ex s = None ->
      feval s (FIte ex c1 c2) None
| FEHavoc : forall s v val,
      feval s (FHavoc v) (Some (fupdate s v (Some val)))
| FEFail : forall s, feval s FFail None
.

(* TODO wrap FloatToR *)

Locate FloatToR.

Print float.
Print Fappli_IEEE.binary_float.
Check Fappli_IEEE.B754_finite.

Definition F2OR (f : float) : option R :=
  match f with
    | Fappli_IEEE.B754_zero   _       => Some (FloatToR f)
    | Fappli_IEEE.B754_finite _ _ _ _ => Some (FloatToR f)
    | _                               => None
  end.

(* TODO side condition: output variables should be subset of
   input variables *)

(* Hoare instantiated with what we need for fcmd language *)
Definition stater : Type := Var -> option R.

(* Convert a float state to a real state *)
(* TODO make this also take a var map? *)
Definition realify_state (sf : statef) : stater :=
  (fun (v : Var) =>
     match (sf v) with
       | Some f => F2OR f
       | None   => None
     end)%type.

(* Embedding function for our new language *)
Definition oembed_fcmd : _ -> _ -> fcmd -> Syntax.Formula :=
  oembedStep_maybenone Var fcmd statef
                       feval
                       (fun st v => realify_state st v).


Definition real_float (r : R) (f : float): Prop :=
  (F2OR f = Some r)%type.

Definition stater_statef (s : stater) (a : statef) : Prop :=
  forall x, match s x, a x with
              | Some sx, Some ax => real_float sx ax
              | None, None       => True
              | _, _             => False
            end.

(*
(* TODO: do I have the variable correspondence right *)
Fixpoint stater_statef
           (vs : list (Var * Var)) (s : stater) (a : statef) : Prop :=
  match vs with
    | nil             => True
    | (lv, rv) :: vs' =>
      match s rv, a rv with
        | Some srv, Some arv => real_float srv arv
        | None, None       => True
        | _, _             => False
      end
  end.
*)

(* analogous definition to oembedStep_maybenone *)

(* TODO: ivs vs ovs?? *)
Definition reval (rst : stater) (c : fcmd) (rst' : option stater) : Prop :=
  (exists (fst : statef),
    stater_statef rst fst /\
    ((feval fst c None /\ rst' = None) \/
     (exists (rst'' : stater),
        rst' = Some rst'' /\
        (exists (fst' : statef),
           stater_statef rst'' fst' /\
           feval fst c (Some fst')))))%type.

(* "Concrete Hoare" for floating-point language *)
Definition FHoare (ivs ovs : list (Var * Var)) :=
  Hoare fcmd stater (reval ).

(* Embedding *)
Definition oembed_fcmdr (ivs ovs : list (Var * Var)) : fcmd -> Syntax.Formula :=
  oembedStep_maybenone Var fcmd stater
                       (reval)
                       (fun st v => st v) ivs ovs.

(* Check to ensure that output variables are
   subset of input variables *)
(*Definition var_spec_valid (ivs ovs : list (Var * Var)) : Prop :=
  forall (iv : (Var * Var)),
    (In iv ivs -> In iv ovs).*)

(* Useful auxiliary lemma for proving correspondences
   between float and real states when used with models *)

Lemma omodels_real_float :
      forall (vs : list (Var * Var))
             (st1 : Syntax.state) (st2 : statef),
        omodels Var statef
                (fun (st : statef) (v : Var) =>
                   realify_state st v) vs st1 st2 ->
        omodels Var stater
                (fun (st : stater) (v : Var) => st v)
                vs st1 (realify_state st2).
Proof.
  intros.
  induction vs.
  - simpl. trivial.
  - simpl. destruct a.
    split.
    + simpl in H. forward_reason. assumption.
    + apply IHvs. simpl in H.
      forward_reason. assumption.
Qed.

Print statef.

(* Predicate for whether a float state
   contains any invalid values *)
Definition statef_valid (sf : statef) : Prop :=
  forall (v : Var) (f : float) (r : R),
    sf v = Some f -> F2OR f = Some r.

Lemma realify_stater_statef :
  forall (sf : statef),
    statef_valid sf ->
    stater_statef (realify_state sf) sf.
Proof.
  unfold stater_statef, realify_state.
  intros.
  destruct (sf x) eqn:Hsfx; try constructor.
  destruct (F2OR f) eqn:Horf.
  - unfold real_float. unfold F2OR in Horf.
    destruct f; simpl in *; try congruence.
  - unfold F2OR in Horf.
    unfold statef_valid in H.
    destruct f; simpl in *; try congruence.
    + apply H with (r:=0%R) in Hsfx.
      inversion Hsfx.
    + eapply H with (r:=0%R) in Hsfx.
      inversion Hsfx.
Qed.


(* Another auxiliary lemma - probably not true in general *)
Lemma realify_eval_None :
  forall x c,
    feval x c None -> reval (realify_state x) c None.
Proof.
Abort.
(*
  intros.
  unfold reval, realify_state.
  inversion H; subst; clear H.
  { exists x. split.
    - unfold stater_statef.
      intros.
      destruct (x x0) eqn:Hxx0.
      + destruct (F2OR f) eqn:Ff.
        * unfold real_float. assumption.
        *
  simpl.
  unfold realify_state.
  inversion H; subst; clear H.
  - Print reval.
  econstructor.
  unfold realify_state.


  SearchAbout realify_state.
  intros.
  inversion H; subst; simpl; clear H.
  - econstructor.
Abort.
*)
(*  H1 : feval x c None
  ============================
   reval (realify_state x) c None*)

(* I think we want the first element but not 100% sure *)
Fixpoint syn_state_to_stater (vs : list (Var * Var)) (ss : Syntax.state) : stater :=
  match vs with
    | nil             => fun _ => None
    | (lv, rv) :: vs' => (fun (x : Var) =>
                           if x ?[eq] rv then Some (ss lv)
                           else syn_state_to_stater vs' ss x)
  end.



Definition syn_state_stater (vs : list (Var * Var)) (ss : Syntax.state) (sr : stater) : Prop :=
  (syn_state_to_stater vs ss = sr)%type.

Definition syn_state_statef (vs : list (Var * Var)) (ss : Syntax.state) (sf : statef) : Prop :=
  forall (lv rv : Var),
    In (lv,rv) vs ->
    exists (f : float),
      (sf rv   = Some f /\
       F2OR f  = Some (ss lv))%type.

(* (* old cumbersome definition *)
  match vs with
    | nil             =>
      (forall (x : Var), sf x = None)%type
    | (lv, rv) :: vs' =>
      (forall (x : Var),
         if x ?[eq] rv then
           exists f, sf lv = Some f /\
                     Some (ss lv) = F2OR f
         else syn_state_statef vs' ss sf)%type
  end.
*)


Lemma ss_sf_test :
  syn_state_statef [("x", "x")]
                   (fun _ => 3)%R
                   (fun _ => Some (nat_to_float 3)).
Proof.
  intros.
  unfold syn_state_statef.
  intros. exists (nat_to_float 3).
  inversion H; subst; clear H.
  - inversion H0; subst; clear H0.
    split.
    + reflexivity.
    + admit.
  - inversion H0.
Qed.

(* More aggressive forward reasoning tactic *)
Ltac fwd :=
  forward_reason;
  repeat (match goal with
            | |- let '(_) := ?x in _ => consider x
          end).

(* Validity of input spec
   (does not relate a single program variable
    to multiple TLA variables) *)
Fixpoint ispec_valid (ivs : list (Var * Var)) : Prop :=
  match ivs with
    | nil              => True
    | (lv, rv) :: ivs' =>
      (Forall (fun v' => let '(_, rv') := v' in rv' <> rv) ivs' /\
       ispec_valid ivs')%type
  end.

(* Validity of output spec
   (does not relate a single TLA variable
    to multiple program variables)
   (TODO: make sure this truly is what we want.) *)
Fixpoint ospec_valid (ovs : list (Var * Var)) : Prop :=
  match ovs with
    | nil => True
    | (lv, rv) :: ovs' =>
      (Forall (fun v' => let '(lv', _) := v' in lv' <> lv) ovs' /\
       ospec_valid ovs')%type
  end.

(* Combine both *) (* WARNING THIS IS WRONG!!!!! *)
Definition var_spec_valid (ivs ovs : list (Var * Var)) :=
  (ispec_valid ivs /\ ospec_valid ovs)%type.

(* Useful auxiliary lemma; sanity for relationship between
   omodels and syn_state_to_stater (provided valid var-map) *)
Lemma omodels_syn_state_to_stater:
  forall (ss : Syntax.state) (ivs : list (Var * Var)),
    ispec_valid ivs ->
    omodels Var stater
            (fun (st : stater) (v : Var) => st v) ivs
            ss (syn_state_to_stater ivs ss).
Proof.
  intros ss ivs. generalize dependent ss.
  induction ivs.
  { simpl. auto. }
  { intros. simpl.
    destruct a eqn:Ha.
    split.
    - consider (v0 ?[eq] v0).
      + intro; reflexivity.
      + intro; congruence.
    - simpl in H. forward_reason.
      generalize (Forall_forall); intro Hfafa.
      apply Hfafa with (x := (v,v0)) in H.
      + congruence.
Abort.
(*      + constructor; reflexivity. }
Qed.*)

(*
Lemma feval_emptying :
  forall (c : fcmd) (sf : statef) (s' : option statef),
    feval sf c s' ->
    feval (fun _ => None) c s' \/ feval (fun _ => None) c None.
Proof.
  intro c. induction c.
  { intros.
    inversion H; subst; simpl; clear H.
    - apply IHc1 in H3. apply IHc2 in H5.
      destruct H3; destruct H5.
      + left. eapply FESeqS.
        * eauto.
        *
*)
(*
  intro c. induction c; intros; simpl.
  { inversion H; subst; simpl; clear H.
    -  apply IHc2 in H5. eapply FESeqS.

    - inversion H3; subst; simpl; clear H3.
      + apply FESeqS with (s' := (fun _ => None)).
        * constructor.
        * apply IHc2 in H5. auto.
      + eapply FESeqS.
*)

(* A couple of useful definitions for the correctness
   sub-lemmas that follow *)
Definition sf_subset_present (sub super : statef) : Prop :=
  forall (v : Var),
    super v = None -> sub v = None.

Lemma empty_fstate_subset :
  forall (sf : statef),
    sf_subset_present (fun _ => None) sf.
Proof.
  intros. unfold sf_subset_present.
  intros. auto.
Qed.

(* general form of a fact I need about crashing
   behavior and empty variable environments
   (want to prove that if a program crashes in any
    state it will crash in the empty state) *)
Lemma feval_crash_subset :
  forall (c : fcmd) (sf sf' : statef),
    feval sf  c None ->
    sf_subset_present sf' sf ->
    feval sf' c None.
Proof.
  intro c.
  induction c.
  { intros.
    inversion H; subst; clear H.
    - eapply FESeqS. eapply IHc2 in H6.
Abort.

Lemma feval_empty_crash :
  forall (c : fcmd) (sf : statef),
    feval sf c None ->
    feval (fun _ => None) c None.
Proof.
  intro c. induction c.
  { intros.
    inversion H; subst; clear H.
    - apply IHc2 in H5.
      econstructor 2.
Abort.

(* I worry about the provability of this... *)
Lemma omodels_crash :
    forall (c : fcmd) (ivs : list (Var * Var)) (sf : statef)
           (ss : Syntax.state),
      ispec_valid ivs ->
      omodels Var statef
              (fun (st : statef) (v : Var) => realify_state st v)
              ivs ss sf ->
      feval sf c None ->
      reval (syn_state_to_stater ivs ss) c None.
Proof.
  intros c ivs. generalize dependent c.
  induction ivs.
  - intros. simpl in *. unfold reval.
    exists (fun _ => None). split.
    + unfold stater_statef. intro. auto.
    + left.
      split; try reflexivity.

(* idea: c _can_ crash on an input,
               so it will crash on the "all-None" input *)

      admit.
  - intros. simpl. destruct a.
    simpl in H. forward_reason.
    generalize Forall_forall; intro Hfafa.
    apply Hfafa with (x := (v,v0)) in H.
    + congruence.
    + Abort. (*constructor. reflexivity.
Qed.*)

(*
  intros.
  unfold reval.
  exists sf. split.
  - unfold stater_statef. intros.
    consider (sf x); intros.
    + consider (syn_state_to_stater ivs ss x); intros.
      * unfold syn_state_to_stater in H3.


  intro c. induction c.
  - intros. forward_reason.
    inversion H1; subst; clear H1.
    + unfold reval. exists

specialize (IHc2 ivs sf ss H H0 H7).
*)
  (*
  intros c ivs. generalize dependent c.
  induction ivs.
  - intros.
    simpl. unfold reval. exists sf.
    simpl in *.
    split.
    + simpl in H. unfold stater_statef.
      intro x.
      destruct (sf x).
   *)

(* We need more lemmas for the other admits in the main theorem,
   but I worry that not all of them are true.*)

(*  intro c.
  induction c.
  { intros.
    unfold reval. exists sf.
    split.
    - unfold stater_statef. intros x.

    inversion H0; subst; clear H0.
    - unfold reval. exists sf.
    split.
    - unfold stater_statef. intros x.
      destruct (sf x) eqn:Hsfx.



  unfold reval.
  exists sf.
  split.
  - unfold stater_statef.
    intro.
    destruct (sf x) eqn:Hsfx.
    +


  - left. split; auto.
Qed.
*)

(* We must prove that "abstract" evaluation (over reals)
   refines "concrete" evaluation (over floats) *)
(* THIS is one of our core correctness proofs
   (along with correctness of WP) *)
(* validity: no duplicates in appropriate components
   TODO: separate "covariant" and "contravariant"
   versions of our functions for transforming state types?
   no; just that we need to have all of them take a var list
*)
Lemma fcmd_rembed_refined_fembed :
  forall (c : fcmd) (ivs ovs : list (Var * Var)),
    var_spec_valid ivs ovs ->
    (|- (oembed_fcmd ivs ovs c) --> (oembed_fcmdr ivs ovs c)).
Proof.
(*  intros. simpl. intros.
  fwd.
  Print reval.
  exists (syn_state_to_stater ivs (Semantics.hd tr)).
  split.
  { unfold var_spec_valid in H; forward_reason.
    eapply omodels_syn_state_to_stater in H.
    eapply H. }
  { destruct H1.
    - left. eapply omodels_crash; eauto.
      + red in H. forward_reason. assumption.
    - right. forward_reason.
      exists (realify_state x0). split.
      + red.
        exists x. split. (* need syn_state_to_statef *)
        {
          (* omodels should require input state to correspond "tightly" *)
          assert (forall (v : (Var * Var)), x (snd v) = None <-> ~ In v ivs).
          admit.
          clear -H0 H3.
          induction ivs.
          { simpl in *. red. intro.
            specialize (H3 ("", x0)). simpl in H3.
            consider (x x0); intros.
            - cut (~ False); [| tauto]. intro.
              apply H3 in H1. congruence.
            - constructor. }
          { simpl.
            simpl in *. destruct a.
            unfold stater_statef.
            intros. consider (x0 ?[eq] v0).
            - intros. subst. forward_reason.
              unfold realify_state in H.
              destruct (x v0).
              + unfold real_float. auto.
              + congruence.
            - intros.
              specialize (IHivs (proj2 H0)).
              unfold stater_statef in IHivs.
              admit. (* need to strengthen inductive hyp *)
              (*
              specialize (IHivs x0).
              apply IHivs.*) } }
        { right.
          eexists. split.
          - reflexivity.
          - exists x0. split; eauto.
            Print realify_state.
            Print stater_statef.
            Print reval.
            Print stater_statef.
            Print feval.
            Print real_float.
            admit. }
      + clear -H2.
        induction ovs.
        { simpl. constructor. }
        { simpl. destruct a. simpl in H2.
          forward_reason. split.
          - assumption.
          - assumption. }}*)
Abort.

(* Another way of approaching abstract evaluation *)
Definition vmodels (vs : list (Var * Var)) (ss : Syntax.state) (sf : statef) : Prop :=
  omodels Var statef (fun (st : statef) (v : Var) => realify_state st v) vs ss sf.

(** This is the semantic side condition **)
Definition SEMR (vs : list (Var * Var)) (P : Syntax.state -> Prop) : Prop :=
  forall c a b, vmodels vs a c -> vmodels vs b c -> P a -> P b.

Definition Hoare_ := Hoare fcmd statef feval.


Definition HoareA_all (ivs ovs : list (Var * Var))
           (P : Syntax.state -> Prop) (c : fcmd) (Q : Syntax.state -> Prop)
: Prop :=
  Hoare_ (fun fst => forall rst : Syntax.state, vmodels ivs rst fst -> P rst)%type
         c
         (fun fst => forall rst : Syntax.state, vmodels ovs rst fst -> Q rst)%type.

Definition HoareA_ex (ivs ovs : list (Var * Var))
           (P : Syntax.state -> Prop) (c : fcmd) (Q : Syntax.state -> Prop)
: Prop :=
  Hoare_ (fun fst => exists rst : Syntax.state, vmodels ivs rst fst /\ P rst)%type
         c
         (fun fst => exists rst : Syntax.state, vmodels ovs rst fst /\ Q rst)%type.

Lemma HoareA_all_embed :
  forall P c Q vs1 vs2,
    HoareA_all vs1 vs2 P c Q ->
    SEMR vs1 P ->
    (|- oembed_fcmd vs1 vs2 c -->
                    Embed (fun st st' => P st -> Q st')).
Proof.
  unfold HoareA_all, Hoare. simpl; intros.
  forward_reason.
  destruct (H x); clear H.
  { intros. eapply H0. 2: eassumption. 2: eassumption. eassumption. }
  { forward_reason. destruct H3.
    { exfalso; auto. }
    { forward_reason.
      eapply H5 in H3; eauto. } }
Qed.

Lemma HoareA_embed_ex :
  forall P c Q vs1 vs2,
    HoareA_ex vs1 vs2 P c Q ->
    forall (HsemrQ : SEMR vs2 Q),
    (|- oembed_fcmd vs1 vs2 c -->
                    Embed (fun st st' => P st -> Q st')).
Proof.
  unfold HoareA_ex, Hoare_. simpl; intros.
  forward_reason.
  destruct (H x); clear H.
  { eexists; eauto. }
  { forward_reason. destruct H2; try solve [ exfalso; auto ].
    forward_reason.
    eapply H4 in H2.
    forward_reason.
    eapply HsemrQ; [ | | eassumption ]; eauto. }
Qed.

Lemma Hoare__skip :
  forall P,
    Hoare_ P FSkip P.
Proof.
  red. red. intros.
  split.
  { eexists; constructor. }
  split.
  { intro. inversion H0. }
  { inversion 1. subst; auto. }
Qed.

Lemma Hoare__seq :
  forall P Q R c1 c2,
    Hoare_ P c1 Q ->
    Hoare_ Q c2 R ->
    Hoare_ P (FSeq c1 c2) R.
Proof.
  unfold Hoare_, Hoare.
  intros.
  split.
  { eapply H in H1.
    forward_reason.
    destruct x; try solve [ exfalso; auto ].
    specialize (H0 _ (H3 _ H1)).
    forward_reason.
    eexists. econstructor; eauto. }
  split.
  { red. eapply H in H1.
    forward_reason.
    inversion 1; subst; auto.
    specialize (H0 _ (H3 _ H8)).
    forward_reason. eauto. }
  { intros.
    inversion H2; clear H2; subst.
    eapply H in H1. forward_reason.
    eapply H3 in H6.
    eapply H0 in H6. forward_reason. eauto. }
Qed.

Print fcmd.

Check Hoare_.
Print fexprD.

SearchAbout statef.

(* this plus consequence should be enough to get our real assignment rule
   that talks about bounds *)
Lemma Hoare__asn :
  forall P v e,
    Hoare_
      (fun fs : statef =>
         exists val : float,
           fexprD e fs = Some val /\
           P (fupdate fs v (Some val)))%type
      (FAsn v e)
      P.
Proof.
  intros. red. red.
  intros. fwd.
  split.
  - eexists. constructor. eassumption.
  - split.
    + intro. inversion H1; subst; clear H1. congruence.
    + intros. inversion H1; subst; clear H1.
      rewrite H in H4. inversion H4; subst; clear H4.
      assumption.
Qed.



Require Import bound.

(* Calculating bounds for expressions *)
Fixpoint fexpr_to_NowTerm (fx : fexpr) : NowTerm :=
  match fx with
    | FVar v   => VarNowN v
    | FConst f => FloatN f
    | FPlus fx1 fx2 =>
      PlusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
  end.

Definition bound_fexpr (fx : fexpr) : list singleBoundTerm :=
  bound_term (fexpr_to_NowTerm fx).

Axiom bounds_to_formula : singleBoundTerm -> Syntax.state -> Prop * (R -> Prop).

Axiom bound_fexpr_sound : forall ivs fx sbts,
    bound_fexpr fx = sbts ->
    Forall (fun sbt =>
              forall st st',
                vmodels ivs st st' ->
                let '(P,Pr) := bounds_to_formula sbt st in
                P -> exists fval, fexprD fx st' = Some fval
                                  /\ exists val,
                                    F2OR fval = Some val /\ Pr val)%type
           sbts.

Fixpoint AnyOf (Ps : list Prop) : Prop :=
  match Ps with
    | nil => False
    | P :: Ps => P \/ AnyOf Ps
  end%type.

Fixpoint varmap_check_fexpr (ivs : list (Var * Var)) (e : fexpr) : Prop :=
  match e with
    | FVar v      => exists lv, In (lv, v) ivs
    | FConst _    => True
    | FPlus e1 e2 => varmap_check_fexpr ivs e1 /\
                     varmap_check_fexpr ivs e2
  end%type.

(* perhaps unnecessary *)
Fixpoint varmap_check_fcmd (ivs : list (Var * Var)) (c : fcmd) : Prop :=
  match c with
    | FSeq c1 c2   => varmap_check_fcmd ivs c1 /\
                      varmap_check_fcmd ivs c2
    | FSkip        => True
    | FAsn v e     => In (v, v) ivs /\ varmap_check_fexpr ivs e
    | FIte e c1 c2 => varmap_check_fexpr ivs e  /\
                      varmap_check_fcmd   ivs c1 /\
                      varmap_check_fcmd   ivs c2
    | FHavoc _     => True
    | FFail        => True
  end%type.

Lemma vmodels_irrelevant_update :
  forall (ivs : list (Var * Var)) (v v' : Var) (s : statef)
         (x : Syntax.state) (x1 : R) (val : float),
    vmodels ivs x s ->
    Forall (fun (vv : (Var * Var)) =>
              let '(lv, rv) := vv in 
              lv <> v' /\ rv <> v)%type ivs ->
    vmodels ivs (fupdate x v' x1) (fupdate s v (Some val)).
Proof.
  induction 2. 
  - simpl. constructor.
  - destruct x0. fwd.
    simpl.
    split.
    + unfold fupdate, realify_state.
      do 2 (rewrite rel_dec_neq_false; eauto with typeclass_instances).
      red in H. red in H. fwd. rewrite H. reflexivity.
    + apply IHForall. inversion H. assumption.
Qed.

(* The actually correct definition of var_spec_valid *)
Fixpoint var_spec_valid' {T U : Type} (vs : list (T * U)) : Prop :=
  match vs with 
    | nil             => True
    | (lv, rv) :: vs' =>
      (Forall (fun vv => 
                let '(lv', rv') := vv in
                lv' <> lv /\ rv' <> rv)%type vs' /\
      var_spec_valid' vs')%type
  end.

(* Lemmas aboutt Forall, needed for HoareA_ex_asn *)
Lemma Forall_impl : forall T (P Q : T -> Prop) ls,
                      Forall (fun x => P x -> Q x) ls ->
                      (Forall P ls -> Forall Q ls).
Proof.
  induction 2.
  - constructor.
  - inversion H; clear H; subst.
    constructor; eauto.
Qed.

Lemma Forall_tauto : forall T (P : T -> Prop) ls,
                       (forall x, P x) ->
                       Forall P ls.
Proof.
  induction ls; simpl; intros; eauto.
Qed.

Lemma vmodels_fupdate_match :
   forall (ivs : list (Var * Var)) (v v' : Var)
          (sf : statef) (ss : Syntax.state) (r : R) (f : float),
   var_spec_valid' ivs ->
   In (v, v') ivs ->
   vmodels ivs ss sf ->
   F2OR f = Some r ->
   vmodels ivs (fupdate ss v r) (fupdate sf v' (Some f)).
Proof.
  induction ivs.
  - simpl in *. constructor.
  - intros.
    destruct H0.
    + simpl. fwd. intros. subst. split. 
      * unfold fupdate, realify_state.
        inversion H1; subst; clear H1; simpl.
        do 2 (rewrite rel_dec_eq_true; eauto with typeclass_instances).
      * clear IHivs. simpl in H3. fwd.
        inversion H1; subst; clear H1.
        apply vmodels_irrelevant_update; auto.
        clear -H0.
        red in H0. fwd. 
        revert H. apply Forall_impl.
        eapply Forall_tauto.
        clear. destruct x. tauto.
    + simpl in H. destruct a. fwd.
      simpl in H2. fwd.
      simpl. split.
      * eapply Forall_forall in H; eauto.
        simpl in H. fwd.
        unfold fupdate, realify_state.
        do 2 (rewrite rel_dec_neq_false; eauto with typeclass_instances).
        simpl in H1. fwd. rewrite H1. reflexivity.
      * simpl in H1. fwd. eauto. 
Qed.

Lemma varmap_check_contradiction :
  forall (ivs : list (Var * Var)) (v : Var) (fe : fexpr)
         (sf : statef) (ss : Syntax.state),
    varmap_check_fexpr ivs fe ->
    vmodels ivs ss sf ->
    fexprD fe sf = None ->
    False.
Proof.
  intros.
  induction fe.
  - induction ivs.
    + intros. simpl in *. fwd. assumption.
    + intros. simpl in *. fwd. destruct a. fwd.
      destruct H.
      { inversion H; subst; clear H.
        unfold realify_state in H0.
        rewrite H1 in H0. congruence. }
      { eauto. } 
  - inversion H1.
  - inversion H1; subst; clear H1.
    destruct (fexprD fe1 sf).
    + destruct (fexprD fe2 sf).
      * inversion H3.
      * apply IHfe2; try reflexivity.
        inversion H. assumption.
    + destruct (fexprD fe2 sf).
      * apply IHfe1; try reflexivity.
        inversion H. assumption.
      * inversion H. auto. 
Qed.

(* Significant correctness lemma for HoareA/Abstractor as a whole *)
Lemma HoareA_ex_asn :
  forall ivs (P : _ -> Prop) v v' e,
    var_spec_valid' ivs ->
    varmap_check_fexpr ivs e ->
    In (v, v') ivs ->
    HoareA_ex ivs ivs
      (fun ss : Syntax.state =>
         AnyOf (List.map (fun sbt =>
                            let '(pred,bound) := bounds_to_formula sbt ss in
                            pred /\ forall val : R,
                                      bound val -> P (fupdate ss v val))
                         (bound_fexpr e)))%type
      (FAsn v' e)
      P.
Proof.
  red. red. red. intros.
  forward_reason.
  split.
  { consider (fexprD e s); intros; eexists.
    - econstructor; eauto.
    - eapply FEAsnN. auto. }
  split.
  { clear -H0 H2. intro.
    inversion H; subst; clear H.
    eapply varmap_check_contradiction; eauto. }
  { intros.
    inversion H4; clear H4; subst.
    generalize (bound_fexpr_sound ivs e _ eq_refl). intro.

    induction (bound_fexpr e).
    { simpl in *. contradiction. }
    { simpl in *.
      inversion H4; subst; clear H4.
      destruct H3; auto.
      clear IHl H9.
      specialize (H8 _ _ H2).
      destruct (bounds_to_formula a x). fwd.
      specialize (H4 _ H8).
      rewrite H5 in H7. inversion H7; subst; clear H7.
      eexists; split; [|apply H4]. 
      apply vmodels_fupdate_match; auto. } }
Qed.



(* Anyof -> feval will *)

(* Type checking - need to see if all variables mentioned on RHS in program are
   contained in variable map. Add successful typecheck to premises of asn
   (and others that need it maybe) *)

(* We want to be able to abstract program x := 1+1, and show that it
   refines x > 0 *)


(*
Fixpoint bounds_to_formula' (bounds : list singleBoundTerm) (center : Term) : Prop :=
  match bounds with
    | nil => True
    | (mkSBT lb ub side) :: bounds' =>
      ((bounds_to_formula' bounds' center) /\
      (side -> ((Comp lb center Le) /\
                (Comp center ub Le))))%type
  end.
*)

(*
    HoareA_ex ivs ivs
      (fun ss : Syntax.state =>
         AnyOf (List.map (fun sbt =>
                            let '(pred,bound) := bounds_to_formula sbt ss in
                            pred /\ forall val : R,
                                      bound val -> P (fupdate ss v val))
                         (bound_fexpr e)))%type
      (FAsn v' e)
      P
*)

(* TODO prove consequence *)

(*
Lemma fwp_correct :
  forall ivs c P,
    HoareA_ex ivs ivs
*)
(*
    HoareA_ex ivs ivs
      (fun ss : Syntax.state =>
         AnyOf (List.map (fun sbt =>
                            let '(pred,bound) := bounds_to_formula sbt ss in
                            pred /\ forall val : R,
                                      bound val -> P (fupdate ss v val))
                         (bound_fexpr e)))%type
      (FAsn v' e)
      P.
*)

Check conseqR.

Lemma Hoare__conseq :
  forall (P P' Q Q' : statef -> Prop) (c : fcmd),
    (forall (st : statef), P st  -> P' st) ->
    (forall (st : statef), Q' st -> Q  st) ->
    Hoare_ P' c Q' ->
    Hoare_ P c Q.
Proof.
  intros. unfold Hoare_, Hoare in *.
  intros. apply H in H2. apply H1 in H2. fwd. 
  split; [|split]; try eexists; eauto.
Qed.

(* Weakest-precondition calcluation function for fcmd language *)
(* TODO made fwp take ivs? *)
Fixpoint fwp (c : fcmd) (P : Syntax.state -> Prop) : Syntax.state -> Prop :=
  match c with
  | FSkip => P
  | FSeq c1 c2 => fwp c1 (fwp c2 P)
  | FAsn v e => (fun ss =>
                   AnyOf (List.map
                            (fun sbt =>
                               let '(pred,bound) := bounds_to_formula sbt ss in
                               pred /\ forall val : R,
                                         bound val -> P (fupdate ss v val))
                            (bound_fexpr e)))%type
  | FFail => fun s => False
  | FHavoc v => fun s => False
  (*| FIte ex c1 c2 => (fun s =>
                        (fexprD ex s = Some fzero /\ fwp c1 P s) \/
                        (exists (f : source.float), f <> fzero /\
                                                   fexprD ex s = Some f /\
                                                   fwp c2 P s))%type*)
  | FIte _ _ _ => fun s => False
  end.

Lemma fwp_correct :
  forall c ivs P,
    var_spec_valid' ivs ->
    varmap_check_fcmd ivs c ->
    HoareA_ex ivs ivs
              (fwp c P)
              c
              P.
Proof.
  intros c.
  induction c; intros.
  { simpl. eapply Hoare__seq.
    - eapply IHc1. 
      + assumption.
      + simpl in H0; fwd; assumption.
    - eapply IHc2. 
      + assumption. 
      + simpl in H0; fwd; assumption. }
  { eapply Hoare__skip. }
  { eapply HoareA_ex_asn; simpl in H0; fwd; assumption. }
  { (* wp implemented as false here; could perhaps be weaker *)
    simpl. repeat red. intros.
    fwd. contradiction. }
  { (* wp implemented as false here; could perhaps be weaker *)
    simpl. repeat red. intros.
    fwd. contradiction. }
  { simpl. repeat red. intros.
    fwd. contradiction. }
Qed.

Print fcmd.
Print fexpr.

Definition simple_prog : fcmd :=
  FAsn "x" (FConst (nat_to_float 1%nat)).

Opaque nat_to_float.

Fact fwp_test :
  (fwp simple_prog (fun (ss : Syntax.state) => (ss "x" > 0)%R)%type)
    (fun _ => 0%R).
Proof.
  compute.
  simpl. left.
  generalize (bound_fexpr_sound). intro.
  SearchAbout bounds_to_formula.
  
Abort.
(* TODO: Prove that predicates produced by fwp have SEMR property
   Also prove assignment Hoare rule *)
