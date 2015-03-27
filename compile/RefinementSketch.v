Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.ProofRules.
Require Import String.
Open Local Scope string_scope.
Open Local Scope HP.

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
| OEIteTrue :
    forall s os' ex c1 c2,
      cexprD ex s = Some 0%R ->
      oeval s c1 os' ->
      oeval s (Ite ex c1 c2) os'
| OEIteFalse:
    forall s os' ex c1 c2 r,
      cexprD ex s = Some r ->
      r <> 0%R ->
      oeval s c2 os' ->
      oeval s (Ite ex c1 c2) os'
| OEHavoc : forall s v val,
      oeval s (Havoc v) (Some (update s v (Some val)))
| OEFail : forall s, oeval s Fail None
.

(* First notion of embedding for our imperative language
   With new semantics distinguishing failure from looping
   Uses oembedStep_maybenot *)
Definition oembed_cmd : cmd -> Syntax.Formula :=
  oembedStep_maybenot nat cmd state
                      oeval
                      (fun st v => st v)
                      [("x",0)] [("x",0)].

(* Making sure we can still handle deterministic, failing,
   and nondeterministic programs *)

(* We cannot prove Fail is a refinement of a deterministic,
   nonfailing program. Good. *)
Lemma fail_refines_prog2_6 :
  |- oembed_cmd Fail -->
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
  |- oembed_cmd cmd1 --> ("x"! = "x").
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
  |- oembed_cmd (Havoc 0) --> ("x"! = "x").
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
  |- oembed_cmd prog_havoc_crash --> ("x"! = "x").
Proof.
  unfold oembed_cmd, oembedStep_maybenot.
  simpl; intros.
  unfold eval_comp; simpl.
  forward_reason.
  destruct H0.
  - exfalso. apply H0. eexists. unfold prog_havoc_crash.
    econstructor.
    + constructor.
    + eapply OEIteFalse.
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
Definition oembed_cmd' : cmd -> Syntax.Formula :=
  oembedStep_maybenone nat cmd state
                       oeval
                       (fun st v => st v)
                       [("x",0)] [("x",0)].

(* With this formulation we are still able to prove
   this simple valid refinement *)
Lemma cmd1_refines_prog2_7 : 
  |- oembed_cmd' cmd1 --> ("x"! = "x").
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
  |- oembed_cmd' Fail -->
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
  |- oembed_cmd' (Havoc 0) --> ("x"! = "x").
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
  |- oembed_cmd' prog_havoc_crash --> ("x"! = "x").
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

Print oembed_cmd'.
Print Asn.
Print cexpr.

Definition prog_inc : cmd :=
  Asn 0 (CPlus (CConst 1) (CVar 0)).

(* As an additional test, let's see if we can prove a refinement
   that should be true about a nondeterministic program *)
Lemma good_nondet_refines_7 :
  |- oembed_cmd' prog_inc --> ("x"! > "x").
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
Check Hoare.

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

(* Hoare rule for if-then-else - TODO *)

(* Hoare rule for havoc - TODO *)

(* Hoare rule for Fail; for use in weakest-precondition calculation *)
Lemma FailR_pre : forall P, CHoare (fun _ => False) Fail P.
Proof.
  simpl. red. inversion 1.
Qed.

(* Weakest-precondition calcluation function *)
Fixpoint wp (c : cmd) (P : state -> Prop) : state -> Prop :=
  match c with
  | Skip => P
  | Seq a b => wp a (wp b P)
  | Asn v e => (fun s =>
                 exists val, cexprD e s = Some val /\
                             let s' := update s v (Some val) in
                             P s')%type
  | Fail => fun s => False
  | _ => fun s => False (* TODO: ITE; Havoc *)
  end.    

Theorem wp_sound :
  forall c P,
    CHoare (wp c P) c P.
Proof.
  induction c; intros.
  - eapply SeqR; eauto.
  - apply SkipR.
  - apply AssR_pre.
  - admit. (* wp function doesn't do Ite *)
  - admit. (* wp function doesn't do Havoc *)
  - apply FailR_pre.
Qed.

SearchAbout Semantics.eval_formula.
Print oembed_cmd'.
Print embed_coq.
Check CHoare.
Locate state.
Print state.
Print Syntax.state.
Check embed_coq.

(* Function for embedding state transformers expressed in Gallina into TLA
   Need to deal with the mismatch between state and Syntax.state... *)
(*
Definition embed_coq2 : (state -> state) -> Syntax.Formula :=
  embedStep string (Syntax.state -> Syntax.state) Syntax.state
            (fun st p st' => st' = p st)%type
            (fun st v => Some (st v))
            [("x","x")] [("x","x")].
*)

(* The correctness lemma that we ultimately want to prove will look
   something like this *)
(*
Lemma hoare_embed :
  forall P c Q,
    CHoare P c Q ->
    (|- oembed_cmd' c) ->
    (|- embed_coq2 (fun x y => P x -> Q y)).
*)
