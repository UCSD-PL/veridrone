Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.ProofRules.
Require Import String.
Local Open Scope HP_scope.
Local Open Scope string_scope.
Require Import List.
Require Import Strings.String.
Import ListNotations.
Require Import Rdefinitions.
Require Import RelDec.
Require Import Coq.Reals.Rbase.
Require Import Z3.Tactic.
Require Import Embed.
Require Import FloatEmbed.
Require Import TLA.Automation.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Tactics.

Lemma Z3Test : forall (a : R), (a + 1 = 3)%R%type -> ((a + 2 = 3)%R /\ ((1+1)%R=2%R)%R)%type.
Proof.
  intros.
  (* z3 solve. *)
  Abort.

(* Implementation of postprocessing automation for the Abstractor,
   using the Z3 plugin to simplify the terms produced b ythe abstractor *)

(* test case: proportional controller *)

(* c is constant and goal is 0 *)

Definition proportional_controller : fcmd :=
  FAsn "a" (FMinus (FConst fzero) (FVar "x")).

Definition proportional_controller_ivs : list (Var * Var) :=
  [("a", "a"); ("x", "x")].

(* "Pushing" Embed through connectives *)
Lemma lequiv_formula_iff :
  forall (P Q : Formula),
    (forall tr, eval_formula P tr <-> eval_formula Q tr) <->
    (P -|- Q).
Proof.
  intros.
  split.
  - intros. split; breakAbstraction; intros; apply H; assumption.
  - intros. unfold lequiv in H. destruct H.
    breakAbstraction.
    split; intros; [apply H | apply H0]; assumption.
Qed.

Ltac shatterAbstraction :=
  try apply lequiv_formula_iff; unfold lequiv in *; breakAbstraction.  

Lemma embed_push_TRUE :
  Embed (fun _ _ => True) -|- TRUE.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_FALSE :
  Embed (fun _ _ => False) -|- FALSE.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma embed_push_And :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y /\ P2 x y) -|- F1 //\\ F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Or :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y \/ P2 x y) -|- F1 \\// F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Lemma embed_push_Imp :
  forall (P1 P2 : _ -> _ -> Prop) (F1 F2 : Formula),
    Embed P1 -|- F1 -> Embed P2 -|- F2 ->
    Embed (fun x y => P1 x y -> P2 x y) -|- F1 -->> F2.
Proof.
  shatterAbstraction. intuition.
Qed.

Ltac fwd := forward_reason.

Lemma embed_push_Exists :
  forall (T : Type) (P : T -> state -> state -> Prop) (F : T -> Formula),
    (forall (t : T), Embed (P t) -|- F t) ->
    Embed (fun x y => exists (t : T), (P t x y)) -|- lexists F.
Proof.
  shatterAbstraction.
  intuition.
  fwd. specialize (H x). fwd.
  eexists. eauto.
  fwd. specialize (H x). fwd.
  eexists. eauto.
Qed.

Lemma embed_push_Forall :
  forall (T : Type) (P : T -> state -> state -> Prop) (F : T -> Formula),
    (forall (t : T), Embed (P t) -|- F t) ->
    Embed (fun x y => forall (t : T), (P t x y)) -|- lforall F.
Proof.
  intros.
  shatterAbstraction. intuition.
  eapply H. apply H0.
  eapply H. apply H0.  
Qed.

Lemma embed_push_Const : forall P, Embed (fun _ _ => P) -|- PropF P.
Proof.
  shatterAbstraction; tlaIntuition.
Qed.

(* Relation expressing a side-condition that must be used to push embed through arithmetic facts *)
Definition evals_to (f : Term) (f' : state -> state -> R) : Prop :=
  (eval_term f = f')%type.

Notation "f =|> g" := (evals_to f g) (at level 60).

(* comparison pushing *)
Lemma embed_push_Eq :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => l' x y = r' x y)%type -|-
          Comp l r Eq.
Proof.
  intros.
  unfold evals_to in *. 
  shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Gt :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rgt (l' x y) (r' x y))%type -|-
          Comp l r Gt.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Ge :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rge (l' x y) (r' x y))%type -|-
          Comp l r Ge.
Proof.
  intros.
  unfold evals_to in *. 
  shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Lt :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rlt (l' x y) (r' x y))%type -|-
          Comp l r Lt.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma embed_push_Le :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    Embed (fun x y => Rle (l' x y) (r' x y))%type -|-
          Comp l r Le.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

(* arithmetic pushing *)
Lemma arith_push_plus :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    PlusT l r =|> (fun x y => l' x y + r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_minus :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MinusT l r =|> (fun x y => l' x y - r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_mult :
  forall l r l' r',
    l =|> l' ->
    r =|> r' ->
    MultT l r =|> (fun x y => l' x y * r' x y)%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_inv :
  forall l l',
    l =|> l' ->
    InvT l =|> (fun x y => / (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_cos :
  forall l l',
    l =|> l' ->
    CosT l =|> (fun x y => Rtrigo_def.cos (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

Lemma arith_push_sin :
  forall l l',
    l =|> l' ->
    SinT l =|> (fun x y => Rtrigo_def.sin (l' x y))%R.
Proof.
  intros. unfold evals_to in *. shatterAbstraction. subst. reflexivity.
Qed.

(* var, real *)
Lemma arith_push_VarNow :
  forall (x : Var),
    VarNowT x =|> fun st _ => st x.
Proof.
  reflexivity.
Qed.

Lemma arith_push_VarNext :
  forall (x : Var),
    VarNextT x =|> fun _ st' => st' x.
Proof.
  reflexivity.
Qed.

(* special cases for 0 and 1: want to compile these into nats,
   since nat are easier to work with *)
Lemma arith_push_Nat_zero :
    NatT 0 =|> fun _ _ => 0%R.
Proof. reflexivity. Qed.

Lemma arith_push_Nat_one :
    NatT 1 =|> fun _ _ => 1%R.
Proof. reflexivity. Qed.

Lemma arith_push_Nat :
  forall (n : nat),
    NatT n =|> fun _ _ => INR n.
Proof. reflexivity. Qed.

Lemma arith_push_Real :
  forall (r : R),
    RealT r =|> fun _ _ => r.
Proof. reflexivity. Qed.

(* for solving goals containing fupdate *)
Check fm_update.

(*
Lemma arith_push_fm_update_eq :
  forall (t: state -> state -> R) (v : Var) (X : Term) (f : state -> state -> state),
    X =|> t ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v).
Proof.
  intros. unfold evals_to in *.
  rewrite H. unfold fupdate.
  rewrite rel_dec_eq_true; eauto with typeclass_instances.
Qed.

Lemma arith_push_fupdate_neq :
  forall (t: state -> state -> R) (v v' : Var) (X : Term) (f : state -> state -> istate),
    v <> v' ->
    X =|> (fun x y : state => f x y v') ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v').
Proof.
  intros.
  unfold fupdate, evals_to in *. rewrite H0.
  rewrite rel_dec_neq_false; eauto with typeclass_instances.
Qed.
*)


Create HintDb embed_push discriminated.
Create HintDb arith_push discriminated.

Hint Rewrite
     embed_push_TRUE embed_push_FALSE
     embed_push_And embed_push_Or embed_push_Imp
     embed_push_Exists embed_push_Forall
     embed_push_Const
  : embed_push.

Hint Rewrite
     embed_push_Eq embed_push_Gt embed_push_Ge embed_push_Lt embed_push_Le
     using solve [eauto 20 with arith_push]
                         : embed_push.

(* for the "<>" goals created by arith_push_fupdate_neq *)
Hint Extern
     0 (_ <> _) => congruence : arith_push.

(* Other miscellaneous rewriting lemmas *)
Lemma AnyOf_singleton :
  forall (P : Prop), AnyOf [P] -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma AnyOf_weaken :
  forall (P : Prop) (Ps : list Prop),
    AnyOf Ps |-- AnyOf (P :: Ps).
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma and_True_snip1 :
  forall (P : Prop),
    True //\\ P -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma and_True_snip2 :
  forall (P : Prop),
    P //\\ True -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma or_False_snip1 :
  forall (P : Prop),
    P \\// False -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

Lemma or_False_snip2 :
  forall (P : Prop),
    False \\// P -|- P.
Proof.
  shatterAbstraction. tauto.
Qed.

(* Very simple program for testing. We want to prove that x stays >0 *)
Definition float_one := source.nat_to_float 1.
Definition simple_prog : fcmd :=
  FAsn "x" (FPlus (FConst float_one) (FVar "x")).

Definition simple_prog_ivs : list (Var) :=
  [("x")].

Definition simpler_prog : fcmd :=
  FAsn "x" (FConst float_one).

Lemma PropF_revert :
  forall (P : Prop) (G Q : Syntax.Formula),
    (P -> G |-- Q) ->
    (G |-- PropF P -->> Q).
Proof.
  tlaIntuition.
Qed.

Lemma PropF_pull :
  forall (P : Prop) (G Q : Syntax.Formula),
    P ->
    (G |-- Q) ->
    (PropF P -->> G |-- Q).
Proof.
  tlaIntuition.
Qed.

Require Import bound.
Require Import source.
Definition FP2RP (vs : list Var) (P : fstate -> Prop) : state -> Prop :=
  (fun st =>
     exists (fst : fstate), vmodels vs fst st /\ P fst).

(* Version of HoareA_embed_ex we can use for rewriting. *)
Require Import source.
Require Import ExtLib.Tactics.
Import FloatEmbed.
Lemma Hoare__embed_rw :
  forall (c : fcmd)
         (vs : list string),
    (*var_spec_valid' vs ->*)
    (*varmap_check_fcmd vs c ->*)
    fembed_ex vs c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  Embed (fun st st' : state =>
           (exists fst : fstate,
             vmodels vs fst st /\
             (P fst -> exists fst' : fstate, vmodels vs fst' st' /\ Q fst'))).
Proof.
  intros.
  breakAbstraction.
  intros.
  fwd.
  exists x0.
  split; auto.
  intros.
  eapply fwp_correct in H2.
  fwd.
  specialize (H3 _ H1).
  exists x1.
  split; auto.
Qed.

Require Import source.
Definition FP2RP' (vs : list Var) (P : fstate -> Prop) (Q : Prop) : state -> Prop :=
  (fun st =>
     exists (fst : fstate), vmodels vs fst st /\ (P fst -> Q)).

Check FloatEmbed.embed_ex.

Lemma Hoare__embed_rw' :
  forall (c : fcmd)
         (vs : list Var),
    (*varmap_check_fcmd vs c ->*)
    FloatEmbed.embed_ex vs c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  Embed (fun st st' : state =>
           FP2RP' vs P (exists fst' : fstate, vmodels vs fst' st' /\ Q fst') st).
Proof.
  generalize (Hoare__embed_rw); intro HHer.
  simpl in HHer.
  simpl.
  unfold FP2RP'.
  eapply HHer.
Qed.
Axiom Always_proper : Proper (lentails ==> lentails) Syntax.Always.
Existing Instance Always_proper.

(* Used to begin rewriting in our goal. *)
Lemma lequiv_rewrite_left :
  forall (A B C : Formula),
    A -|- C -> C |-- B -> A |-- B.
Proof.
  shatterAbstraction. intuition.  
Qed.

(* Convert a predicate over float states to a predicate over real states *)

(*
Definition FP2RP (P : fstate -> Prop) : state -> Prop :=
  (fun st =>
     exists (fst : fstate),
       (forall (v : Var) (f : float), fstate_lookup fst v = Some f ->
                                      exists r, F2OR f = Some r /\ st v = r) /\
       P fst).
 *)

(* Here is the thing I am trying to figure out *)
(*
Lemma FP2RP_rewrite :
  forall ivs,
  _ /\ (isFloat ivs _) -|- FP2RP ivs (fun st => ... (F2R x...)).
*)

(* this theorem is not true so try something that is, like always set x to 5; need invariant that x is float
   simple_prog_ivs will be given to is_float
 *)


(* Automation for rewriting Embeds *)
Hint Extern
     0 (_ =|> (fun _ _ => ?X)) => first [ apply arith_push_Nat_zero | apply arith_push_Nat_one
                                          | apply arith_push_Nat | apply arith_push_Real]
                                  : arith_push.

Hint Resolve
     arith_push_plus arith_push_minus arith_push_mult arith_push_inv
     arith_push_sin arith_push_cos
     arith_push_VarNow arith_push_VarNext
     (*arith_push_fupdate_eq arith_push_fupdate_neq*)
  : arith_push.

(* Automation for pushing through embed rewriting *)
Ltac crunch_embeds :=
  progress repeat
           match goal with
           | |- Embed (fun x y => vmodels _ _ _) -|- _ => reflexivity
           | |- Embed (fun x y => _ -> _) -|- _ => eapply embed_push_Imp
           | |- Embed (fun x y => _ \/ _) -|- _ => eapply embed_push_Or
           | |- Embed (fun x y => _ /\ _) -|- _ => eapply embed_push_And
           | |- Embed (fun x y => exists z, _) -|- _ => eapply embed_push_Exists; intro
           | |- Embed (fun x y => forall z, _) -|- _ => eapply embed_push_Forall; intro
           | |- Embed (fun x y => _ = _) -|- _ => eapply embed_push_Eq; eauto with arith_push
           | |- Embed (fun x y => (_ < _)%R) -|- _ => eapply embed_push_Lt; eauto with arith_push
           | |- Embed (fun x y => (_ <= _)%R) -|- _ => eapply embed_push_Le; eauto with arith_push
           | |- Embed (fun x y => (_ > _)%R) -|- _ => eapply embed_push_Gt; eauto with arith_push
           | |- Embed (fun x y => (_ >= _)%R) -|- _ => eapply embed_push_Ge; eauto with arith_push
           | |- Embed (fun x y => ?X) -|- _ => eapply embed_push_Const
           end.

(* Small logic lemmas for the subsequent theorem *)
Lemma lentail_cut1 :
  forall (A B C : Formula),
    C |-- A ->
    A -->> B |-- C -->> B.
Proof.
  intros. breakAbstraction. intuition.
Qed.

Lemma lentail_cut2 :
  forall (A B C D : Formula),
    C |-- A ->
    B |-- D ->
    (A -->> B |-- C -->> D).
Proof.
  intros. tlaIntuition.
Qed.

Lemma land_comm_left :
  forall (A B C : Formula),
    A //\\ B |-- C ->
    B //\\ A |-- C.
Proof.
  tlaIntuition.
Qed.

Lemma limpl_comm1 :
  forall (A B C D : Formula),
    A |-- B -->> C -->> D ->
    A |-- C -->> B -->> D.
Proof.
  tlaIntuition.
Qed.


(*Fact fwp_simple : |-- "x" > 0 //\\ [](oembed_fcmd simple_prog_ivs simple_prog_ivs simple_prog) -->> []("x" > 0).*)
Fact fwp_simpler : |-- "x" > 0 //\\ [](FloatEmbed.embed_ex simple_prog_ivs simpler_prog) -->> []("x" > 0).
Proof.
  erewrite -> Hoare__embed_rw.
  charge_intros.
  eapply discr_indX.
  { red; intuition. }
  { charge_assumption. }
  { charge_assumption. }
  {
    (* rhs *)
    rewrite landforallDL. eapply lforallL.
    instantiate (1 := (fun fst => exists f, fstate_lookup fst "x" = Some f /\ exists r, F2OR f = Some r /\ (r > 0)%R)).
    tlaRevert.
    simpl fwp.
    eapply lequiv_rewrite_left.

    {
      crunch_embeds.
    }


    apply lexistsL.
    intro.
    
    apply land_comm_left.
    apply landAdj.
    apply limpl_comm1.
    apply lentail_cut2.

    Require Import Coq.micromega.Psatz.
    {
      breakAbstraction.
      intros.
      exists float_one.
      split; try reflexivity.
      left.
      split; auto. 
      intros.
      generalize fstate_lookup_update_match; intro Hflum.
      symmetry in Hflum.
      rewrite Hflum.
      exists x0.
      split; try reflexivity.
      exists x1.
      split; auto.
      unfold F2OR, FloatToR in H0.
      destruct x0; try congruence.
      - lazy in H0. lazy in H1. (* contradiction *) psatz R.
      - lazy in H1. psatz R.
    }
    {
      breakAbstraction.
      intros.
      fwd.
      unfold vmodels, models in H.
      specialize (H "x"). fwd. unfold simple_prog_ivs in H. simpl in H.
      destruct H; auto. fwd.
      rewrite fstate_lookup_fm_lookup in H1.
      rewrite H1 in H. inversion H; subst.
      unfold asReal in H5. rewrite H2 in H5. inversion H5. lra.
    }
  }
Qed.

(*
Definition varValidPre (v : Var) : Syntax.Formula :=
  Embed (fun pre _ =>
           exists (f : float), (eq (F2OR f) (Some (pre v)))).

Definition varValidPost (v : Var) : Syntax.Formula :=
  Embed (fun _ post =>
           exists (f : float), (eq (F2OR f) (Some (post v)))).

Definition varValidBoth (v : Var) : Syntax.Formula :=
  varValidPre v //\\ varValidPost v.           
 *)

(* Embed (...) can't be a state formula, so here are versions that
   do not use it. *)

(* TODO: we can't encode these definitions in the current version of RTLA, I think. *)
(*
Definition varValidPre (v : Var) : Syntax.Formula :=
  Embed (fun pre _ =>
           exists (f : float), (eq (F2OR f) (Some (pre v)))).

Definition varValidPost (v : Var) : Syntax.Formula :=
  Embed (fun _ post =>
           exists (f : float), (eq (F2OR f) (Some (post v)))).

Definition varValidBoth (v : Var) : Syntax.Formula :=
  varValidPre v //\\ varValidPost v.           
 *)

(* Predicate capturing that the given variable is a float in the pre-state *)
(* todo, possibly: lift to variable maps? *)
Definition preVarIsFloat (v : Var) : Syntax.Formula :=
  Syntax.Exists float (fun (f : float) =>
                  Comp (RealT (FloatToR f)) (VarNowT v) Eq //\\
                       PropF (exists (r : R), eq (F2OR f) (Some r))).

Lemma sf_preVarIsFloat :
  forall (v : Var),
    is_st_formula (preVarIsFloat v).
Proof.
  intros.
  simpl.
  intuition.
Qed.

Lemma F2OR_FloatToR :
  forall (f : float) (r r' : R),
    F2OR f = Some r ->
    FloatToR f = r' ->
    r = r'.
Proof.
  intros.
  unfold F2OR, FloatToR in *.
  destruct f; try congruence.
Qed.

(* generalized version of Enabled_action, needed to prove
   enabledness goals *)
Lemma Enabled_action_gen
  : forall P Q : Syntax.Formula,
    (forall (st : state) (tr : trace),
        Semantics.eval_formula Q (Stream.Cons st tr) ->
        exists st' : state,
          Semantics.eval_formula P (Stream.Cons st (Stream.forever st'))) ->
    Q |-- Enabled P.
Proof.
  tlaIntuition.
  destruct tr.
  eapply H in H0.
  simpl.
  fwd.
  eauto.
Qed.

Lemma PropF_tauto :
  forall (P : Prop) F,
    P -> F |-- PropF P.
Proof.
  tlaIntuition.
Qed.

Print simpler_prog.

Fact fwp_simpler_full : preVarIsFloat "x" //\\ "x" > 0 //\\
                                [](embed_ex simple_prog_ivs simpler_prog \\//
                                               (Enabled (embed_ex simple_prog_ivs simpler_prog) -->> lfalse))
                                |-- [](preVarIsFloat "x" //\\ "x" > 0).
Proof.
  eapply discr_indX.
  { red. simpl. intuition. }
  { charge_assumption. }
  { tlaIntuition. }

  tlaRevert.
  eapply lorL.
  {
    erewrite -> Hoare__embed_rw.
    eapply lforallL.
    instantiate (1 := (fun fst => exists f, fstate_lookup fst "x" = Some f /\ exists r, F2OR f = Some r /\ (r > 0)%R)).
    simpl fwp.
    cbv zeta.
    eapply lequiv_rewrite_left.
    { crunch_embeds. }
    apply lexistsL.
    intros.
    charge_intros.
    etransitivity.
    {
      charge_use.
      tlaRevert.
      apply landL1. (* get rid of the fact we used *)
      charge_intro.
      apply (lexistsR float_one).
      charge_split; [apply PropF_tauto; reflexivity|].
      charge_left.
      charge_split; [apply PropF_tauto; constructor|].
      charge_intros.
      apply (lexistsR x0).
      rewrite <- (fstate_lookup_update_match).
      charge_split; [apply PropF_tauto; reflexivity|].
      apply (lexistsR x1).
      charge_split; [charge_assumption|].
      match goal with
      | |- context[Fcore_defs.F2R ?X] => 
        let X2 := eval compute in (Fcore_defs.F2R X) in change (Fcore_defs.F2R X) with X2
      end.
      
      breakAbstraction.
      intros.
      lra.
    }
    {
      apply lexistsL. intros.
      breakAbstraction.
      intros. fwd.
      split.
      { do 2 red in H.
        specialize (H "x"). fwd.
        simpl in H. destruct H; auto. fwd.
        rewrite fstate_lookup_fm_lookup in H0. rewrite H0 in H. inversion H; subst.
        unfold asReal in H4. rewrite H1 in H4. inversion H4; subst.
        exists x3.
        split.
        - unfold F2OR in H1. destruct x3; congruence.
        - eauto.
      }
      {
        do 2 red in H.
        specialize (H "x"). fwd. simpl in H.
        destruct H; auto. fwd.
        rewrite fstate_lookup_fm_lookup in H0. rewrite H0 in H. inversion H; subst.
        unfold asReal in H4. rewrite H1 in H4. inversion H4; subst.
        assumption.
      }
    }
  }
  {
    (* enabledness tactic? *)
    charge_intro.
    transitivity lfalse; [| eapply lfalseL].
    charge_use.
    tlaRevert.
    eapply Lemmas.forget_prem.
    Require Import TLA.Tactics.
    charge_intro.
    eapply Enabled_action_gen.
    simpl.
    intros.
    clear tr.
    fwd.
    eapply (ex_state "x").
    eapply ex_state_any.
    unfold models.
    intros.
    
    (*intro st0. clear st0.*)
    generalize (F2OR_FloatToR _ _ _ H1 H); intro HF2OR.
    subst.

    eexists.
    exists ([("x", x)]).
    eexists.
    split.
    { split.
      - intros.
        simpl in H2. destruct H2; try contradiction. subst.
        exists x.
        split; auto.
      - intros. simpl.
        consider (string_dec s "x"); intros; subst; try reflexivity.
        simpl in H2.
        exfalso. auto.
    }
    { split; [|econstructor; simpl; reflexivity].
      intros. split.
      { intros.
        consider (string_dec "x" s); intros; subst.
        { unfold asReal. eexists. split; simpl; reflexivity. }
        { simpl in H2. destruct H2; [congruence|contradiction]. } }
      { intros.
        simpl.
        consider (string_dec s "x"); intros; subst; [|reflexivity].
        simpl in H2. destruct H2; auto. } } }
Qed.

Lemma limpl_limpl_land :
  forall (A B C : Syntax.Formula),
    |-- A //\\ B -->> C ->
    |-- A -->> B -->> C.
Proof.
  tlaIntuition.
Qed.

(* velocity-shim controller *)
(*
Definition velshim : fcmd :=
  FIte (FMinus (FVar "ub") (FPlus (FMult (FVar "a") (FVar "d")) (FVar "vmax")))
       (FAsn "a" (FVar "a"))
       (FAsn "a" (FConst fzero)).
 *)

Definition f10 := Eval lazy in (concretize_float (nat_to_float 10)).

Definition velshim : fcmd :=
  FIte (FMinus (FConst f10) (FPlus (FMult (FVar "a") (FConst float_one)) (FVar "v")))
       (FAsn "a" (FConst fzero))
       (FAsn "a" (FVar "a")).

Definition velshim_ivs : list (Var * Var) :=
  [("a", "a"); ("v", "v")].

(* TODO: prove thorem about always-enabledness of oembed_fcmd
     (true of any semantics embedded using oembedStep_maybenone, provided
     that any state has some other state it steps to *)
Lemma feval_never_stuck :
  forall (fs : fstate) (c : fcmd),
  exists (ofst : option fstate),
    feval fs c ofst.
Proof.
  intros fs c.
  generalize dependent fs.
  induction c.
  - intros.
    specialize (IHc1 fs). fwd.
    destruct x.
    + specialize (IHc2 f). fwd.
      eexists. econstructor 2; eassumption.
    + eexists. econstructor 3. eassumption.
  - intros. eexists. econstructor.
  - intros.
    consider (fexprD f fs); intros.
    + eexists. econstructor 4. eassumption.
    + eexists. econstructor 5. eassumption.
  - intros.
    consider (fexprD f fs); intros.
    + generalize (float_lt_ge_trichotomy f0 fzero); intro Htri.
      destruct Htri.
      * specialize (IHc1 fs). fwd. eexists. econstructor 6; eauto.
      * specialize (IHc2 fs). fwd. eexists. econstructor 7; eauto.
    + eexists. econstructor 8; eauto.
  - intros. eexists. econstructor.
  - intros. eexists. econstructor.
    Grab Existential Variables.
    apply fzero.
Qed.

(* TODO - prove these lemmas inline *)
Lemma oembed_fcmd_enabled :
  forall (ivs ovs : list (Var * Var)) (fc : fcmd),
    (|-- Enabled (oembed_fcmd ivs ovs fc)).
Proof.
  breakAbstraction.
  intros.
Abort.

(* Idea: oembedStep_maybenone will always be enabled so long as it is given an evaluation
   relation which is "never stuck" *)
Lemma oembedStep_maybenone_enabled :
  forall (var ast state : Type)
    (eval : state -> ast -> option state -> Prop)
    (asReal : state -> var -> option R)
    (pre_vars post_vars : list (Var * var))
    (prog : ast)
    (Heval : forall (a : ast) (st : state), exists (ost : option state), eval st a ost),
    (|-- Enabled (oembedStep_maybenone var ast state eval asReal pre_vars post_vars prog)).
Proof.
  intros.
  breakAbstraction.
  intros.
Abort.

(* Used to expose post-states, since fwp by default does not let us talk about both
   pre- and post-states *)
Definition fstate_get_rval (v : Var) (P : R -> fstate -> Prop) (fs : fstate) : Prop :=
  match fstate_lookup fs v with
  | None => False
  | Some vf =>
    match F2OR vf with
    | None => False
    | Some vr => P vr fs
    end
  end.

(* Used to get pre-state variable values *)
Lemma inject_var :
  forall (s : Var) G P,
    (G |-- Forall x : R, (RealT x = VarNowT s)%HP -->> P) ->
    (G |-- P).
Proof.
  tlaIntuition.
  eapply H. eassumption.
  reflexivity.
Qed.

Fact fwp_velshim_full : preVarIsFloat "a" //\\ preVarIsFloat "v" //\\ 
                                      (oembed_fcmd velshim_ivs velshim_ivs velshim \\//
                                                   (Enabled (oembed_fcmd velshim_ivs velshim_ivs velshim) -->> lfalse))
                                      |-- (VarNextT "a" = 0 \\// "v" + ((VarNextT "a") * NatT 1) < NatT 10 )%HP.
(*
Fact fwp_velshim_full : preVarIsFloat "a" //\\ preVarIsFloat "v" //\\
                                       ("a" <  0 -->> "v" <= NatT 10)%HP //\\
                                       ("a" >= 0 -->> "a"* (NatT 1) + "v" <= NatT 10)%HP //\\
                                      (oembed_fcmd velshim_ivs velshim_ivs velshim \\//
                                                   (Enabled (oembed_fcmd velshim_ivs velshim_ivs velshim) -->> lfalse))
                                      |-- (VarNextT "a" = 0 \\// "v" + ((VarNextT "a") * NatT 1) < NatT 10 )%HP.
*)
(* TODO need to refactor body of proof to take new hypotheses into account *)
Proof.
  repeat rewrite Lemmas.land_lor_distr_L.
  apply lorL.
  {
    rewrite landC.
    tlaRevert.
    rewrite landC.
    tlaRevert.

    erewrite -> Hoare__embed_rw.
    { (* main goal *)
      Opaque fwp.
      breakAbstraction.
      intro.
      generalize dependent (Stream.hd tr "a").
      generalize dependent (Stream.hd tr "v").
      generalize dependent (Stream.hd (Stream.tl tr) "a").
      generalize dependent (Stream.hd (Stream.tl tr) "v").
      clear tr.
      intros.
      fwd.
      Print fstate_get_rval.
      (* v2 or v1? i think v1 *)
      specialize (H (fstate_get_rval "a" (fun a fs => a = 0 \/ (v1 + a) < 10))%R).
      fwd.
      unfold Value in *.
      subst.
      unfold fstate_get_rval in *.
      unfold fstate_lookupR in *.
      forward.
      destruct H4.
      { Transparent fwp.
        cbv beta iota zeta delta [ fwp velshim fexprD ].
        rewrite H0; rewrite H.
        eexists; split; [ reflexivity | ].

        assert (f = x0) by admit.
        assert (f0 = x) by admit.

        Definition Impl (A B : list singleBoundTerm) : Prop :=
          List.Forall (fun a => (forall st, a.(premise) st -> False) \/ In a B) A.

        Theorem optimize_bound_fexpr
        : forall f opt_f,
            Impl (bound_fexpr f) opt_f ->
            forall P, P opt_f ->
                      P (bound_fexpr f).
        Admitted.
        eapply (@optimize_bound_fexpr (FMinus (FConst f10)
            (FPlus (FMult (FVar "a") (FConst float_one)) (FVar "v")))).
        { Transparent ILInsts.ILFun_Ops.
          cbv beta iota zeta delta
              [ bound_fexpr bound_term fexpr_to_NowTerm cross flat_map app
                            combineTripleMult combineTriplePlus
                            combineTripleMinus simpleBound a_mult premise lb ub c_ge
                            Arithable_Lift simpleBound2 Arithable_R Arithable_Applicative
                            Fun.Applicative_Fun Applicative.ap
                            Applicative.pure c_lt c_le
                            Comparable_R Comparable_Lift simpleBound7 a_plus a_minus land 
                            Comparable_Applicative ILInsts.ILFun_Ops 
                            simpleBound3 simpleBound4 simpleBound5 simpleBound6 simpleBound7
                            ILogicOps_Prop
                            simpleBound8 simpleBound9 simpleBound6 simpleBound10 lofst fstate_lookup_force
              ].
          Lemma Impl_keep : forall A B D,
              Impl B D ->
              Impl (A :: B) (A :: D).
          Proof. Admitted.
          Lemma Impl_drop : forall A B D x,
              (A.(premise) x -> False) ->
              Impl B D ->
              Impl (A :: B) D.
          Proof. Admitted.
          Lemma Impl_nil : Impl nil nil.
                             constructor.
          Qed.

          Ltac show_value val :=
            let x := eval compute in val in
            assert (val = x) by reflexivity.

          Ltac try_it HH :=
            unfold premise;
            show_value error; show_value floatMin; show_value floatMax;
            intros;
            repeat match goal with
                   | H: context[Fappli_IEEE.B2R ?x1 ?x2 ?x3] |- _ => 
                     let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2 in H
                   end;
           repeat match goal with
                  | H : context[Fcore_Raux.bpow ?x1 ?x2] |- _ =>
                    let X2 := eval compute in (Fcore_Raux.bpow x1 x2) in
                                               change (Fcore_Raux.bpow x1 x2) with X2 in H
                  end;
           repeat match type of HH with
                  | context[nat_to_float ?x1]  =>
                    idtac "1" x1 ; 
                    let X2 := eval lazy in (nat_to_float x1) in
                                            idtac "2" ;
                                               change (nat_to_float x1) with X2 in HH
                  end;
           repeat match goal with
                  | H : _ = _ |- _ => rewrite H in *
                  end;
           try (z3 solve; admit).
          repeat first [ eapply Impl_drop with (x:=x3); [ solve [ try_it H9 ] | idtac "dropped" ]
                       | eapply Impl_keep
                       | simple eapply Impl_nil ]. }
        { 


(*
        Print bound_term.
        Print combineTriplePlus.
        Print simpleBound.
Print simpleBound4.

simpleBound = 
fun (triple1 triple2 : singleBoundTerm)
  (combFunc : (fstate -> R) -> (fstate -> R) -> fstate -> R)
  (fla : fstate -> Prop) =>
{|
lb := a_mult (combFunc (lb triple1) (lb triple2))
        (fun _ : fstate => a_minus 1%R error);
ub := a_mult (combFunc (ub triple1) (ub triple2))
        (fun _ : fstate => a_plus 1%R error);
premise := fla |}

simpleBound4 = 
fun (triple1 triple2 : singleBoundTerm)
  (combFunc : (fstate -> R) -> (fstate -> R) -> fstate -> R)
  (fla : fstate -> Prop) =>
{|
lb := a_mult (combFunc (lb triple1) (lb triple2))
        (fun _ : fstate => a_plus 1%R error);
ub := a_mult (combFunc (ub triple1) (ub triple2))
        (fun _ : fstate => a_minus 1%R error);
premise := fla |}
*)
        

(*
        Eval cbv beta iota zeta delta [ bound_fexpr bound_term fexpr_to_NowTerm cross flat_map app
                                        combineTripleMult combineTriplePlus
                                                             combineTripleMinus simpleBound a_mult premise lb ub c_ge
Arithable_Lift simpleBound2 Arithable_R Arithable_Applicative Fun.Applicative_Fun Applicative.ap
Applicative.pure 
c_lt c_le
Comparable_R Comparable_Lift simpleBound7 a_plus a_minus land 
Comparable_Applicative ILInsts.ILFun_Ops 
simpleBound3 simpleBound4 simpleBound5 simpleBound6 simpleBound7
ILogicOps_Prop
simpleBound8 simpleBound9 simpleBound6 simpleBound10 lofst
 
in (bound_fexpr
         (FMinus (FConst f10)
            (FPlus (FMult (FVar "a") (FConst float_one)) (FVar "v")))).
 *)
          unfold maybe_lt0, maybe_ge0, map, AnyOf, bound_fexpr, bound_term, fexpr_to_NowTerm,
          bounds_to_formula, denote_singleBoundTermNew, isVarValid, lb, ub, premise.
          rewrite H0.
          rewrite H.
          repeat rewrite fstate_lookup_update_match with (fst := x3) (v := "a").
          repeat match goal with
            | |- context[Fappli_IEEE.B2R ?x1 ?x2 ?x3] => idtac x3;
              let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2
                 end.

          (* assertions bounding values of variables (hopefully provable later) *)
          (*
          assert (FloatToR x >= 1)%R as Halow by admit.
          assert (FloatToR x <= 101)%R as Haup by admit.
          assert (FloatToR x0 >= 1)%R as Hvlow by admit.
          assert (FloatToR x0 <= 101)%R as Hvup by admit.
           *)

          Lemma crunch_or :
            forall (P P' Q Q' : Prop),
              (P' -> P) -> (Q' -> Q) ->
              P' \/ Q' -> P \/ Q.
          Proof.
            intuition.
          Qed.

          Lemma F2OR_isFloatConstValid :
            forall (f : float) (r : R),
              F2OR f = Some r ->
              isFloatConstValid f.
          Proof.
            intros.
            unfold isFloatConstValid.
            destruct f; try constructor; unfold F2OR in *; try congruence.
          Qed.
          
          repeat split.
          {
            intros.
            fwd.
            eexists.
            split.
            erewrite <- fstate_lookup_update_match. reflexivity.
            left.
            split. eauto.
            intros.
            rewrite <- fstate_lookup_update_match. (* todo - previous ones rewrite in wrong direction *)
            rewrite H9. left.
            clear -H10. lra.
          }

          {
            intros.
            eexists.
            rewrite <- fstate_lookup_update_match.
            split; [reflexivity|].
            left.
            split.
            
            eapply F2OR_isFloatConstValid. eauto.

            intros.
            rewrite <- fstate_lookup_update_match.
            rewrite H9.

            show_value error.
            show_value floatMin.
            show_value floatMax.
            unfold fstate_lookup_force in *.
            rewrite H in H10.
            
            subst.

            z3 solve; admit.
          }

          (* Fappli_IEEE.bounded_lt_emax will let us prove half of this theorem
             (rx <= floatMax) but we can't find any similar theorems in the Flocq library
             that talk about floatMin... *)
          Require Import compcert.flocq.Core.Fcore_generic_fmt.
          Lemma isFloatConstValid_F2OR : forall x : float,
              isFloatConstValid x <->
              exists rx,
                F2OR x = Some rx /\
                (floatMin <=  rx <= floatMax \/
                 floatMin <= -rx <= floatMax \/
                 rx = 0)%R.
          Proof.
            (*  (* failed proof attempt - subnormal_exponent is probably not the right theorem here *)
            intros.
            split.
            { unfold isFloatConstValid. intros.
              destruct x; try contradiction; simpl.
              { eexists. split; auto. }
              { eexists. split; [reflexivity|].
                destruct b.
                { (* negative case *)
                  right; left.
                  generalize subnormal_exponent; intro Hsne.
                  Print Fappli_IEEE.
                  specialize (Hsne Fappli_IEEE.radix2 (Fcore_FLT.FLT_exp prec emax)).
                  
                  Require Import compcert.flocq.Core.Fcore_FLT.
                  SearchAbout Valid_exp.
                  assert (Valid_exp (FLT_exp prec emax)).
                  {
                    generalize (Fappli_IEEE.fexp_correct). prec emax).
                    intros.
                    unfold Fcore_FLX.Prec_gt_0, prec, emax in *.
                    assert (0 < 24)%Z by lia.
                    specialize (H0 H1); clear H1.
                    unfold prec, e
                    
                    compute; reflexivity.
                  }
                  specialize (Hsne H0); clear H0.
                  SearchAbout Exp_not_FTZ.
                  assert (Exp_not_FTZ (FLT_exp prec emax)).
                  unfold prec, emax.
                  lazy.
                  intros.
                  cbv beta zeta delta [Exp_not_FTZ FLT_exp generic_format Fcore_Raux.Ztrunc] in Hsne.
                  lazy in Hsne.
                  SearchAbout (Exp_not_FTZ).
                  Print Fcore_FLT.

                  generalize (forall P, Fcore_FLT.FLT_exp_valid prec emax P).
                  Print Valid_exp.
                  Print generic_format.
                  simpl in e0.
                  Pr
                  specialize (Hsne 
                  
                  
              split.
              - simpl.
             *)
          Admitted.

          idtac.

          assert (isFloatConstValid f10) by auto.
          assert (isFloatConstValid float_one) by auto.
          
          replace (isFloatConstValid f10) with True by (lazy; reflexivity).
          replace (isFloatConstValid float_one) with True by auto.
          assert (isFloatConstValid f0) by admit.
          assert (isFloatConstValid f) by admit.
         
          unfold plusResultValidity, minusResultValidity, multResultValidity.
          Opaque Fappli_IEEE.Bminus Fappli_IEEE.Bmult Fappli_IEEE.Bplus.
          simpl. rewrite H0. rewrite H.
          simpl.
          (* relate isFloatConstValid to being between max float and min float *)

          (* isFloatConstValid lemmas from Gregory's whiteboard *)
          Lemma isFloatConstValid_Bplus : forall a b : float,
              Basics.impl (exists ra,
                 F2OR a = Some ra /\
                 exists rb, F2OR b = Some rb /\
                       (floatMin <=  ra + rb <= floatMax \/
                        floatMin <= -(ra + rb) <= floatMax \/
                        ra + rb = 0))%R
              (isFloatConstValid (Fappli_IEEE.Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                   custom_nan Fappli_IEEE.mode_NE a b)).
          Proof.
            (* again, unsure how exactly to go about proving this *)
          Admitted.

          Lemma isFloatConstValid_Bminus : forall a b : float,
              Basics.impl (exists ra,
                 F2OR a = Some ra /\
                 exists rb, F2OR b = Some rb /\
                       (floatMin <=  ra - rb <= floatMax \/
                        floatMin <= -(ra - rb) <= floatMax \/
                        ra - rb = 0))%R
              (isFloatConstValid (Fappli_IEEE.Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                   custom_nan Fappli_IEEE.mode_NE a b)).
          Proof.
            (* again, unsure how exactly to go about proving this *)
          Admitted.

          Check Fappli_IEEE.Bmult_correct.
          (* look at bound.v to see how to change - make the others like this  *)
          Lemma isFloatConstValid_Bmult : forall a b : float,
              Basics.impl (exists ra,
                 F2OR a = Some ra /\
                 exists rb, F2OR b = Some rb /\
                       (floatMin <= (ra * rb) /\
                        floatMax >= (ra * rb) * (1 + error)) \/
                       (floatMin <= - (ra * rb) /\
                        floatMax >= - (ra * rb) * (1 - error)))%R
              (isFloatConstValid (Fappli_IEEE.Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax
                                                   custom_nan Fappli_IEEE.mode_NE a b)).
          Proof.
            (* again, unsure how exactly to go about proving this *)
          Admitted.

          idtac.

          rewrite <- isFloatConstValid_Bplus.
          rewrite <- isFloatConstValid_Bminus.
          rewrite <- isFloatConstValid_Bmult.

          apply isFloatConstValid_F2OR in H10.
          apply isFloatConstValid_F2OR in H11.

          assert (isFloatConstValid f) by admit.
          assert (isFloatConstValid f0) by admit.
          fwd.
          assert (x5 = FloatToR x) by admit.
          assert (x4 = FloatToR x0) by admit.
          
          
          show_value floatMin.
          show_value floatMax.
          show_value error.
          subst.

          (*
          assert (FloatToR x0 <  100000)%R by admit.
          assert (FloatToR x0 > -100000)%R by admit.
          assert (FloatToR x  <  100000)%R by admit.
          assert (FloatToR x  > -100000)%R by admit.
           *)

          assert (FloatToR x0 <  100000)%R by admit.
          assert (FloatToR x0 > 1/10)%R by admit.
          assert (FloatToR x  <  100000)%R by admit.
          assert (FloatToR x  > 1/10)%R by admit.


          (* options for solving this problem:
             1. Change semantics so inf/nan is not a stuchk state. Requires changes to Vignesh's code
             2. Add constructs to language such as "safe_plus a b" returns true if (a + b) guaranteed to be a valid float, and false otherwise.
             3. Just add bounds to the variables. We'll need to do this in any case. This is our approach for now. *)

          destruct H14 as [?|[?|?]]; destruct H15 as [?|[?|?]]; try (z3 solve; admit).
          idtac.

          (* trying to figure out why it still isn't working *)
          left.
          repeat split; try (z3 solve; admit).
          exists (FloatToR x). split; [auto|].
          eexists. split; [reflexivity|].
          left. assert (FloatToR float_one = 1)%R by admit.
          try (z3 solve; admit).

          Locate Bmult_correct.
          Check Fappli_IEEE.Bmult_correct.

          unfold float_mult.
          
          eexists. split.

          

          Print float_mult.
          SearchAbout Fappli_IEEE.Bmult.
          Check Fprop_relative.relative_error.
          (* Bmult_correct *)
          reflexivity.
          
          repeat split.

          z3 solve.
          Focus 9.

          (* we need to prove this theorem, then go back and clean things up
             then, finally, we need to figure out what's left to do *)
          z3 solve.

          left.

          repeat split; try tauto. Focus 9.
          rewrite <- isFloatConstValid_Bplus.
Print Basics.impl.
          

          isFloatConstValid a <-> exists ra, F2OR a = Some ra.
          
          Print f0.

          left.
          

            (* this is as far as Gregory and I got on 8/20 *)
          simpl maybe_lt0.
          unfold maybe_lt0.
        
        split.
        { intros; eexists; split; [ reflexivity | ].
          admit. }
        { Print maybe_ge0.
          Print fwp.
        
        simpl.
      
      
      
      eapply (inject_var "v").
      charge_intro.
      eapply lforallL.

      instantiate (1 := (fstate_get_rval "a" (fun a fs => a = 0 \/ (x + a) < 10)%R)).
      cbv zeta.
      simpl fwp.
      eapply lequiv_rewrite_left.
      { crunch_embeds. }
      (* todo find a cbv list to control reduction, leaving as much abstracion as possible *)
      (* maybe need two versions of bound_term: one for conjunct-of-disjuncts and one for disjunct-of-conjuncts *)

      Lemma limpl_lentail_limpl :
        forall A B C D,
          (C |-- A) -> (B |-- D) ->
          (A -->> B |-- C -->> D).
      Proof.
        tlaIntuition.
      Qed.

      idtac.
      rewrite <- curry.
      rewrite <- curry.

      apply lexistsL.
      intro.
      rewrite landC.

      tlaRevert.
      rewrite <- curry.
      
      apply limpl_lentail_limpl.
      (* we know the lookups will succeed *)

      Lemma varIsFloat_fstate_lookup :
        forall (v : Var) (fs : fstate) ivs G X,
          (G |-- preVarIsFloat v) ->
          (G |-- Embed (fun x1 _ : state => vmodels ivs x1 fs)) ->
          (exists v', In (v,v') ivs) ->          
          (forall res, fstate_lookup fs v = Some res -> G |-- X) ->
          G |-- X.
      Proof.
        tlaIntuition.
        specialize (H _ H3). fwd.
        specialize (H0 _ H3).
        assert (exists Res, fstate_lookup fs v = Some Res).
        admit.
        fwd.
        eapply H2; eauto.
      Qed.

      idtac.

      eapply varIsFloat_fstate_lookup with (v := "a").
      charge_assumption.
      charge_assumption.
      simpl. eauto.

      intros.
      repeat (rewrite H).

      (* do this again for v, and then we can simplify the lift2 and things *)
      eapply varIsFloat_fstate_lookup with (v := "v").
      charge_assumption.
      charge_assumption.
      simpl. eauto.
      intros.
      repeat (rewrite H0).

      unfold lift2.

      eapply lexistsR.

      charge_split; [apply PropF_tauto; reflexivity|].

      charge_split.
      {
        charge_intros.
        eapply lexistsR.
        charge_split; [apply PropF_tauto; reflexivity|].
        Lemma fstate_lookup_isVarValid :
          forall v vs  fs,
            (exists (v' : Var), In (v,v') vs) ->
            Embed (fun rs _ : state => vmodels vs rs fs) //\\
                  preVarIsFloat v |--
                  PropF (isVarValid v fs).
        Proof.
        Admitted.

        idtac.

        charge_left.

        charge_split; [apply PropF_tauto; tauto|].

        charge_intros.
        
        Lemma fstate_set_fstate_get_rval :
          forall fs v f (P : R -> fstate -> Prop) r,
            F2OR f = Some r ->
            P r (fstate_set fs v f) ->
            fstate_get_rval v P (fstate_set fs v f).
        Proof.
          intros.
          unfold fstate_get_rval;
            rewrite <- fstate_lookup_update_match;
            eauto.
        Qed.

        breakAbstraction.
        intros.
        fwd.
        eapply fstate_set_fstate_get_rval.
        eauto.
        lra.
      }
      {
        charge_split.
        {
          charge_intros.
          eapply lexistsR.
          charge_split; [apply PropF_tauto; reflexivity|].
          charge_left.
          charge_split.
          {
            rewrite <- fstate_lookup_isVarValid.
            charge_tauto.
            compute; eauto.
          }
          {
            charge_intros.
            breakAbstraction.
            intros. fwd.
            eapply fstate_set_fstate_get_rval; [eauto|].
            unfold bound_fexpr in H5.
            simpl fexpr_to_NowTerm in H5.

            (* idea: need a "pull out one possible bound" tactic when unfolding bound_term
               apply it after solving each goal to "get" the next goal *)

            unfold bound_term in H5.

            (* janky infrastructure for working with lists as sets *)
            Definition isSubsetOf {T : Type} (X X' : list T) :=
              forall (x : T), In x X -> In x X'.

            Definition FilterBad {T : Type} (fs : fstate) (X X': list T) :=
              isSubsetOf X X'.

              (* Something like
                   FilterBad X X' st -> FilterBad Y Y' st ->
                   AnyOf (fun P => P) (cross X Y) st -> AnyOf (fun P => P) (cross X' Y') st 
               *)

            unfold maybe_ge0 in H5.

            (* the following lemmas might not actually be useful *)
            Transparent ILInsts.ILFun_Ops.
            cbv beta iota zeta delta
                [cross map flat_map
                       combineTriplePlus combineTripleMinus combineTripleMult
                       simpleBound simpleBound2 simpleBound3 simpleBound4 simpleBound5 simpleBound6 simpleBound7 simpleBound8 simpleBound9 simpleBound10
                       lb ub premise c_lt c_gt c_le c_ge lofst a_mult a_plus a_minus
                       Arithable_Lift Comparable_Lift Arithable_R fstate_lookup_force
                       Comparable_R Comparable_Applicative Fun.Applicative_Fun Arithable_Applicative
                       Applicative.ap Applicative.pure app land lor ILInsts.ILFun_Ops ILogicOps_Prop] in H5.

            unfold fstate_lookupR in *.
            unfold fstate_lookup_force in *.
            generalize dependent (fstate_lookup x0 "a").
            generalize dependent (fstate_lookup x0 "v").
            intros; subst.

            Lemma realMatch_F2OR_FloatToR :
              forall (f f' : float) (r1 r2 : R), F2OR f = Some r1 -> FloatToR f' = r1 -> F2OR f' = Some r2 ->
                                            FloatToR f = r1.
            Proof.
              intros.
              unfold FloatToR, F2OR in *.
              destruct f; try congruence; inv_all; rewrite <- H; reflexivity.
            Qed.
            idtac.
            generalize (realMatch_F2OR_FloatToR _ _ _ _ (eq_sym H1) H7 H8). intro Hrew_a.
            generalize (realMatch_F2OR_FloatToR _ _ _ _ (eq_sym H11) H9 H10). intro Hrew_v.
            unfold floatMin, error, floatMax, custom_prec, custom_emax, prec, emax, custom_emin, emin, f10 in H5.
            Time repeat match goal with
                   | H : AnyOf _ |- _ => destruct H
                                                
                   end;
            repeat match goal with
            | H: context[Fappli_IEEE.B2R ?x1 ?x2 ?x3] |- _ => 
              let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2 in H
                   end;
            repeat match goal with
                   | H : context[Fcore_Raux.bpow ?x1 ?x2] |- _ =>
                                 let X2 := eval compute in (Fcore_Raux.bpow x1 x2) in
                                     change (Fcore_Raux.bpow x1 x2) with X2 in H
                                 end; try (z3 solve; admit).
          }
        }
        {        
            (*
            repeat rewrite app_nil_r in H5.
            unfold app in H5.
            unfold cross in H5.
            unfold cross in H5.
            unfold cross, flat_map, map in H5.
            unfold combineTripleMult in H5.

            (* (map (thingToPred) (cross crossfn l1 l2))
               thus we need crossfun to be present in our lemma as well. *)

            (* we can generalize fstate into some other type T' of course *)
            Lemma FilterBad_AnyOf_cross :
              forall {T : Type} (X X' Y Y' : list T) (st : fstate)
                (t2prop : fstate -> T -> Prop) (combiner : T -> T -> list T),
                FilterBad st X X' -> FilterBad st Y Y' ->
                AnyOf (map (t2prop st) (cross combiner X Y)) -> AnyOf (map (t2prop st) (cross combiner X' Y')).
            Proof.
              intros.
              fwd.
              unfold FilterBad, isSubsetOf in *.

              Lemma FilterBad_cross1 :
                forall {T : Type} (X X' Y  : list T) (combiner : T -> T -> list T),
                  isSubsetOf X X' ->
                  isSubsetOf (cross combiner X Y) (cross combiner X' Y).
              Proof.
                induction X.
                - simpl. unfold isSubsetOf. intuition.
                - intros. simpl.
                  unfold isSubsetOf in *.
                  intros.
                  SearchAbout (In _ (_ ++ _)).
                  apply Coqlib.in_app in H0.
                  destruct H0.
                  + assert (In a X').
                    { apply H. constructor. reflexivity. }
                    
                    (* need a lemma saying:
                       - if a is in X'
                                    - then everything that's in flat_map (combiner a) Y
                                                                - will be in cross combiner X' Y *)
                    Lemma cross_in:
                      forall {T : Type} (X Y : list T) (combiner : T -> T -> list T)
                        (a x : T),
                        In a X -> In x (flat_map (combiner a) Y) ->
                        In x (cross combiner X Y).
                    Proof.
                      induction Y.
                      - simpl. intros. contradiction.
                      - simpl. intros.
                        apply Coqlib.in_app in H0.
                        destruct H0.
                        + destruct X.
                          * simpl in *. contradiction.
                          * simpl.
                            apply Coqlib.in_app.
                      
 
 
              
              (* we must first prove that the cross generates a subset *)
              Lemma FilterBad_cross :
                forall {T : Type} (X X' Y Y' : list T) (combiner : T -> T -> list T),
                  isSubsetOf X X' -> isSubsetOf Y Y' ->
                  isSubsetOf (cross combiner X Y) (cross combiner X' Y').
              Proof.
                induction X.
                - intros.
                  simpl.
                  unfold isSubsetOf.
                  intuition.
                - intros.
                  simpl.
                  destruct Y.
                  + simpl.
                    eapply IHX; eauto.
                    admit.
                  + simpl. 
                  (* isSubsetOf (x :: X) X' -> isSubsetOf X X' *)
                  (* isSubsetOf (X ++ X') Y -> isSubsetOf *)
                  unfold flat_map.

                  indection Y.
                
                intros.
                  
              
              intuition.
                
              
              admit.
             *)
          (*
            Lemma F2OR_FloatToR' :
              forall f f' r,
                F2OR f = Some r -> F2OR f' = Some r -> FloatToR f = FloatToR f'.
            Proof.
              intros.
              unfold F2OR, FloatToR in *.
              destruct f; destruct f'; try congruence.
            Qed.

            Transparent ILInsts.ILFun_Ops.
            Ltac crunch_goals_post :=
              unfold land in *;
              simpl in *;
              fwd;
              unfold lofst in *;
              simpl in *;
              repeat match goal with
                     | H: context[Fcore_defs.F2R ?X] |- _ =>
                       let Y := constr:(@Fcore_defs.F2R Fappli_IEEE.radix2 X) in
                       let Y' := eval compute in Y in
                         change Y with Y' in H
                     end;
              unfold fstate_lookup_force in *;
              unfold plusResultValidity, minusResultValidity in *;
              simpl eval_NowTerm in *;
              repeat
                match goal with
                | H: _ = _ |- _ => rewrite H in *
                end;
              let X := eval compute in floatMax in change floatMax with X in *;
                let X := eval compute in floatMin in change floatMin with X in *;
                  let X := eval compute in error in change error with X in *;
                    unfold lift2 in *;
                    unfold fstate_lookupR in *;
                    repeat match goal with
                           | H: fstate_lookup ?fs ?v = Some ?f |- _ =>
                             rewrite H in *
                           end;
                    repeat match goal with
                           | H0: F2OR ?f = Some ?r, H1: FloatToR ?f = ?r' |- _ =>
                             lazymatch r with
                           | r' => fail
                           | _ => generalize (F2OR_FloatToR _ _ _ H0 H1); intro; subst
                           end
            end;
            
            repeat match goal with
                   | H1 : Some ?r1 = F2OR ?f1, H2: F2OR ?f2 = Some ?r1 |- _ =>
                     symmetry in H1;
                       generalize (F2OR_FloatToR' _ _ _ H1 H2);
                       intro
                   end.    
                    
            admit.
            (*(repeat match goal with
                   | H: ?A \/ ?B |- _=> destruct H
                    end); crunch_goals_post ; try (z3 solve; admit).*)
          }
        }
        { *)
          idtac.  
          breakAbstraction.
          intros.
          fwd.
          (* assertions relating stream elements to variables (provable) *)
          assert (FloatToR res = Stream.hd tr "a") by admit.
          assert (FloatToR res0 = Stream.hd tr "v") by admit.

          (* assertions bounding values of variables (hopefully provable later) *)
          assert (Stream.hd tr "a" >= 1)%R by admit.
          assert (Stream.hd tr "a" <= 101)%R by admit.
          assert (Stream.hd tr "v" >= 1)%R by admit.
          assert (Stream.hd tr "v" <= 101)%R by admit.
                    
           repeat match goal with
                     | |- context[Fcore_defs.F2R ?X] =>
                       let Y := constr:(@Fcore_defs.F2R Fappli_IEEE.radix2 X) in
                       let Y' := eval compute in Y in
                         change Y with Y'
                     end;
              unfold fstate_lookup_force in *;
              unfold plusResultValidity, minusResultValidity in *;
              simpl eval_NowTerm in *.
              repeat
                match goal with
                | H: _ = _ |- _ => rewrite H in *
                end;
              let X := eval compute in floatMax in change floatMax with X in *;
                let X := eval compute in floatMin in change floatMin with X in *;
                  let X := eval compute in error in change error with X in *.
              unfold lofst.
              unfold lift2.

              idtac.
              unfold float_one, float_plus, float_minus, float_mult, nat_to_float.
              unfold floatMin, error, floatMax, custom_prec, custom_emax, prec, emax, custom_emin, emin, f10.
              unfold plusResultValidity, minusResultValidity, multResultValidity.
              unfold isFloatConstValid.
              Import Fappli_IEEE_extra.
              repeat match goal with
                     | |- context[BofZ ?x1 ?x2 ?x3 ?x4 ?x5] =>
                       idtac x5;
                       let X := constr:(BofZ x1 x2 x3 x4 x5) in
                       let X' := constr:(concretize_float X) in
                       let X'' := eval lazy in X' in
                           replace X with X''; [|rewrite <- concretize_float_correct; lazy; reflexivity]
                     end.
              unfold eval_NowTerm.
              simpl eval_NowTerm.
              unfold custom_nan.
              unfold lift2.
              rewrite H.
              Lemma is_finite_match :
                forall (f : float),
                  match f with
                  | Fappli_IEEE.B754_zero _ => True
                  | Fappli_IEEE.B754_infinity _ => False
                  | Fappli_IEEE.B754_nan _ _ => False
                  | Fappli_IEEE.B754_finite _ _ _ _ => True
                  end <-> Fappli_IEEE.is_finite _ _ f = true.
              Proof.
                destruct f; intros; intuition.
              Qed.
              idtac.
              rewrite -> (is_finite_match (Fappli_IEEE.Bmult custom_prec custom_emax custom_precGt0
         custom_precLtEmax Floats.Float32.binop_pl Fappli_IEEE.mode_NE res
         (Fappli_IEEE.B754_finite 24 128 false 8388608 (-23) eq_refl))).
              (* begin arbitary branch picks to reduce formula siZe *)
              (* begin experimental new section *)
              idtac.
              Print Fappli_IEEE.B2R.
              Print Fcore_defs.F2R.
              Print Fcore_defs.Float.
              right.
              
              Print floatToReal.
              right.
              left.

              rewrite -> is_finite_match.
              rewrite -> is_finite_match.
              split; [auto|].
              repeat split.

              Focus 12.
              psatz R.

              (* end experimental new section *)

              left.
              rewrite -> is_finite_match.
              rewrite -> is_finite_match.
              split; [auto|].

              Lemma multRounding_finite :
                forall (f1 f2 : float) (r1 r2 : R),
                  Some r1 = floatToReal f1 ->
                  Some r2 = floatToReal f2 ->
                  (Rbasic_fun.Rabs
                     (Fcore_generic_fmt.round Fappli_IEEE.radix2
                                              (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                              (Fappli_IEEE.round_mode Fappli_IEEE.mode_NE)
                                              (Fappli_IEEE.B2R custom_prec custom_emax f1 *
                                               Fappli_IEEE.B2R custom_prec custom_emax f2)) <
                   Fcore_Raux.bpow Fappli_IEEE.radix2 custom_emax)%R ->
                  Fappli_IEEE.is_finite custom_prec custom_emax
                                        (Fappli_IEEE.Bmult custom_prec custom_emax custom_precGt0
                                                           custom_precLtEmax custom_nan Fappli_IEEE.mode_NE f1 f2) = true.
              Proof.
                intros.
                generalize (multRoundingTruth2 f1 f2 r1 r2 H H0 H1); intro Hmrt.
                destruct Hmrt.
                assumption.
              Qed.

              idtac.

              repeat split.
              admit.
              Focus 5.
              eapply multRounding_finite.
              instantiate (1 := (Stream.hd tr "a")).
              admit (* should be easily provable*).
              reflexivity.
              
              (* good for reducing B2Rs that can be reduced (those with concrete values) *)
              (*
              match goal with
              | |- context[Fappli_IEEE.B2R ?x1 ?x2 ?x3] =>
                match x3 with
                | Fappli_IEEE.B754_zero _ _ _ => 
                  let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2
                | Fappli_IEEE.B754_finite _ _ _ _ _ _ => 
                  let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2
                end
              end.
             *)
              
              eapply multRoundingTruth with (lb1 := (1)%R) (ub1 := (101)%R).
              instantiate (1 := (Stream.hd tr "a")). admit.
              lazy. reflexivity.
              Lemma Rge_le :
                forall (r1 r2 : R),
                  (r1 >= r2)%R -> (r2 <= r1)%R.
              Proof.
                intros.
                lra.
              Qed.
              idtac.
              Focus 2.
              apply Rge_le in H11.
              apply H11.
              Focus 2.

              Ltac compute_concrete_B2R :=
                match goal with
                | |- context[Fappli_IEEE.B2R ?x1 ?x2 ?x3] =>
                  match x3 with
                  | Fappli_IEEE.B754_zero _ _ _ => 
                    let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2
                  | Fappli_IEEE.B754_finite _ _ _ _ _ _ => 
                    let X2 := eval lazy in (Fappli_IEEE.B2R x1 x2 x3) in change (Fappli_IEEE.B2R x1 x2 x3) with X2
                  end
                end.

              apply Req_le.
              reflexivity.
              Focus 2.
              apply H12.
              Focus 2.
              apply Req_le; reflexivity.
              left.
              repeat split.
              unfold floatMin. lazy. psatz R.
              lra.
              lra.
              unfold error, floatMax.
              lazy.
              lra.

              (* getting bounds using an external tool? *)
              (* assert all bounds at beginning *)
              (* eventually we need bounds for subnormals *)
              lra.
              lra.
              lra.
              lra.
              admit.
              lra.
              lra.
              lra.

              (* analogues to multRounding_finite *)
              Lemma plusRounding_finite :
                forall (f1 f2 : float) (r1 r2 : R),
                  Some r1 = floatToReal f1 ->
                  Some r2 = floatToReal f2 ->
                  (Rbasic_fun.Rabs
                     (Fcore_generic_fmt.round Fappli_IEEE.radix2
                                              (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                              (Fappli_IEEE.round_mode Fappli_IEEE.mode_NE)
                                              (Fappli_IEEE.B2R custom_prec custom_emax f1 +
                                               Fappli_IEEE.B2R custom_prec custom_emax f2)) <
                   Fcore_Raux.bpow Fappli_IEEE.radix2 custom_emax)%R ->
                  Fappli_IEEE.is_finite custom_prec custom_emax
                                        (Fappli_IEEE.Bplus custom_prec custom_emax custom_precGt0
                                                           custom_precLtEmax custom_nan Fappli_IEEE.mode_NE f1 f2) = true.
              Proof.
                intros.
                generalize (plusRoundingTruth2 f1 f2 r1 r2 H H0 H1); intro Hprt.
                destruct Hprt.
                assumption.
              Qed.

              Lemma minusRounding_finite :
                forall (f1 f2 : float) (r1 r2 : R),
                  Some r1 = floatToReal f1 ->
                  Some r2 = floatToReal f2 ->
                  (Rbasic_fun.Rabs
                     (Fcore_generic_fmt.round Fappli_IEEE.radix2
                                              (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)
                                              (Fappli_IEEE.round_mode Fappli_IEEE.mode_NE)
                                              (Fappli_IEEE.B2R custom_prec custom_emax f1 -
                                               Fappli_IEEE.B2R custom_prec custom_emax f2)) <
                   Fcore_Raux.bpow Fappli_IEEE.radix2 custom_emax)%R ->
                  Fappli_IEEE.is_finite custom_prec custom_emax
                                        (Fappli_IEEE.Bminus custom_prec custom_emax custom_precGt0
                                                            custom_precLtEmax custom_nan Fappli_IEEE.mode_NE f1 f2) = true.
              Proof.
                intros.
                generalize (minusRoundingTruth2 f1 f2 r1 r2 H H0 H1); intro Hmrt.
                destruct Hmrt.
                assumption.
              Qed.

              (* need lemma relating is_finite to floatToReal *)
              Lemma isFinite_floatToReal :
                forall (f : float),
                  Fappli_IEEE.is_finite _ _ f = true -> exists x, (Some x = floatToReal f)%R.
              Proof.
                destruct f; intros.
                - simpl. eexists. reflexivity.
                - simpl in H. congruence.
                - simpl in H. congruence.
                - simpl. eexists. reflexivity.
              Qed.

              (* goal 2 is unprovable here... *)

              generalize (isFinite_floatToReal (Fappli_IEEE.Bmult 24 128 custom_precGt0 custom_precLtEmax
        Floats.Float32.binop_pl Fappli_IEEE.mode_NE res
        (Fappli_IEEE.B754_finite 24 128 false 8388608 (-23) eq_refl))); intro Hiff2r.
              destruct Hiff2r.
              eapply multRounding_finite.
              instantiate (1 := (Stream.hd tr "a")). admit.
              reflexivity.
              eapply multRoundingTruth.
              instantiate (1 := (Stream.hd tr "a")). admit.
              reflexivity.

              Focus 2.
              instantiate (1 := 1%R).
              lra.
              Focus 3.
              instantiate (1 := 101%R). lra.
              Focus 2.
              apply Req_le. lazy. reflexivity.
              Focus 2.
              apply Req_le. lazy. reflexivity.
              unfold error, floatMin, floatMax, emax, emin.
              unfold custom_prec, custom_emax, custom_emin.
              unfold emin, emax, prec.
              lazy.
              lra.
              Focus 2.
              psatz R.

              Focus 2.
              eapply H15.
              
              
              SearchAbout floatToReal Fappli_IEEE.Bmult.
              Focus 2. instantiate (1 := (Stream.hd tr "v")). admit (*for later *).
              
              unfold floatToReal.
              lazy.
              lazy.
              
              admit.
              assert (Stream.hd tr "a" >= 1)%R by admit.
              assert (Stream.hd tr "a" <= 101)%R by admit.
              idtac.
              try( z3 solve; admit).
              assert (Stream.hd tr "a" >= 1)%R by admit.
              assert (Stream.hd tr "a" <= 101)%R by admit.
              try( z3 solve; admit).
              admit.
              lra.
              admit.

              assert (Stream.hd tr "v" >= 1)%R by admit.
              assert (Stream.hd tr "v" <= 101)%R by admit.
              assert (Stream.hd tr "a" >= 1)%R by admit.
              assert (Stream.hd tr "a" <= 101)%R by admit.
              try (z3 solve; admit).
              
              unfold isVarValid.
              unfold error, floatMax, floatMin, custom_emax, custom_emin, emax, emin.
              unfold custom_prec, prec.
              lazy.
              clear.
              assert (1 = 1)%R by lra.
              left. split.
              split.
              clear.
              z3 solve_dbg.
              cbv beta zeta delta [Fappli_IEEE.radix2 Fcore_Raux.bpow].
              
              z3 solve_dbg.
              apply H11.
              rewrite Rle_ge in H11.
              Check multRoundingTruth.
              instantiate (1 := (-100)%R).
              left.
              split. split. z3 solve_dbg.
              z3 solve_dbg.
              z3 solve_dbg.
              Focus 5.
              compute.
              
              apply relErrorBasedOnFloatMinTruthMult.
              
              admit.
              reflexivity.
              simpl.
              cbv beta zeta iota delta [Fcore_defs.F2R Fappli_IEEE.B2R].
              cbv beta zeta iota delta [Fcore_Raux.Z2R Fcore_defs.Fnum Fcore_defs.Fexp].
              cbv beta zeta iota delta [Fcore_Raux.P2R Fcore_Raux.bpow Fappli_IEEE.radix2].
              cbv beta zeta iota delta [Fcore_Raux.Z2R Z.pow_pos Fcore_Zaux.radix_val].
              cbv beta zeta iota delta [Pos.iter Z.mul].
              cbv beta zeta iota delta [Fcore_generic_fmt.round Fcore_FLT.FLT_exp Fcore_generic_fmt.Znearest].
              cbv beta zeta iota delta [Fcore_defs.F2R Fcore_Raux.P2R].
              cbv beta zeta iota delta [Fcore_defs.Fnum].

              
              
              
              cbv beta zeta iota delta [Fcore_generic_fmt.scaled_mantissa].
              cbv beta zeta iota delta [Fcore_Raux.Z2R Fcore_Raux.Rcompare].






              lazy.
              compute.
              
              
              
              
              split.

              idtac.
              unfold custom_prec, custom_emax.
              
              (* res and res0 are quantified but our math is blocking on them
                 what can we do to get them to compute so that we can evaluate the
                 match statements that are matching on them? *)
              admit.
              rewrite <- concretize_float_correct. lazy.
              Focus 2.
              idtac.
              Check concretize_float_correct.

              Eval lazy in (concretize_float ((Fappli_IEEE_extra.BofZ 24 128 custom_precGt0 custom_precLtEmax
                 (Z.of_nat 1)))).
              unfold custom_precGt0.
              

              Eval compute in (concretize_float (Fappli_IEEE.Bplus 24 128 custom_precGt0 custom_precLtEmax custom_nan
        Fappli_IEEE.mode_NE
        (Fappli_IEEE.Bmult 24 128 custom_precGt0 custom_precLtEmax custom_nan
           Fappli_IEEE.mode_NE res
           (Fappli_IEEE_extra.BofZ 24 128 custom_precGt0 custom_precLtEmax
              (Z.of_nat 1))) res0)).
              
              match goal with
                     | |- context[Fappli_IEEE.Bplus ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8] => idtac "HI THERE"; idtac x1;
                       let X' := eval lazy in (Fappli_IEEE.Bplus x1 x2 x3 x4 x5 x6 x7 x8) in
                           change (Fappli_IEEE.Bplus ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) with X'
                     end.
              Eval lazy in 
                         

              z3 solve_dbg.

              Unfold Lofst in *;
              simpl in *;
              repeat match goal with
                     | |- context[Fcore_defs.F2R ?X] =>
                       let Y := constr:(@Fcore_defs.F2R Fappli_IEEE.radix2 X) in
                       let Y' := eval compute in Y in
                         change Y with Y'
                     end.


              Lemma crunch_and :
                forall (P P' Q Q' : Prop),
                  (P' -> P) -> (Q' -> Q) ->
                  P' /\ Q' -> P /\ Q.
              Proof.
                intuition.
              Qed.

              

              Definition z3proved : Prop -> Prop :=
                fun _ => True.

              Lemma True_expand1 : forall (P : Prop),
                  P <-> True /\ P.
              Proof. intuition. Qed.

              Lemma True_expand2 : forall (P : Prop),
                  P <-> P /\ True.
              Proof. intuition. Qed.

              Lemma False_expand1 : forall (P : Prop),
                  P <-> False \/ P.
              Proof. intuition. Qed.

              Lemma False_expand2 : forall (P : Prop),
                  P <-> P \/ False.
              Proof. intuition. Qed.

              unfold multResultValidity.
              unfold lift2.
              simpl eval_NowTerm.
              rewrite H.

              Lemma Lcut :
                forall (P P' : Prop),
                  (P' -> P) -> P' -> P.
              Proof.
                tauto.
              Qed.

              idtac.

              eapply Lcut.
              rewrite <- True_expand1.
              
              eapply True_expand1.
              
              match goal with
              | |- ?X =>
                match X with
                | True \/ ?B => eapply 
                end
              end
              
              try (
                  match goal with
                  | contex[
                  end
                ).

              rewrite H0.
              (* need case for isVarValid *)
              
              idtac.

              (* need to do context cleanup first in order to set up relationships between res/0 and x/0 *)
              Ltac crunch_logic :=
                progress repeat
                         match goal with
                         | |- True /\ ?R => eapply True_expand1
                         | |- ?L /\ True => eapply True_expand2
                         | |- False \/ ?R => eapply False_expand1
                         | |- ?L \/ False => eapply False_expand2
                         | |- ?L /\ ?R => eapply crunch_and
                         | |- ?L \/ ?R => eapply crunch_or
                         end.

              eapply crunch_or.
              
              intro.

              Unset Printing Notations.
              idtac.
              
              
              crunch_logic.

              rewrite <- True_expand1.
              rewrite <- False_expand2.
              
              match goal with
              | |- context[?X] =>
                match X with
                | context[True /\ ?Y] =>
                  idtac "doing it";
                  replace X with Y by apply True_expand1
                end
              end.
              
              match goal with
              | |- context[True /\ ?X] => idtac;
                                      rewrite (True_expand1 X)
                       (*replace (True /\ X) with X by apply True_expand1*)
              end.
              
              repeat match goal with
                     | |- context[True /\ ?X] =>
                        replace (True /\ X) with X by apply True_expand1
                     | |- context[?X /\ True] =>
                       setoid_rewrite (True_expand2 X)
                     | |- context[False \/ ?X] =>
                       setoid_rewrite (False_expand1 X)
                     | |- context[?X \/ False] =>
                       setoid_rewrite (False_expand2 X)
                     end.
                       

              repeat match goal with
                     | |- context[?X] =>
                       match X with
                       | context[_/\_] => idtac "found or"; fail
                       | context[_\/_] => idtac "found or"; fail
                       | _ =>
                         idtac "GOOD GOAL " X;
                         assert (z3proved X) by auto (*assert X; [assert (z3Proved X) by auto | try (z3 solve_dbg; admit)]*)
                       end
                     end.
               

        
              {
                cbv beta.
          intuition.
      simpl. intuition.
      constructor. intuition congruence.
      constructor.
    }
    {
      simpl. intuition eauto.
    }

    (* copied over from "main goal" section of previous theorem *)
    eapply lforallL.
    instantiate (1 := (fun fst => exists f, fstate_lookup fst "x" = Some f /\ exists r, F2OR f = Some r /\ (r > 0)%R)).
    simpl fwp.
    cbv zeta.
    eapply lequiv_rewrite_left.
    { crunch_embeds. }
    apply lexistsL.
    intros.
    charge_intros.
    etransitivity.
    
    admit. }
  {
  (* TODO: prove thorem about always-enabledness of oembed_fcmd
     (true of any semantics embedded using oembedStep_maybenone, provided
     that any state has some other state it steps to *)
    admit. }
  Qed.

(* TODO: repeat the preceding exercise (proving correctness and enabledness) for velocity shim
   then, for height shim *)

(* sample abstractor outputs *)
(* this section now defunct... *)
(* Bmult_correct - theorem we want! *)
(*
Section fwp.
  Parameter st : state.
  Parameter postcond : state -> Prop.
  
  (* discrete invariant: controller never changes x *)
  (*Fact fwp_propcontrol : forall (P : (fwp proportional_controller postcond proportional_controller_ivs st)), False.*)
  Fact fwp_propcontrol : (fwp proportional_controller postcond proportional_controller_ivs st).
  Proof.
    intros.
    cbv beta iota delta [fwp proportional_controller].
    simpl.
    Print bound.isVarValid.
    
    unfold Semantics.eval_comp.
    simpl.


    (* TODO may need to bolt on continuation support *)
    Unset Ltac Debug.
    Ltac abstractor_cleanup P :=
      let rec cleanup P :=
          match P with
          | AnyOf ?P1 :: nil => apply AnyOf_singleton in P; abstractor_cleanup P
          | AnyOf ?PS => cleanup_list PS
          | ?P1 \/ ?P2 => abstractor_cleanup P1; abstractor_cleanup P2
          | True /\ ?P1 => apply and_True_snip1 in P; abstractor_cleanup P
          | _ => idtac
    end
    with cleanup_list ls :=
      match ls with
      | ?P :: ?PS => cleanup P; cleanup_list PS
      | nil => idtac
      end
      in
        let t := type of P in
        cleanup t.

    (* use entailment |-- and -|-
       also want to convert (state -> Prop) to Formula by distributing embed.
       test on "just increment x" controller, where safety is x > 0 
       prove bi entailment of result formula *)

    Ltac abstractor_cleanup_goal :=
      match goal with
      | |- ?P => abstractor_cleanup P
      end.

    match goal with
    | |- _ \/ _ => idtac
    end.

    abstractor_cleanup_goal.

    
    Unset Ltac Debug.

              Lemma silly_AnyOf :
                AnyOf (True :: nil) -> False.
              Proof.
                intro.
                apply AnyOf_singleton in H.
                Focus 2.
                Check AnyOf_singleton.
                rewrite AnyOf_singleton; reflexivity.
                apply AnyOf_singleton.
                abstractor_cleanup H.
              
              abstractor_cleanup P.

              repeat (
        match P with
        | 
        end
        ).
  Abort.
  
Fact fwp_velshim : False.
  pose (fun P => fwp velshim P velshim_ivs).
Opaque AnyOf. 
cbv beta iota delta [ fwp velshim ] in P.
unfold Semantics.eval_comp in P.
simpl in P.
unfold maybe_ge0, maybe_lt0 in P.
simpl eval_term in P.
simpl bound_fexpr in P.

Abort.


(* ltac automation *)
Ltac abstractor_cleanup P :=
  

(*
Fact fwp_test :
  forall (st : Syntax.state),
    (st "x" = 1%R)%type ->
    (fwp simple_prog (fun (ss : Syntax.state) => (ss "x" > 0)%R)%type)
      st.
Proof.
  intros.
  simpl. destruct (bounds_to_formula
           {|
           lb := RealT
                   (Fappli_IEEE.B2R custom_prec custom_emax (nat_to_float 1));
           ub := RealT
                   (Fappli_IEEE.B2R custom_prec custom_emax (nat_to_float 1));
           premise := TRUE |} st) eqn:Hb2f.
  left.
  split.
  
  - apply P.
  red.
  compute.

Opaque nat_to_float.

Check fwp.

Fact fwp_test :
  forall (st : Syntax.state),
  (fwp simple_prog (fun (ss : Syntax.state) => (ss "x" > 0)%R)%type)
    st.
Proof.
  intros.
  compute.

  Print nat_to_float.
  Print Fappli_IEEE_extra.BofZ.
  Print Fappli_IEEE.binary_normalize.
  Check Fappli_IEEE.FF2B.
  About Fappli_IEEE.binary_round_correct.
  Eval vm_compute in (nat_to_float 0).


  Print custom_prec.


  simpl. left.
  generalize (bound_fexpr_sound). intro.
  SearchAbout bounds_to_formula.
  
Abort.
*)
