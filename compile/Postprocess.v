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
Require Import Abstractor.
Require Import TLA.Automation.
Require Import Coq.Classes.Morphisms.



Lemma Z3Test : forall (a : R), (a + 1 = 3)%R%type -> ((a + 2 = 3)%R /\ ((1+1)%R=2%R)%R)%type.
Proof.
  intros.
  (*z3 solve.*)
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
Lemma arith_push_fupdate_eq :
  forall (t: state -> state -> R) (v : Var) (X : Term) f,
    X =|> t ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v).
Proof.
  intros. unfold evals_to in *.
  rewrite H. unfold fupdate.
  rewrite rel_dec_eq_true; eauto with typeclass_instances.
Qed.

Lemma arith_push_fupdate_neq :
  forall (t: state -> state -> R) (v v' : Var) (X : Term) f,
    v <> v' ->
    X =|> (fun x y : state => f x y v') ->
    X =|> (fun x y : state => fupdate (f x y) v (t x y) v').
Proof.
  intros.
  unfold fupdate, evals_to in *. rewrite H0.
  rewrite rel_dec_neq_false; eauto with typeclass_instances.
Qed.

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

Definition simple_prog_ivs : list (Var * Var) :=
  [("x", "x")].

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
Definition FP2RP (ivs : list (Var * Var)) (P : fstate -> Prop) : state -> Prop :=
  (fun st =>
     exists (fst : fstate), vmodels ivs st fst /\ P fst).

(* Version of HoareA_embed_ex we can use for rewriting. *)
Require Import source.
(*
Lemma Hoare__embed_rw :
  forall (c : fcmd)
         (vs1 : list (Var * Var)),
    var_spec_valid' vs1 ->
    varmap_check_fcmd vs1 c ->
    oembed_fcmd vs1 vs1 c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  Embed (fun st st' : state =>
           (exists fst : fstate,
             vmodels vs1 st fst /\
             P fst) -> exists fst' : fstate, vmodels vs1 st' fst' /\ Q fst').
 *)
(*
Lemma Hoare__embed_rw :
  forall (c : fcmd)
         (vs1 : list (Var * Var)),
    var_spec_valid' vs1 ->
    varmap_check_fcmd vs1 c ->
    oembed_fcmd vs1 vs1 c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  Embed (fun st st' : state =>
           FP2RP vs1 P st -> FP2RP vs1 Q st').
Proof.
  intros. apply lforallR.
  intro. simpl. restoreAbstraction.
  tlaRevert.
  unfold FP2RP.
  breakAbstraction.
  intros.
  fwd.
  destruct H5.
  unfold vmodels in *.
  exists x0. split; eauto.
  
  intros.
  fwd.
  destruct H5.
  { inversion H5; subst; clear H5; try congruence.
    { simpl in H4.
    - 
  }
  
  {
  split.

  apply fwp_correct in H4. fwd.
  destruct x2; try congruence.
  specialize (H7 _ H4).
  exists f.
  split; auto.
  destruct H5.
  unfold limpl.
  simpl.
  unfold tlaEntails.
  intros.
  simpl.
  shatterAbstraction.
  intros.
  eexists. intros.
  simpl.
  eapply Hoare__embed.
  Check Hoare__embed.
  (*fix this later *)
Admitted.
*)

Require Import ExtLib.Tactics.
Lemma Hoare__embed_rw :
  forall (c : fcmd)
         (vs1 : list (Var * Var)),
    var_spec_valid' vs1 ->
    varmap_check_fcmd vs1 c ->
    oembed_fcmd vs1 vs1 c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  Embed (fun st st' : state =>
           (exists fst : fstate,
             vmodels vs1 st fst /\
             (P fst -> exists fst' : fstate, vmodels vs1 st' fst' /\ Q fst'))).
Proof.
  intros.
  breakAbstraction.
  intros.
  fwd.
  exists x0.
  split; auto.
  intros.
  eapply fwp_correct in H3.
  fwd.
  destruct H2; try congruence.
  fwd.
  consider x1; intros; try congruence; subst.
  exists x2.
  split; auto.
Qed.

Check fwp.
Print SEMR.

(*
Lemma HoareA_embed_ex_rw_orig :
  forall (c : fcmd) (vs1 : list (Var * Var)),
    var_spec_valid' vs1 ->
    varmap_check_fcmd vs1 c ->
    oembed_fcmd vs1 vs1 c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  PropF (SEMR vs1 Q) -->> Embed (fun st st' : state => P st -> Q st').
*)

Require Import source.
Definition FP2RP' (ivs : list (Var * Var)) (P : fstate -> Prop) (Q : Prop) : state -> Prop :=
  (fun st =>
     exists (fst : fstate), vmodels ivs st fst /\ (P fst -> Q)).

Lemma Hoare__embed_rw' :
  forall (c : fcmd)
         (vs1 : list (Var * Var)),
    var_spec_valid' vs1 ->
    varmap_check_fcmd vs1 c ->
    oembed_fcmd vs1 vs1 c |--
                Forall Q : fstate -> Prop,
  let P := fwp c Q in
  Embed (fun st st' : state =>
           FP2RP' vs1 P (exists fst' : fstate, vmodels vs1 st' fst' /\ Q fst') st).
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
Check fstate_lookup.
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

Check isVarValid.

(* Automation for rewriting Embeds *)
Hint Extern
     0 (_ =|> (fun _ _ => ?X)) => first [ apply arith_push_Nat_zero | apply arith_push_Nat_one
                                          | apply arith_push_Nat | apply arith_push_Real]
                                  : arith_push.

Hint Resolve
     arith_push_plus arith_push_minus arith_push_mult arith_push_inv
     arith_push_sin arith_push_cos
     arith_push_VarNow arith_push_VarNext
     arith_push_fupdate_eq arith_push_fupdate_neq
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
Fact fwp_simpler : |-- "x" > 0 //\\ [](oembed_fcmd simple_prog_ivs simple_prog_ivs simpler_prog) -->> []("x" > 0).
Proof.
  erewrite -> Hoare__embed_rw; [| solve [simpl; intuition] | solve [simpl; intuition; eauto]].
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
      unfold fstate_lookupR in H.
      rewrite H2 in H.
      rewrite H3 in H.
      inversion H; subst; clear H.
      assumption.
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

Fact fwp_simpler_full : preVarIsFloat "x" //\\ "x" > 0 //\\
                                [](oembed_fcmd simple_prog_ivs simple_prog_ivs simpler_prog \\//
                                               (Enabled (oembed_fcmd simple_prog_ivs simple_prog_ivs simpler_prog) -->> lfalse))
                                |-- [](preVarIsFloat "x" //\\ "x" > 0).
Proof.
  eapply discr_indX.
  { red. simpl. intuition. }
  { charge_assumption. }
  { tlaIntuition. }

  tlaRevert.
  eapply lorL.
  {
    erewrite -> Hoare__embed_rw; [| solve [simpl; intuition] | solve [simpl; intuition; eauto]].
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
      { unfold fstate_lookupR in H.
        rewrite H0 in H.
        rewrite H1 in H.
        inversion H.
        exists x1.
        split.
        - unfold F2OR in H1.
          destruct x1; try congruence.
        - eauto.
      }
      {
        unfold fstate_lookupR in H.
        rewrite H0 in H.
        rewrite H1 in H. inversion H.
        rewrite H5.
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
    simpl.
    intro st0; clear st0.
    generalize (F2OR_FloatToR _ _ _ H1 H); intro HF2OR.
    subst.

    eexists.
    exists (fstate_set nil "x" x).

    simpl.
    split.
    { split; auto. }
    { right.
      eexists.
      split.
      { econstructor. reflexivity. }
      { simpl. split; auto. } } }
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
  exists (vf : float), fstate_lookup fs v = Some vf /\
                  exists (vr : R), F2OR vf = Some vr /\ P vr fs.

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
      eapply (inject_var "v").
      charge_intro.
      eapply lforallL.

      instantiate (1 := (fstate_get_rval "a" (fun a fs => a = 0 \/ (x + a) < 10)%R)).
      cbv zeta.
      simpl fwp.
      eapply lequiv_rewrite_left.
      { crunch_embeds. }
      (* todo find a cbv list to control reduction, leaving as much abstracion as possible *)

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

            simpl bound_term in H5.
            unfold simpleBound2 in H5.
            unfold simpleBound in H5.
            simpl in H5.


            Print lofst.
            unfold maybe_ge0 in H5.
            unfold map in H5.
            simpl in H5.

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
        {
           repeat match goal with
                     | |- context[Fcore_defs.F2R ?X] =>
                       let Y := constr:(@Fcore_defs.F2R Fappli_IEEE.radix2 X) in
                       let Y' := eval compute in Y in
                         change Y with Y' in H
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

              breakAbstraction.
              intros. fwd.
              rewrite H. rewrite H0.
              unfold lift2.

              unfold lofst in *;
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

              Lemma crunch_or :
                forall (P P' Q Q' : Prop),
                  (P' -> P) -> (Q' -> Q) ->
                  P' \/ Q -> P \/ Q.
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
