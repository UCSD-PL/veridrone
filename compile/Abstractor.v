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

(* Next, we move to programs that operate on real numbers.
   We need to add an (axiomatized) decider for the reals, since the one in
   the standard library returns a value that cannot be matched on *)
Axiom my_req_dec : forall (a b : R),
                     {a = b} + {a <> b}.

Require Import micromega.Psatz.
Require Import ExtLib.Tactics.
Require Import FunctionalExtensionality.

Definition update {T} (s : nat -> T) (v : nat) (val : T) : nat -> T :=
  fun x =>
    if v ?[ eq ] x then val else s x.

Require Import ExtLib.Data.Option.

(* Embedding functions that
   distinguish between nontermination and failure. *)
Section embedding.
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
End embedding.


(***********************************************************************)
(* Next, we repeat this process for a language that operates on floats *)
(***********************************************************************)
Require Import source.

(* We no longer use this. It just made everything more complicated. We use fstate instead. *)
(* Definition statef : Type := Var -> option float. *)

Inductive fexpr :=
| FVar : Var -> fexpr
| FConst : source.float -> fexpr
| FPlus : fexpr -> fexpr -> fexpr
| FMinus : fexpr -> fexpr -> fexpr
| FMult : fexpr -> fexpr -> fexpr
(*| FDiv : fexpr -> fexpr -> fexpr*)
.
(* TODO - other ops? *)

Definition fplus : source.float -> source.float -> source.float :=
  Fappli_IEEE.Bplus custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Definition fminus : source.float -> source.float -> source.float :=
  Fappli_IEEE.Bminus custom_prec custom_emax custom_precGt0
                     custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Definition fmult : source.float -> source.float -> source.float :=
  Fappli_IEEE.Bmult custom_prec custom_emax custom_precGt0
                    custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

Definition fdiv : source.float -> source.float -> source.float :=
  Fappli_IEEE.Bdiv custom_prec custom_emax custom_precGt0
                   custom_precLtEmax custom_nan Fappli_IEEE.mode_NE.

(* TODO pretty sure we need to do variable translation here *)
Fixpoint fexprD (fx : fexpr) (sf : fstate) : option source.float :=
  match fx with
    | FVar s         => fstate_lookup sf s
    | FConst f       => Some f
    | FPlus fx1 fx2  => lift2 fplus  (fexprD fx1 sf) (fexprD fx2 sf)
    | FMinus fx1 fx2 => lift2 fminus (fexprD fx1 sf) (fexprD fx2 sf)
    | FMult fx1 fx2  => lift2 fmult  (fexprD fx1 sf) (fexprD fx2 sf)
    (*| FDiv fx1 fx2   => lift2 fdiv   (fexprD fx1 sf) (fexprD fx2 sf)*)
  end.

Inductive fcmd : Type :=
| FSeq   : fcmd -> fcmd -> fcmd
| FSkip  : fcmd
| FAsn   : Var -> fexpr -> fcmd
| FIte   : fexpr -> fcmd -> fcmd -> fcmd
| FHavoc : Var -> fcmd
| FFail  : fcmd
.

Definition fupdate {T : Type} (s : Var -> T) (v : Var) (val : T) : Var -> T :=
  fun x =>
    if v ?[eq] x then val else s x.

Definition fzero := Eval compute in (nat_to_float 0).

Require Import compcert.flocq.Core.Fcore_ulp.

Definition F2OR (f : float) : option R :=
  match f with
    | Fappli_IEEE.B754_zero   _       => Some (FloatToR f)
    | Fappli_IEEE.B754_finite _ _ _ _ => Some (FloatToR f)
    | _                               => None
  end.

Definition float_lt (f1 f2 : float)  : Prop :=
  (*(F2OR f1 = Some r1 /\ F2OR f2 = Some r2 /\ (r1 < r2)%R)%type.*)
  (FloatToR f1 < FloatToR f2)%R.

Definition float_ge (f1 f2 : float) : Prop :=
  (FloatToR f1 >= FloatToR f2)%R.

SearchAbout fstate.

Inductive feval : fstate -> fcmd -> option fstate -> Prop :=
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
    feval s (FAsn v e) (Some (fstate_set s v val))
| FEAsnN : forall s v e,
    fexprD e s = None ->
    feval s (FAsn v e) None
| FEIteT :
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_lt f fzero ->
      feval s c1 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteF:
    forall s os' ex c1 c2 f,
      fexprD ex s = Some f ->
      float_ge f fzero ->
      feval s c2 os' ->
      feval s (FIte ex c1 c2) os'
| FEIteN :
    forall s ex c1 c2,
      fexprD ex s = None ->
      feval s (FIte ex c1 c2) None
| FEHavoc : forall s v val,
      feval s (FHavoc v) (Some (fstate_set s v val))
| FEFail : forall s, feval s FFail None
.

(* Next, we develop Hoare instantiated with what we need for fcmd language *)
(* We probably don't need this type at all... We can remove it once we are sure
   this approach works. *)

Definition rstate : Type := list (Var * R).

Fixpoint rstate_lookup (r : rstate) (v : Var) : option R :=
  match r with
  | nil => None
  | (v', b) :: rs => if v ?[eq] v' then Some b else rstate_lookup rs v
  end.

Fixpoint rstate_set (r : rstate) (v : Var) (val : R) : rstate :=
  match r with
  | nil => [(v, val)]
  | (v', b) :: rs => if v ?[eq] v' then (v, val) :: rs  else (v', b) :: rstate_set rs v val
  end.

Definition real_float (r : R) (f : float): Prop :=
  (F2OR f = Some r)%type.

Check state.

(* Convert a float state to a real state *)
(* Assumes the floats are valid. *)
Fixpoint realify_state (fst : fstate) : rstate :=
  match fst with
  | nil            => nil
  | (v, f) :: fst' => (v, FloatToR f) :: realify_state fst'
  end.

Require Import bound.

(* Embedding function for our new language *)
Definition oembed_fcmd : _ -> _ -> fcmd -> Syntax.Formula :=
  oembedStep_maybenone Var fcmd fstate
                       feval
                       (fun st v => match fstate_lookup st v with
                                    | None => None
                                    | Some f => F2OR f
                                    end).

(* Useful auxiliary lemma for proving correspondences
   between float and real states when used with models *)

(*
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
*)
(*
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
*)

(*
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
*)

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
      (List.Forall (fun v' => let '(_, rv') := v' in rv' <> rv) ivs' /\
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
      (List.Forall (fun v' => let '(lv', _) := v' in lv' <> lv) ovs' /\
       ospec_valid ovs')%type
  end.

Definition var_spec_valid (ivs ovs : list (Var * Var)) :=
  (ispec_valid ivs /\ ospec_valid ovs)%type.

(*
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
*)

(* A couple of useful definitions for the correctness
   sub-lemmas that follow *)
(*
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
*)


Definition fstate_lookupR (fst : fstate) (v : Var) : option R :=
  match fstate_lookup fst v with
  | None => None
  | Some f => F2OR f
  end.
  
(* remember, left vars are floating point vars and right vars are TLA vars *)
(* Maybe useless; probably same as vmodels *)
Fixpoint fstate_state (vs : list (Var * Var)) (fst : fstate) (st : state) : Prop :=
  match vs with
  | nil => True
  | (vl, vr) :: vs' =>
    fstate_lookupR fst vl = Some (st vr) /\
              fstate_state vs' fst st
  end.

(* Another way of approaching abstract evaluation *)
Definition vmodels (vs : list (Var * Var)) (ss : Syntax.state) (sf : fstate) : Prop :=
  omodels Var fstate fstate_lookupR vs ss sf.

(** This is the semantic side condition **)
Definition SEMR (vs : list (Var * Var)) (P : Syntax.state -> Prop) : Prop :=
  forall c a b, vmodels vs a c -> vmodels vs b c -> P a -> P b.

Definition Hoare_ := Hoare fcmd fstate feval.

(* These are no longer used; we're performing the abstraction at the level
   of fwp rather than here. This was due to underlying changes to bound.v *)
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
    (|-- oembed_fcmd vs1 vs2 c -->>
                    Embed (fun st st' => P st -> Q st')).
Proof.
  unfold HoareA_all, Hoare_, Hoare. simpl; intros.
  unfold tlaEntails. intros tr HNOPE.
  simpl. intros. forward_reason. 
  destruct (H x).
  { intros. eapply H0. 2: eassumption. 2: eassumption. eassumption. }
  { forward_reason. destruct H3.
    { exfalso; auto. }
    { forward_reason.
      specialize (H6 _ H3). eauto. } }
Qed.

Lemma HoareA_embed_ex :
  forall P c Q vs1 vs2,
    HoareA_ex vs1 vs2 P c Q ->
    forall (HsemrQ : SEMR vs2 Q),
    (|-- oembed_fcmd vs1 vs2 c -->>
                    Embed (fun st st' => P st -> Q st')).
Proof.
  simpl. intros. unfold tlaEntails. simpl. intros tr HNOPE. intros.
  forward_reason.
  destruct (H x); clear H.
  { eexists; eauto. }
  { forward_reason. destruct H2; try solve [ exfalso; auto ].
    forward_reason.
    eapply H4 in H2.
    forward_reason.
    eapply HsemrQ; [ | | eassumption ]; eauto. }
Qed.

Print oembedStep_maybenone.

Print oembed_fcmd.
Require Import bound.
Lemma Hoare__embed :
  forall P c Q vs1 vs2,
    Hoare_ P c Q ->
    (|-- oembed_fcmd vs1 vs2 c -->>
         Embed (fun st st' =>
                  exists fst,
                    vmodels vs1 st fst /\
                    (P fst ->
                    exists fst',
                      vmodels vs2 st' fst' /\
                      Q fst'))).
Proof.
  simpl. intros. unfold tlaEntails. simpl.
  intros.
  fwd.
  unfold Hoare_, Hoare in H.
  exists x. intros. fwd.
  specialize (H _ H4). fwd.
  destruct H2.
  - contradiction.
  - fwd.
    specialize (H6 _ H2).
    exists x1.
    unfold vmodels, fstate_lookupR.
    split; auto.
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

(* this plus consequence should be enough to get our real assignment rule
   that talks about bounds *)
SearchAbout fstate.
Lemma Hoare__asn :
  forall P v e,
    Hoare_
      (fun fs : fstate =>
         exists val : float,
           fexprD e fs = Some val /\
           P (fstate_set fs v val))%type
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

(* Variable translation functions *)
(* These may be unnecessary *)
Fixpoint vtrans_flt2tla (ivs : list (Var * Var)) (v : Var) : Var :=
  match ivs with
    | nil              => v (* bogus *)
    | (vl, vr) :: ivs' =>
      if v ?[eq] vr then vl
      else vtrans_flt2tla ivs' v
  end.

Fixpoint vtrans_tla2flt (ivs : list (Var * Var)) (v : Var) : Var :=
  match ivs with
    | nil              => v (* bogus *)
    | (vl, vr) :: ivs' =>
      if v ?[eq] vl then vr
      else vtrans_tla2flt ivs' v
  end.

(* The actually correct definition of var_spec_valid *)
Fixpoint var_spec_valid' {T U : Type} (vs : list (T * U)) : Prop :=
  match vs with 
    | nil             => True
    | (lv, rv) :: vs' =>
      (List.Forall (fun vv => 
                let '(lv', rv') := vv in
                lv' <> lv /\ rv' <> rv)%type vs' /\
      var_spec_valid' vs')%type
  end.

(* Calculating bounds for expressions *)
(* TODO: removing vtrans here may be the wrong call *)
Fixpoint fexpr_to_NowTerm (fx : fexpr) (ivs : list (Var * Var)) : NowTerm :=
  match fx with
  (*| FVar v   => VarNowN (vtrans_flt2tla ivs v)*)
  | FVar v => VarNowN v
  | FConst f => FloatN f
  | FPlus fx1 fx2 =>
    PlusN (fexpr_to_NowTerm fx1 ivs) (fexpr_to_NowTerm fx2 ivs)
  | FMinus fx1 fx2 =>
    MinusN (fexpr_to_NowTerm fx1 ivs) (fexpr_to_NowTerm fx2 ivs)
  | FMult fx1 fx2 =>
    MultN (fexpr_to_NowTerm fx1 ivs) (fexpr_to_NowTerm fx2 ivs)
  end.

Definition bound_fexpr (fx : fexpr) (ivs : list (Var * Var)) : list singleBoundTerm :=
  bound_term (fexpr_to_NowTerm fx ivs).

Definition bounds_to_formula (sbt : singleBoundTerm) (fs : fstate) : (Prop * (R -> Prop)) :=
  denote_singleBoundTermNew fs sbt.

(* Used to translate between two different representations
   of floating-point state (since bounds proofs use a different one) *)
(*
Fixpoint fstate_statef (ivs : list (Var * Var)) (fs : fstate) (sf : statef) : Prop :=
  match ivs with
  | nil              => True
  | (vl, vr) :: ivs' =>
    fstate_lookup fs vl = sf vr /\ fstate_statef ivs' fs sf
  end.
             *)
(* old definition *)
(*
  match fs with
    | nil           => True
    | (v, f) :: fs' =>
      (sf v = Some f /\ fstate_statef fs' sf)%type
  end.
 *)

(*
Lemma fstate_statef_correct :
  forall (ivs : list (Var * Var)) (fs : fstate) (sf : statef) (v : Var) (f : float),
    fstate_statef ivs fs sf ->
    fstate_lookup fs v = sf v.
Proof.
  intro.
  induction fs.
  - intros. simpl in *. congruence.
  - intros. simpl in *. destruct a.
    fwd.
    consider (v ?[eq] v0); intros; subst; auto.
    rewrite <- H2. rewrite <- H. reflexivity.
Qed.
*)

(* TODO maybe have a concept of statef "containing" var map *)
(*
Fixpoint statef_to_fstate (ivs : list (Var * Var)) (sf : statef) : fstate :=
  match ivs with
    | nil             => nil
    | (vl, vr) :: ivs' =>
      match (sf vr) with
        | None   => statef_to_fstate ivs' sf
        | Some f => (vl, f) :: statef_to_fstate ivs' sf (* TODO: vr or vl? *)
                            (* vr = use float var for float state
                               vl = use tla var for float state *)
      end
  end.
*)

(*
Lemma related_vmodels :
  forall (ivs : list (Var * Var)) (ss : Syntax.state) (sf : statef),
    var_spec_valid' ivs ->
    vmodels ivs ss sf ->
    related (statef_to_fstate ivs sf) ss.
Proof.
  induction ivs.
  - intros. simpl in *. unfold related. intros.
    simpl in *. congruence.
  - intros. simpl in *. destruct a.
    fwd.
    unfold realify_state in H0.
    generalize (IHivs _ _ H2 H1); intro Hrel.
    consider (sf v0); intros; auto.
    unfold related. simpl. intros.
    consider (x ?[eq] v); intros; auto.
    inversion H5; subst; clear H5.    
    rewrite H3. reflexivity. 
Qed.
*)
      
(* Ensures the variable map only mentions variables in the given expression *)
Fixpoint varmap_check_fexpr (ivs : list (Var * Var)) (e : fexpr) : Prop :=
  match e with
  | FVar v       => exists lv, In (lv, v) ivs
  | FConst _     => True
  | FPlus e1 e2  => varmap_check_fexpr ivs e1 /\
                    varmap_check_fexpr ivs e2
  | FMinus e1 e2 => varmap_check_fexpr ivs e1 /\
                    varmap_check_fexpr ivs e2
  | FMult e1 e2  => varmap_check_fexpr ivs e1 /\
                    varmap_check_fexpr ivs e2
  end%type.  

(* Another lemma relating the behaviors of necessary primitives *)
(*
Lemma related_vmodels_lookup :
  forall ivs v x,
    var_spec_valid' ivs ->
    In (x, v) ivs ->
    forall st,
      fstate_lookup (statef_to_fstate ivs st) x = st v.
Proof.
  induction ivs.
  - simpl. intros. contradiction.
  - simpl.
    destruct a. 
    intros.
    destruct H0.
    { inversion H0; subst; clear H0.
      fwd.
      consider (st v1); intros.
      - simpl. rewrite RelDec.rel_dec_eq_true; eauto with typeclass_instances.
      - clear IHivs. induction H.
        + reflexivity.
        + simpl. destruct x0. fwd.
          simpl in H0.
          consider (st v0); intros.
          { simpl. consider (v1 ?[eq] v0); intros.
            - subst. rewrite H4 in H1. congruence.
            - fwd. consider (x ?[eq] v); intros;  congruence. }
          { fwd; eauto. } }
     { fwd. 
       specialize (IHivs _ _ H1 H0).
       rewrite <- IHivs.
       consider (st v0); intros.
       - simpl.
         consider (x ?[eq] v); intros.
         + subst. generalize Forall_forall. intros Hfafa.
           edestruct Hfafa. clear H4. specialize (H3 H _ H0). simpl in H3.
           fwd. congruence.
         + rewrite IHivs. consider (v1 ?[eq] v0); intros.
           * subst. auto.
           * reflexivity.
       - reflexivity. }
Qed.
*)

(* Important auxiliary lemma related fexprD and eval_NowTerm *)

(*
Lemma fexpr_NowTerm_related_eval :
  forall ivs fst stf,
    var_spec_valid' ivs ->
    fstate_statef ivs fst stf ->
    forall fx f,
    varmap_check_fexpr ivs fx ->
    fexprD fx stf = Some f ->
    eval_NowTerm fst (fexpr_to_NowTerm fx ivs) = Some f.
 *)

Print varmap_check_fexpr.

Lemma fexpr_NowTerm_related_eval :
  forall ivs fst,
    var_spec_valid' ivs ->
    forall fx f,
    varmap_check_fexpr ivs fx ->
    fexprD fx fst = Some f ->
    eval_NowTerm fst (fexpr_to_NowTerm fx ivs) = Some f.
Proof.
  induction fx; eauto;
  try (intros; simpl; simpl in *; fwd;
    unfold lift2 in *;
    consider (fexprD fx1 fst); intros; try congruence;
    consider (fexprD fx2 fst); intros; try congruence;
    erewrite IHfx1; eauto;
    erewrite IHfx2; eauto). (* take care of plus, minus *)

  (* (* used to be necessary; we've changed how we do variable translation now *)
  - simpl. intros. fwd.
    rewrite <- H1.
    generalize dependent x.
    induction ivs.
    + simpl in *. contradiction.
    + simpl. destruct a. simpl in *. intros. fwd.
      destruct H0.
      { inversion H0; subst; clear H0. rewrite RelDec.rel_dec_eq_true; eauto with typeclass_instances. }
      { consider (v ?[eq] v1); intros.
        - subst. eapply Forall_forall in H; eauto.
        - eapply IHivs; eauto. }
   *)
Qed.


(* THE correctness lemma for bound_fexpr (that we use) *)
(*
Lemma bound_fexpr_sound : forall ivs fx sbts,
    bound_fexpr fx ivs = sbts ->
    var_spec_valid' ivs ->
    varmap_check_fexpr ivs fx ->
    List.Forall (fun sbt =>
              forall st st' f,
                fexprD fx st' = Some f ->
                vmodels ivs st st'  ->
                let '(P,Pr) := bounds_to_formula sbt st in
                P -> exists fval, fexprD fx st' = Some fval
                                  /\ exists val,
                                    F2OR fval = Some val /\ Pr val)%type
           sbts.
 *)

(* TODO - need another hypothesis linking fst to var map ? *)
Lemma bound_fexpr_sound : forall ivs fx sbts,
    bound_fexpr fx ivs = sbts ->
    var_spec_valid' ivs ->
    varmap_check_fexpr ivs fx ->
    List.Forall (fun sbt =>
              forall (fst : fstate) f,
                fexprD fx fst = Some f ->
                (*fstate_statef ivs fst stf ->*)
                let '(P,Pr) := bounds_to_formula sbt fst in
                P -> exists fval, fexprD fx fst = Some fval
                                  /\ exists val,
                                    F2OR fval = Some val /\ Pr val)%type
                sbts.
Proof.
  intros.
  generalize (bound_proof'). intro Hbp.
  apply Forall_forall. intros.
  specialize (Hbp (fexpr_to_NowTerm fx ivs) fst).
  fwd. intros.
  unfold bounds_to_formula, denote_singleBoundTermNew in H4.  simpl in H4.
  inversion H4; subst; clear H4.
  exists f.
  split; auto.
  unfold boundDef' in Hbp. simpl in Hbp.
  generalize (fexpr_NowTerm_related_eval ivs fst H0 fx f H1 H3); intro Hentfxd.
  rewrite Hentfxd in Hbp.
  apply Forall_forall with (x := x) in Hbp.
  - consider (floatToReal f); intros.
    + exists r. split.
      * rewrite <- H. reflexivity.
      * auto.
    + exfalso; auto.
  - unfold bound_fexpr in *; assumption.
Qed.

(* Useful prop combinator *)
Fixpoint AnyOf (Ps : list Prop) : Prop :=
  match Ps with
    | nil => False
    | P :: Ps => P \/ AnyOf Ps
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

Lemma fstate_lookup_irrelevant_update :
  forall fst v v' val,
    v <> v' ->
    fstate_lookup fst v = fstate_lookup (fstate_set fst v' val) v.
Proof.
  intros.
  induction fst.
  - simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
  - simpl. destruct a.
    consider (v ?[eq] v0); intros; subst.
    + rewrite rel_dec_neq_false; eauto with typeclass_instances.
      simpl. rewrite rel_dec_eq_true; eauto with typeclass_instances.
    + consider (v' ?[eq] v0); intros; subst.
      * simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
      * simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
Qed.

Lemma vmodels_irrelevant_update :
  forall (ivs : list (Var * Var)) (v v' : Var) (s : fstate)
         (x : Syntax.state) (x1 : R) (val : float),
    vmodels ivs x s ->
    List.Forall (fun (vv : (Var * Var)) =>
              let '(lv, rv) := vv in 
              lv <> v' /\ rv <> v)%type ivs ->
    vmodels ivs (fupdate x v' x1) (fstate_set s v val).
Proof.
  induction 2. 
  - simpl. constructor.
  - destruct x0. fwd.
    simpl.
    split.
    + unfold fupdate, realify_state.
      rewrite rel_dec_neq_false; eauto with typeclass_instances.
      simpl in H. fwd. rewrite H.
      unfold fstate_lookupR.
      erewrite fstate_lookup_irrelevant_update; eauto.
    + apply IHForall. simpl in H. fwd. assumption.
Qed.

(* Lemmas aboutt Forall, needed for HoareA_ex_asn *)
Lemma Forall_impl : forall T (P Q : T -> Prop) ls,
                      List.Forall (fun x => P x -> Q x) ls ->
                      (List.Forall P ls -> List.Forall Q ls).
Proof.
  induction 2.
  - constructor.
  - inversion H; clear H; subst.
    constructor; eauto.
Qed.

Lemma Forall_tauto : forall T (P : T -> Prop) ls,
                       (forall x, P x) ->
                       List.Forall P ls.
Proof.
  induction ls; simpl; intros; eauto.
Qed.

Lemma fstate_lookup_update_match :
  forall fst v val,
    Some val = fstate_lookup (fstate_set fst v val) v.
Proof.
  intros.
  induction fst.
  - simpl. rewrite rel_dec_eq_true; eauto with typeclass_instances.
  - simpl. destruct a.
    consider (v ?[eq] v0); intro; subst.
    + simpl. rewrite rel_dec_eq_true; eauto with typeclass_instances.
    + simpl. rewrite rel_dec_neq_false; eauto with typeclass_instances.
Qed.

Lemma vmodels_fupdate_match :
   forall (ivs : list (Var * Var)) (v v' : Var)
          (fst : fstate) (ss : Syntax.state) (r : R) (f : float),
   var_spec_valid' ivs ->
   In (v, v') ivs ->
   vmodels ivs ss fst ->
   F2OR f = Some r ->
   vmodels ivs (fupdate ss v r) (fstate_set fst v' f).
Proof.
  induction ivs.
  - simpl in *. constructor.
  - intros.
    destruct H0.
    + simpl. fwd. intros. subst. split. 
      * unfold fupdate, realify_state.
        inversion H1; subst; clear H1; simpl.
        rewrite rel_dec_eq_true; eauto with typeclass_instances.
        unfold fstate_lookupR. rewrite <- fstate_lookup_update_match.
        auto.
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
        rewrite rel_dec_neq_false; eauto with typeclass_instances.
        simpl in H1. fwd. rewrite H1.
        unfold fstate_lookupR. rewrite <- fstate_lookup_irrelevant_update; eauto.
      * simpl in H1. fwd. eauto. 
Qed.

Lemma varmap_check_contradiction :
  forall (ivs : list (Var * Var)) (fe : fexpr)
         (fst : fstate) (ss : Syntax.state),
    varmap_check_fexpr ivs fe ->
    vmodels ivs ss fst ->
    fexprD fe fst = None ->
    False.
Proof.
  intros.
  induction fe;
    (* dispatch recursive cases *)
    try (solve [
             simpl in *; unfold lift2 in *; 
             inversion H1; subst; clear H1;
             destruct (fexprD fe1 fst); try congruence;
             destruct (fexprD fe2 fst); try congruence;
             fwd;
             try (solve [apply IHfe1; eauto] ); try (solve [apply IHfe2; eauto]) ] ).
  - induction ivs.
    + intros. simpl in *. fwd. assumption.
    + intros. simpl in *. fwd. destruct a. fwd.
      destruct H.
      { inversion H; subst; clear H.
        unfold fstate_lookupR in H0. rewrite H1 in H0. congruence. }
      { eauto. } 
Qed.

(* Significant correctness lemma for HoareA/Abstractor as a whole *)
(*
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
                         (bound_fexpr e ivs)))%type
      (FAsn v' e)
      P.
 *)

SearchAbout fstate state.

Lemma HoareA_ex_asn :
  forall ivs (P : _ -> Prop) v v' e,
    var_spec_valid' ivs ->
    varmap_check_fexpr ivs e ->
    In (v, v') ivs ->
    HoareA_ex ivs ivs
              (fun ss : Syntax.state =>
                 forall fs : fstate,
                   vmodels ivs ss fs ->
                   AnyOf (List.map (fun sbt =>
                                      let '(pred,bound) := bounds_to_formula sbt fs in
                                      pred /\ forall val : R,
                                          bound val -> P (fupdate ss v val))
                                   (bound_fexpr e ivs)))%type
              (FAsn v' e)
              P.
SearchAbout oembed_fcmd HoareA_ex.
Proof.
  unfold HoareA_ex.
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
    { simpl in *.
      exfalso; eauto. }
    { simpl in *.
      fwd.
      inversion H4; subst; clear H4.
      clear IHl.
      specialize (H3 s H2).
      destruct H3.
      - fwd.
        specialize (H8 _ _ H7 H3). fwd.
        exists (fupdate x v x1).
        split; auto.
        apply vmodels_fupdate_match; auto.
        rewrite H7 in H5. inversion H5; subst; clear H5.
        assumption.
      - simpl in H3.

  } }
Qed.

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

Lemma vtrans_flt2tla_In :
  forall x v ivs,
    var_spec_valid' ivs ->
    In (x, v) ivs ->
    vtrans_flt2tla ivs v = x.
Proof.
  induction ivs.
  - intros. inversion H0.
  - intros. simpl in *. destruct a. fwd.
    destruct H0.
    + inversion H0; subst; clear H0.
      rewrite RelDec.rel_dec_eq_true; eauto with typeclass_instances.
    + rewrite IHivs; auto. consider (v ?[eq] v1); intros.
      { eapply Forall_forall in H; eauto.
        simpl in H. fwd. subst. congruence. }
      { reflexivity. }
Qed.

Lemma vmodels_must_exist :
  forall (ivs : list (Var * Var)),
    var_spec_valid' ivs ->
    forall x v,
      In (x, v) ivs ->
      forall s x0,
      vmodels ivs x0 s ->
      exists y, (s v = Some y)%type.
Proof.
  induction ivs.
  - intros. simpl in *. contradiction.
  - intros. simpl in *. destruct a.
    fwd.
    destruct H0.
    + inversion H0; subst; clear H0.
      unfold realify_state in H1.
      consider (s v); intros; try congruence.
      eexists; reflexivity.
    + eapply IHivs; eauto.
Qed.

Lemma vmodels_correspond :
  forall ivs,
    var_spec_valid' ivs ->
    forall x v,
      In (x, v) ivs ->
      forall ss sf,
        vmodels ivs ss sf ->
        forall f,
          sf v = Some f ->
          (F2OR f = Some (ss x))%type.
Proof.
  induction ivs.
  - simpl. intros. contradiction.
  - simpl. intros.
    destruct a. fwd.
    destruct H0.
    + inversion H0; subst; clear H0.
      unfold realify_state in H1.
      consider (sf v); intros; try congruence.
    + eapply IHivs; eauto.
Qed.        

Lemma HoareA_ex_or :
  forall ivs (P1 P2 Q : _ -> Prop) c,
    HoareA_ex ivs ivs P1 c Q ->
    HoareA_ex ivs ivs P2 c Q ->
    HoareA_ex ivs ivs (fun st => P1 st \/ P2 st)%type c Q.
Proof.
  intros.
  unfold HoareA_ex, Hoare_, Hoare in *.
  intros. fwd.
  destruct H2.
  { clear H0.
    specialize (H s).
    destruct H.
    - eexists; eauto.
    - split; auto. }
  { clear H.
    specialize (H0 s).
    destruct H0.
    - eexists; eauto.
    - split; auto. }
Qed.

Lemma HoareA_ex_False :
  forall ivs (P : _ -> Prop) c,
    HoareA_ex ivs ivs (fun _ => False) c P.
Proof.
  intros.
  unfold HoareA_ex, Hoare_, Hoare.
  intros. fwd. contradiction.
Qed.

Lemma HoareA_conseq :
  forall (P P' Q Q' : Syntax.state -> Prop) (c : fcmd) (ivs ovs : list (Var * Var)),
    (forall st : Syntax.state, P st -> P' st) ->
    (forall st : Syntax.state, Q' st -> Q st) -> 
    HoareA_ex ivs ovs P' c Q' ->
    HoareA_ex ivs ovs P c Q.
Proof.
  intros.
  unfold HoareA_ex in *. eapply Hoare__conseq; eauto.
  - intros. fwd. eexists. split; eauto.
  - intros. simpl in H2. fwd. eexists.
    split; eauto.
Qed.

(* auxiliary functions for HoareA ITE rule *)
Definition maybe_lt0 (sbts : list singleBoundTerm) : (Syntax.state -> Prop) :=
  fun ss =>
    AnyOf (List.map
             (fun sbt =>
                (eval_term (lb sbt) ss ss <  0)%R /\
                (Semantics.eval_formula (premise sbt) (traceFromState ss))) sbts)%type.

Definition maybe_ge0 (sbts : list singleBoundTerm) : (Syntax.state -> Prop) :=
  fun ss =>
    AnyOf (List.map
             (fun sbt =>
                (eval_term (ub sbt) ss ss >= 0)%R /\
                (Semantics.eval_formula (premise sbt) (traceFromState ss))) sbts)%type.


Lemma or_distrib_imp :
  forall A B C : Prop,
    (A \/ B -> C) <->
    (A -> C) /\ (B -> C).
Proof.
  tauto.
Qed.

Lemma and_distrib_or :
  forall A B C : Prop,
    A /\ (B \/ C) <->
    (A /\ B) \/ (A /\ C).
Proof.
  tauto.
Qed.

Lemma float_lt_ge_trichotomy :
  forall f f', (float_lt f f' \/ float_ge f f').
Proof.
  intros. unfold float_lt, float_ge.
  lra.
Qed.

Lemma float_lt_ge_trichotomy_contra :
  forall f f', float_lt f f' /\ float_ge f f' -> False.
Proof.
  intros. unfold float_lt, float_ge in H. lra.
Qed.

Lemma HoareA_ex_ite :
  forall ex ivs (P Q1 Q2: _ -> Prop) c1 c2,
    var_spec_valid' ivs ->
    varmap_check_fexpr ivs ex ->
    HoareA_ex ivs ivs Q1 c1 P ->
    HoareA_ex ivs ivs Q2 c2 P ->
    HoareA_ex ivs ivs
    (fun ss => let bs := bound_fexpr ex ivs in
               (maybe_lt0 bs ss -> Q1 ss) /\
               (maybe_ge0 bs ss -> Q2 ss) /\
               (AnyOf (List.map (fun sbt => fst (denote_singleBoundTermNew ss sbt)) bs)))%type
    (FIte ex c1 c2)
    P.
Proof.
  intros.
  generalize (bound_fexpr_sound ivs ex _ eq_refl H H0).
  induction 1.
  { simpl. eapply HoareA_conseq.
    3: eapply HoareA_ex_False.
    simpl. tauto.
    exact (fun _ x => x). }
  { simpl. eapply HoareA_conseq.
    2: exact (fun _ x => x).
    unfold maybe_lt0. unfold maybe_ge0.
    simpl. intros.
    repeat rewrite or_distrib_imp in H5.
    repeat rewrite and_distrib_or in H5.
    eapply H5.
    eapply HoareA_conseq.
    2: exact (fun _ x => x).
    2: eapply HoareA_ex_or.
    3: eapply IHForall.
    simpl.
    intros.
    destruct H5.
    { fwd.
      left. exact (conj H5 (conj H6 H7)). }
    { right. tauto. }
    clear IHForall H4.
    do 3 red.
    intros. fwd.
    generalize (varmap_check_contradiction ivs ex s x0 H0 H4); intro Hvmcc.
    consider (fexprD ex s); intros; try congruence.
    clear Hvmcc.
    do 3 red in H1, H2.
    specialize (H1 s). specialize (H2 s).
    destruct (float_lt_ge_trichotomy f fzero).
    { destruct H1.
      { eexists; split; eauto. eapply H5.
        specialize (H3 _ _ _ H8 H4 H7).
        forward_reason.
        unfold traceFromState in *; simpl in *.
        rewrite H1 in *; inv_all; subst.
        split; auto.
        destruct f; simpl in H3; try congruence.
        - unfold float_lt in H9. simpl in H9. lra.
        - inversion H3; subst; clear H3.
          unfold float_lt in H9. simpl in H9. lra. }
      forward_reason. split.
      { eexists; eapply FEIteT; eauto. }
      split.
      { intro. inversion H12; clear H12; subst; eauto; try congruence.
        rewrite H8 in H17. inv_all. subst.
        unfold float_ge in H19. unfold float_lt in H9.
        lra. }
      intros.
      inversion H12; clear H12; subst; eauto.
      rewrite H8 in *. inv_all; subst. 
      exfalso. eapply float_lt_ge_trichotomy_contra; eauto. }
    { destruct H2.
      { eexists; split; eauto. apply H6.
        specialize (H3 _ _ _ H8 H4 H7).
        fwd.
        unfold traceFromState in *; simpl in *.
        rewrite H2 in *; inv_all; subst.
        split; auto.
        destruct f; simpl in H3; try congruence.
        - inversion H3; subst; clear H3.
          lra.
        - inversion H3; subst; clear H3. 
          unfold float_ge in H9. simpl in H9.
          lra. }
      { fwd.
        split.
        { eexists; eapply FEIteF; eauto. }
        split.
        { intro. inversion H12; subst; clear H12; eauto; try congruence.
          rewrite H8 in H17. inversion H17; subst; clear H17.
          eapply float_lt_ge_trichotomy_contra; eauto. }
        intros. inversion H12; subst; clear H12; auto.
        rewrite H8 in H17. inversion H17; subst; clear H17.
        exfalso; eapply float_lt_ge_trichotomy_contra; eauto. } } }
Qed.


(* Weakest-precondition calcluation function for fcmd language *)
(* TODO made fwp take ivs? *)
Check eval_term.

Fixpoint fwp (c : fcmd) (P : Syntax.state -> Prop) (ivs : list (Var * Var)) : Syntax.state -> Prop :=
  match c with
  | FSkip => P
  | FSeq c1 c2 => fwp c1 (fwp c2 P ivs) ivs
  | FAsn v e => (fun ss =>
                   AnyOf (List.map
                            (fun sbt =>
                               let '(pred,bound) := bounds_to_formula sbt ss in
                               pred /\ forall val : R,
                                         bound val -> P (fupdate ss v val))
                            (bound_fexpr e ivs)))%type
  | FFail => fun s => False
  | FHavoc v => fun s => False
  (*| FIte ex c1 c2 => (fun ss =>
                        AnyOf (List.map
                                   (fun sbt =>
                                      (* NB the bounds on 0 are just 0 *)
                                      (* "ex is maybe < 0" *)
                                      ((eval_term (lb sbt) ss ss <  0)%R -> fwp c1 P ivs ss) /\
                                      (* "ex is maybe >= 0" *)
                                      ((eval_term (ub sbt) ss ss >= 0)%R -> fwp c2 P ivs ss))
                                   (bound_fexpr ex ivs)))%type*)
  | FIte ex c1 c2 => (fun ss =>
                        let bs := bound_fexpr ex ivs in
                        (maybe_lt0 bs ss -> fwp c1 P ivs ss) /\
                        (maybe_ge0 bs ss -> fwp c2 P ivs ss) /\
                        (AnyOf (List.map (fun sbt => fst (denote_singleBoundTermNew ss sbt)) bs)))%type
  (*| FIte ex c1 c2 => (fun ss =>
                        (fexprD ex s = Some fzero /\ fwp c1 P s) \/
                        (exists (f : source.float), f <> fzero /\
                                                   fexprD ex s = Some f /\
                                                   fwp c2 P s))%type *)
  (*| FIte _ _ _ => fun s => False*)
  end.

Lemma fwp_correct :
  forall c ivs P,
    var_spec_valid' ivs ->
    varmap_check_fcmd ivs c ->
    HoareA_ex ivs ivs
              (fwp c P ivs)
              c
              P.
Proof.
  intros c.
  induction c; intros; eauto using HoareA_ex_False.
  { simpl. eapply Hoare__seq.
    - eapply IHc1. 
      + assumption.
      + simpl in H0; fwd; assumption.
    - eapply IHc2. 
      + assumption. 
      + simpl in H0; fwd; assumption. }
  { eapply Hoare__skip. }
  { eapply HoareA_ex_asn; simpl in H0; fwd; assumption. }
  { simpl in *. forward_reason.
    simpl. eapply HoareA_ex_ite; eauto. }
Qed.

(* test case - velocity shim *)

Definition velshim : fcmd :=
  FIte (FMinus (FVar "ub") (FPlus (FMult (FVar "a") (FVar "d")) (FVar "vmax")))
       (FAsn "a" (FVar "a"))
       (FAsn "a" (FConst fzero)).

Definition velshim_ivs : list (Var * Var) :=
  [("ub", "ub"); ("a", "a"); ("d", "d"); ("vmax", "vmax")].

Definition proportional_controller : fcmd :=
  FAsn "a" (FMult (FVar "c") (FMinus (FVar "goal") (FVar "x"))).

Definition proportional_controller_ivs : list (Var * Var) :=
  [("a", "a"); ("c", "c"); ("x", "x"); ("goal", "goal")].

(* TODO make and prove equivalent a transparent version of nat_to_float/B2R/BofZ. *)

(*
Fact fwp_propcontrol : False.
  pose (fun P => fwp proportional_controller P proportional_controller_ivs).
  Opaque AnyOf.
  cbv beta iota delta [fwp proportional_controller] in P.
  simpl in P.
  unfold Semantics.eval_comp in P.
Abort.

Fact fwp_velshim : False.
  pose (fun P => fwp velshim P velshim_ivs).
Opaque AnyOf. 
cbv beta iota delta [ fwp velshim ] in P.
unfold Semantics.eval_comp in P.
simpl in P.
unfold maybe_ge0, maybe_lt0 in P.
simpl eval_term in P.
Abort.
*)
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
(* TODO: Prove that predicates produced by fwp have SEMR property? *)

