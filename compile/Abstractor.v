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

(* state utility functions *)
(* finite map lookup *)
Fixpoint fm_lookup {T : Type} (l : list (string * T)) (s : string): option T :=
  match l with
  | nil => None
  | (var, val) :: l' =>
    if string_dec s var
    then Some val
    else fm_lookup l' s
  end.

(* finite map update *)
Fixpoint fm_update {T : Type} (l : list (string * T)) (s : string) (t : T) : list (string * T) :=
  match l with
  | nil => [(s,t)]
  | (var, val) :: l' =>
    if string_dec s var
    then (var, t) :: l'
    else (var, val) :: fm_update l' s t
  end.



Module Type EMBEDDING.
  Parameter ast : Type.
  Parameter pl_data : Type.

  Parameter pl_equ : pl_data -> pl_data -> Prop.

  Axiom pl_equ_refl : forall (p : pl_data), pl_equ p p.
  Axiom pl_equ_trans : forall (p p' p'' : pl_data),
      pl_equ p p' -> pl_equ p' p'' -> pl_equ p p''.
  Axiom pl_equ_symm : forall (p p' : pl_data),
      pl_equ p p' -> pl_equ p' p.
  
  Definition istate : Type := list (string * pl_data).
    
  Parameter eval : (istate -> ast -> istate -> Prop).

  (* Embedding deterministic functions that fail by
   "getting stuck" *)
  
  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string),
      match (fm_lookup st s), (fm_lookup st' s) with
      | None, None => True
      | Some f1, Some f2 => pl_equ f1 f2
      | _, _ => False
      end.
      
  Notation "a ~~ b" := (states_iso a b) (at level 70).

  (* stronger but difficult-to-prove correctness lemmas *)

  (* we may want to require these but they don't seem to be necessary for our purposes *)
  (*
  Axiom eval_det1:
    forall prg isti istf istf',
      eval isti prg istf ->
      eval isti prg istf' ->
      istf ~~ istf'.

  Axiom eval_det2 :
    forall prg isti istf istf',
      (istf ~~ istf') ->
      eval isti prg istf ->
      exists isti', isti ~~ isti' /\ eval isti' prg istf'.
   *)
  
  Axiom eval_det3 :
    forall prg isti isti' istf,
      (isti ~~ isti') ->
      eval isti prg istf ->
      exists istf', istf ~~ istf' /\ eval isti' prg istf'.

  (* relate concrete to abstract variables *)
  Parameter asReal : pl_data -> R -> Prop.

  Axiom asReal_det1 :
    forall (p : pl_data) (r r' : R),
      asReal p r ->
      asReal p r' ->
      r = r'.

  Axiom asReal_det2 :
    forall (p : pl_data) (r r' : R),
      r = r' ->
      asReal p r ->
      asReal p r'.

  (* False! Because of 0 and -0... *)
  Axiom asReal_det3 :
    forall (p p' : pl_data) (r : R),
      asReal p r ->
      asReal p' r ->
      pl_equ p p'. (* was p = p' *)

  Axiom asReal_det4 :
    forall (p p' : pl_data) (r : R),
      pl_equ p p' ->
      asReal p r ->
      asReal p' r.

  (*
  Axiom asReal_total1 :
    forall (p : pl_data),
    exists (r : R), asReal p r.
  
  Axiom asReal_total2 :
    forall (r : R),
    exists (p : pl_data), asReal p r.
   *)

  Axiom pl_eq_asReal :
    forall (p1 p2 : pl_data) (r : R),
      pl_equ p1 p2 -> asReal p1 r -> asReal p2 r.
  
  (* relate concrete to abstract states *)
  (* only care about variables mentioned in vars *)
  (* should characterize all variables *)
  Definition models (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).

  (*
  Fixpoint models' (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    match vars with
    | nil => True
    | v :: vs =>
      exists (d : pl_data),
      fm_lookup ist v = Some d /\
      asReal d (sst v) /\
      models vs ist sst
    end.
   *)

    
  (* restrict a var-map to a certain list of variables *)
  (*
  Fixpoint restrict (ist : istate) (l : list string) : istate :=
    match ist with
    | nil => ist
    | (v, d) :: ist' =>
      match in_dec string_dec v l with
      | left _ => restrict ist' l
      | right _ => (v, d) :: restrict ist' l
      end
    end.
   *)
  (*
  Variable has_only_vars : ast -> list string -> Prop.

  Axiom has_only_vars_correct1 :
    forall (prg : ast) (ist ist' : istate) (l : list string),
      has_only_vars prg l ->
      eval ist prg ist' ->
      eval (restrict ist l) prg (restrict ist' l).
   *)

  (* type of embeddings *)
  (* thought i needed a has_only_vars argument but i don't think i actually do *)
  (* Definition embedding : Type := forall (v : list string) (prg : ast), has_only_vars prg v -> Syntax.Formula. *)
  Definition embedding : Type := list string -> ast -> Syntax.Formula.

  (* probably need more correctness axioms for has_only_vars *)
    
  (* "preservation" - loosely *)
  (* this one doesn't consider terminating programs. *)
  Definition embedding_correct1 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is is' : istate) (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  Definition embedding_correct2 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed v prg))
        (Stream.Cons ls tr)).

  (* Here is a correct embedding function.
     Note that its correctness depends on the semantics being
     deterministic *)
  Definition embed_ex (v : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).


  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition HoareProgress : Prop :=
      forall s, P s -> exists s', eval s c s'.

    Definition HoarePreservation : Prop :=
      forall s, P s ->
                forall s', eval s c s' ->
                      Q s'.

    (* safety no longer needed *)

    Definition Hoare' : Prop :=
      (HoareProgress /\ HoarePreservation)%type.

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

    
  End Hoare.
End EMBEDDING.

Module Type EMBEDDING_THEOREMS.
  Declare Module M : EMBEDDING.

  Axiom states_iso_symm :
    forall (st st' : M.istate),
      M.states_iso st st' -> M.states_iso st' st.
  
  Axiom models_det1 :
    forall (v : list string) (sst : Syntax.state) (ist ist' : M.istate),
      M.models v ist sst -> M.models v ist' sst ->
      M.states_iso ist ist'.

  Axiom models_det2 :
    forall (v : list string) (sst : Syntax.state) (ist ist' : M.istate),
      M.states_iso ist ist' ->
      M.models v ist sst ->
      M.models v ist' sst.

  Axiom embed_ex_correct1 :
    M.embedding_correct1 M.embed_ex.

  Axiom embed_ex_correct2 :
    M.embedding_correct2 M.embed_ex.

  Axiom Hoare_Hoare' : forall (P : M.istate -> Prop) (c : M.ast) (Q : M.istate -> Prop), M.Hoare P c Q <-> M.Hoare' P c Q.
End EMBEDDING_THEOREMS.

Module EmbeddingProofs (M : EMBEDDING) <: EMBEDDING_THEOREMS with Module M := M.
  Module M := M.
  Import M.

  Lemma states_iso_symm :
    forall (st st' : istate),
      st ~~ st' -> st' ~~ st.
  Proof.
    induction st.
    - unfold states_iso. simpl. intros.
      specialize (H s).
      consider (fm_lookup st' s); try congruence.
    - unfold states_iso. simpl. intros.
      destruct a.
      consider (string_dec s s0); intros.
      + subst. specialize (H s0).
        consider (string_dec s0 s0); intros; try congruence.
        consider (fm_lookup st' s0); try contradiction.
        intros. apply pl_equ_symm. auto.
      + specialize (H s).
        consider (string_dec s s0); intros; try congruence.
        consider (fm_lookup st s); intros; try congruence.
        consider (fm_lookup st' s); intros; try congruence.
        apply pl_equ_symm. auto.
  Qed.

  Lemma models_det1 :
    forall (v : list string) (sst : Syntax.state) (ist ist' : istate),
      models v ist sst -> models v ist' sst ->
      ist ~~ ist'.
  Proof.
    unfold models, states_iso.
    intros.
    specialize (H s). specialize (H0 s).
    consider (In_dec string_dec s v).
    - forward_reason.
      specialize (asReal_det3 _ _ _ H3 H4).
      intro; subst. rewrite H. rewrite H0. apply pl_equ_symm. auto.
    - forward_reason. 
      rewrite H2. rewrite H1. auto.
  Qed.

  Lemma models_det2 :
    forall (v : list string) (sst : Syntax.state) (ist ist' : istate),
      ist ~~ ist' ->
      models v ist sst ->
      models v ist' sst.
  Proof.
    unfold models, states_iso.
    intros.
    split.
    - intros. specialize (H0 s). forward_reason.
      specialize (H s). rewrite H0 in H.
      consider (fm_lookup ist' s).
      + intros. exists p; split; eauto.
        eapply pl_eq_asReal; eauto.
      + contradiction. 
    - intros. specialize (H0 s). forward_reason.
      specialize (H s). rewrite H2 in H.
      consider (fm_lookup ist' s); try reflexivity; try contradiction.
  Qed.

  (* "progress" in the sense of taking into account the possibility of failure to progress *)
  Lemma embed_ex_correct1 :
    embedding_correct1 embed_ex.
  Proof.
    red.
    simpl. intros.
    exists is. exists is'.
    intuition.
  Qed.
  
  Lemma embed_ex_correct2 :
    embedding_correct2 embed_ex.
  Proof.
    red.
    intros.
    simpl. intro.
    repeat destruct H1.
    destruct H2.
    apply H0.
    generalize (models_det1 v ls is x0 H H1); intro Hmf.
    apply states_iso_symm in Hmf.
    generalize eval_det3; intro Hed3.
    specialize (Hed3  _ _ _ _ Hmf H3).
    forward_reason.
    eauto.
  Qed.

  Theorem Hoare_Hoare' : forall (P : M.istate -> Prop) (c : M.ast) (Q : M.istate -> Prop), M.Hoare P c Q <-> M.Hoare' P c Q.
  Proof.
    unfold Hoare, Hoare', HoareProgress, HoarePreservation.
    intuition; forward_reason.
    { specialize (H _ H0). destruct H. auto. }
    { specialize (H _ H0). destruct H. auto. }
    { eauto. }
  Qed.
End EmbeddingProofs.
(*
Section embedding.
  Variable ast : Type.
  Variable pl_data : Type.

  Definition istate := list (string * pl_data).
    
  Variable eval : (istate -> ast -> istate -> Prop).

  (* state utility functions *)
  (* finite map lookup *)
  (* TODO deal with discrepancy between these and fstate_lookup/fstate_set *)
  Fixpoint fm_lookup {T : Type} (l : list (string * T)) (s : string): option T :=
    match l with
    | nil => None
    | (var, val) :: l' =>
      if string_dec s var
      then Some val
      else fm_lookup l' s
    end.

  (* finite map update *)
  Fixpoint fm_update {T : Type} (l : list (string * T)) (s : string) (t : T) : list (string * T) :=
    match l with
    | nil => [(s,t)]
    | (var, val) :: l' =>
      if string_dec s var
      then (var, t) :: l'
      else (var, val) :: fm_update l' s t
    end.

  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string), fm_lookup st s = fm_lookup st' s.

  Notation "a ~~ b" := (states_iso a b) (at level 70).

  Lemma states_iso_symm :
    forall (st st' : istate),
      st ~~ st' -> st' ~~ st.
  Proof.
    induction st.
    - unfold states_iso. simpl. intros.
      auto.
    - unfold states_iso. simpl. intros.
      destruct a.
      consider (string_dec s s0); intros.
      + subst. specialize (H s0).
        consider (string_dec s0 s0); intros.
        * auto.
        * congruence.
      + specialize (H s).
        consider (string_dec s s0); intros.
        * congruence.
        * auto.
  Qed.
  
  Axiom eval_det1:
    forall prg ist ist' ist'',
      eval ist prg ist' ->
      eval ist prg ist'' ->
      ist' ~~ ist''.

  Axiom eval_det2 :
    forall prg ist ist' ist'',
      (ist' ~~ ist'') ->
      eval ist prg ist' ->
      eval ist prg ist''.

  Axiom eval_det3 :
    forall prg ist ist' ist'',
      (ist ~~ ist') ->
      eval ist prg ist'' ->
      eval ist' prg ist''.

  (* relate concrete to abstract variables *)
  Variable asReal : pl_data -> R -> Prop.

  Axiom asReal_det1 :
    forall (p : pl_data) (r r' : R),
      asReal p r ->
      asReal p r' ->
      r = r'.

  Axiom asReal_det2 :
    forall (p : pl_data) (r r' : R),
      r = r' ->
      asReal p r ->
      asReal p r'.

  Axiom asReal_det3 :
    forall (p p' : pl_data) (r : R),
      asReal p r ->
      asReal p' r ->
      p = p'.

  Axiom asReal_det4 :
    forall (p p' : pl_data) (r : R),
      p = p' ->
      asReal p r ->
      asReal p' r.

  Axiom asReal_total1 :
    forall (p : pl_data),
    exists (r : R), asReal p r.
  

  Axiom asReal_total2 :
    forall (r : R),
    exists (p : pl_data), asReal p r.
  
  (* relate concrete to abstract states *)
  (* only care about variables mentioned in vars *)
  (* should characterize all variables *)
  Definition models (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).
  
  Fixpoint models' (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    match vars with
    | nil => True
    | v :: vs =>
      exists (d : pl_data),
      fm_lookup ist v = Some d /\
      asReal d (sst v) /\
      models vs ist sst
    end.

  Lemma models_det1 :
    forall (v : list string) (sst : Syntax.state) (ist ist' : istate),
      models v ist sst -> models v ist' sst ->
      ist ~~ ist'.
  Proof.
    unfold models, states_iso.
    intros.
    specialize (H s). specialize (H0 s).
    consider (In_dec string_dec s v).
    - forward_reason.
      specialize (asReal_det3 _ _ _ H3 H4).
      intro; subst. rewrite H. rewrite H0. reflexivity.
    - forward_reason. 
      rewrite H2. rewrite H1. reflexivity.
  Qed.

  Lemma models_det2 :
    forall (v : list string) (sst : Syntax.state) (ist ist' : istate),
      ist ~~ ist' ->
      models v ist sst ->
      models v ist' sst.
  Proof.
    unfold models, states_iso.
    intros.
    split.
    - intros. specialize (H0 s). forward_reason.
      exists x. split.
      + rewrite <- H. assumption.
      + assumption.
    - intros. specialize (H0 s). forward_reason.
      rewrite <- H. assumption.
  Qed.    
    
  (* restrict a var-map to a certain list of variables *)
  Fixpoint restrict (ist : istate) (l : list string) : istate :=
    match ist with
    | nil => ist
    | (v, d) :: ist' =>
      match in_dec string_dec v l with
      | left _ => restrict ist' l
      | right _ => (v, d) :: restrict ist' l
      end
    end.

  Variable has_only_vars : ast -> list string -> Prop.

  Axiom has_only_vars_correct1 :
    forall (prg : ast) (ist ist' : istate) (l : list string),
      has_only_vars prg l ->
      eval ist prg ist' ->
      eval (restrict ist l) prg (restrict ist' l).

  (* type of embeddings *)
  (* thought i needed a has_only_vars argument but i don't think i actually do *)
  (* Definition embedding : Type := forall (v : list string) (prg : ast), has_only_vars prg v -> Syntax.Formula. *)
  Definition embedding : Type := list string -> ast -> Syntax.Formula.

  (* probably need more correctness axioms for has_only_vars *)
    
  (* "preservation" - loosely *)
  (* this one doesn't consider terminating programs. *)
  Definition embedding_correct1 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is is' : istate) (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  Definition embedding_correct2 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed v prg))
        (Stream.Cons ls tr)).

  (* Here is a correct embedding function.
     Note that its correctness depends on the semantics being
     deterministic *)
  Definition embed_ex (v : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).

  (* "progress" in the sense of taking into account the possibility of failure to progress *)
  Lemma embed_ex_correct1 :
    embedding_correct1 embed_ex.
  Proof.
    red.
    simpl. intros.
    exists is. exists is'.
    intuition.
  Qed.
  
  Lemma embed_ex_correct2 :
     embedding_correct2 embed_ex.
  Proof.
    red.
    intros.
    simpl. intro.
    repeat destruct H1.
    destruct H2.
    apply H0. exists x1.
    generalize (models_det1 v ls is x0 H H1); intro Hmf.
    generalize (eval_det3 prg x0 is x1); intro Hdt.
    apply states_iso_symm in Hmf.
    auto.
  Qed.

  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition HoareProgress : Prop :=
      forall s, P s -> exists s', eval s c s'.

    Definition HoarePreservation : Prop :=
      forall s, P s ->
                forall s', eval s c s' ->
                      Q s'.

    (* safety no longer needed *)

    Definition Hoare' : Prop :=
      (HoareProgress /\ HoarePreservation)%type.

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

    Theorem Hoare_Hoare' : Hoare <-> Hoare'.
    Proof.
      unfold Hoare, Hoare', HoareProgress, HoarePreservation.
      intuition; forward_reason.
      { specialize (H _ H0). destruct H. auto. }
      { specialize (H _ H0). destruct H. auto. }
      { eauto. }
    Qed.
  End Hoare.
End embedding.
*)

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
| FFail  : fcmd
.

Definition fupdate {T : Type} (s : Var -> T) (v : Var) (val : T) : Var -> T :=
  fun x =>
    if v ?[eq] x then val else s x.

(*Definition fzero := Eval compute in (nat_to_float 0).*)

Definition fzero : float := Fappli_IEEE.B754_zero 24 128 false.
Definition fnegzero : float := Fappli_IEEE.B754_zero 24 128 true.

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

Inductive feval : fstate -> fcmd -> fstate -> Prop :=
| FESkip : forall s, feval s FSkip s
| FESeqS : forall s s' os'' a b,
    feval s a s' ->
    feval s' b os'' ->
    feval s (FSeq a b) os''
| FEAsnS : forall s v e val,
    fexprD e s = Some val ->
    feval s (FAsn v e) ((fstate_set s v val))
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
.

Definition real_float (r : R) (f : float): Prop :=
  (F2OR f = Some r)%type.

(* Instantiate our general embedding module for our particular case *)
Module FloatEmbed : EMBEDDING.
  Definition ast := fcmd.
  Definition pl_data := float.
  Definition eval := feval.

  (* redefine inaccessible defns? *)
  (* So not DRY... *)
  Definition istate := list (string * float).

  Print EMBEDDING.

  (*
  Inductive pl_eq : pl_data -> pl_data -> Prop :=
  | pl_refl : forall (p1 : pl_data), pl_eq p1 p1
  | pl_zero1 : pl_eq fzero fnegzero
  | pl_zero2 : pl_eq fnegzero fzero
  .
   *)

  Import Fappli_IEEE.

  Inductive pl_eq : pl_data -> pl_data -> Prop :=
  | pl_zero : forall b b', pl_eq (B754_zero _ _ b) (B754_zero _ _ b')
  | pl_inf : forall b b', pl_eq (B754_infinity _ _ b) (B754_infinity _ _ b')
  | pl_nan : forall b b' p p', pl_eq (B754_nan _ _ b p) (B754_nan _ _ b' p')
  | pl_except : forall b b' p, pl_eq (B754_infinity _ _ b) (B754_nan _ _ b' p)
  | pl_refl : forall (p1 : pl_data), pl_eq p1 p1
  | pl_symm : forall p1 p2, pl_eq p1 p2 -> pl_eq p2 p1
  | pl_trans : forall p1 p2 p3, pl_eq p1 p2 -> pl_eq p2 p3 -> pl_eq p1 p3
  .

  Definition pl_equ := pl_eq.
  Hint Unfold pl_equ.
  
  Definition pl_equ_refl : forall p : pl_data, pl_equ p p := pl_refl.
        
  Definition pl_equ_trans : forall p p' p'' : pl_data, pl_equ p p' -> pl_equ p' p'' -> pl_equ p p'' := pl_trans.
    
  Definition pl_equ_symm : forall p p' : pl_data, pl_equ p p' -> pl_equ p' p := pl_symm.
  
  (*
  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string), fm_lookup st s = fm_lookup st' s.
   *)

  Definition states_iso (st st' : istate) : Prop :=
    forall (s : string),
      match (fm_lookup st s), (fm_lookup st' s) with
      | None, None => True
      | Some f1, Some f2 => pl_equ f1 f2
      | _, _ => False
      end.

  Definition states_iso' (st st' : istate) : Prop :=
    forall (s : string),
      match fm_lookup st s with
      | None => fm_lookup st' s = None
      | Some f =>
        exists f', fm_lookup st' s = Some f' /\
              F2OR f = F2OR f'
      end.

  Lemma pl_eq_F2OR :
    forall a b,
      pl_eq a b ->
      F2OR a = F2OR b.
  Proof.
    induction 1; simpl; try reflexivity; auto.
    rewrite IHpl_eq1. auto.
  Qed.

  Lemma bpow_nonzero :
    forall radix2 e, (~Fcore_Raux.bpow radix2 e = 0)%R.
  Proof.
    intros. intro.
    destruct e.
    - simpl in *. lra.
    - simpl in *.
      destruct radix2.
      generalize (Fcore_Zaux.Zpower_pos_gt_0); intro Hzpg.
      simpl in H.
      specialize (Hzpg radix_val p).
      apply Zle_bool_imp_le in radix_prop.
      assert (0 < radix_val)%Z by lia. specialize (Hzpg H0).
      apply Fcore_Raux.Z2R_lt in Hzpg.
      simpl in Hzpg. lra.
    - simpl in *.
      destruct radix2.
      simpl in H.
      generalize (Rinv_neq_0_compat (Fcore_Raux.Z2R (Z.pow_pos radix_val p))%R); intro Hin0.
      assert (~Fcore_Raux.Z2R (Z.pow_pos radix_val p) = 0)%R.
      { intro.
        generalize (Fcore_Zaux.Zpower_pos_gt_0); intro Hzpg.
        apply Zle_bool_imp_le in radix_prop.
        assert (0 < radix_val)%Z by lia.
        specialize (Hzpg radix_val p H1).
        apply Fcore_Raux.Z2R_lt in Hzpg.
        simpl in Hzpg. lra. }
      specialize (Hin0 H0).
      lra.
  Qed.
  
  Require Import ArithFacts.
  Require Import compcert.flocq.Core.Fcore_float_prop.
  
  Lemma F2OR_pl_eq :
    forall f f',
      F2OR f = F2OR f' ->
      pl_eq f f'.
  Proof.
    intros.
    unfold F2OR in H.
    consider f; consider f'; intros; subst; simpl in *; try constructor; try congruence.
    { consider b; intros; subst.
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0.
        inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0. inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. } }
    { constructor. }
    (* copypasta *)
    { consider b0; intros; subst.
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0.
        inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { simpl in *.
        unfold Fcore_defs.F2R, Fcore_Raux.Z2R, Fcore_defs.Fnum in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        simpl in H0. inversion H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. } }
    { pose proof e0 as e0'. pose proof e2 as e2'.
      unfold Fappli_IEEE.bounded in e0', e2'.
      apply Bool.andb_true_iff in e2'. apply Bool.andb_true_iff in e0'.
      forward_reason.
      inversion H1.
      generalize (Fcore_generic_fmt.canonic_unicity radix2 (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)); intro Huni.
      eapply canonic_canonic_mantissa in H2. eapply canonic_canonic_mantissa in H.
      symmetry in H5.
      specialize (Huni _ _ H2 H H5).
      inversion Huni.
      subst.
      eapply F2R_eq_reg in H5.
      consider b; consider b0; intros; subst; try solve [simpl in *; congruence].
      { simpl in H6. inversion H6.
        subst.
        clear.
        cutrewrite (eq e2 e0).
        - apply pl_refl.
        - generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros.
          auto. }
      { simpl in H6. inversion H6.
        subst.
        clear.
        cutrewrite (eq e0 e2).
        - apply pl_refl.
        - generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros. auto. } }
  Qed.
  
  Lemma states_iso_iso' : forall (st st' : istate),
      states_iso st st' <-> states_iso' st st'.
  Proof.
    intros.
    split.
    { intros. unfold states_iso, states_iso' in *.
      intro s. specialize (H s).
      consider (fm_lookup st s); intros; subst.
      { consider (fm_lookup st' s); intros; subst; try contradiction.
        apply pl_eq_F2OR in H1. eexists; split; eauto. }
      { consider (fm_lookup st' s); intros; subst; try contradiction; try reflexivity. } }
    { intros. unfold states_iso, states_iso' in *.
      intro s. specialize (H s).
      consider (fm_lookup st s); intros; subst.
      { consider (fm_lookup st' s); intros; subst.
        { apply F2OR_pl_eq. forward_reason. inversion H1. auto. }
        { forward_reason. congruence. } }
      { rewrite H0. auto. } }
  Qed.

  Definition asReal (f : float) (r : R) :=
    (F2OR f = Some r)%type.

  (* we may perhaps need a notion of validity *)
  Lemma states_iso_nil :
    forall ist,
      states_iso nil ist <-> ist = nil.
  Proof.
    split.
    - rewrite states_iso_iso'.
      intros. simpl in H.
      induction ist.
      * reflexivity.
      * simpl in H. destruct a.
        specialize (H s). simpl in *.
        consider (string_dec s s); intros; try congruence.
    - intros. subst. rewrite states_iso_iso'. unfold states_iso'. simpl. auto.
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
  
  Lemma fstate_lookup_fm_lookup :
    forall fst v,
      fstate_lookup fst v = fm_lookup fst v.
  Proof.
    induction fst.
    - reflexivity.
    - simpl. intros.
      destruct a.
      consider (v ?[eq] v0); intro; subst.
      + consider (string_dec v0 v0); try congruence.
      + consider (string_dec v v0); try congruence.
  Qed.

  Lemma pl_eq_asReal' :
    forall (p1 p2 : pl_data) (r : R),
      pl_equ p1 p2 -> (asReal p1 r <-> asReal p2 r).
  Proof.
    unfold pl_equ.
    induction 1; split; auto;
    try solve [destruct IHpl_eq; auto];
    try solve [destruct IHpl_eq1; destruct IHpl_eq2; auto].
  Qed.

  Lemma pl_eq_asReal :
    forall (p1 p2 : pl_data) (r : R),
      pl_eq p1 p2 -> asReal p1 r -> asReal p2 r.
  Proof.
    intros.
    generalize (pl_eq_asReal' p1 p2 r H). intro Hplear.
    destruct Hplear. auto.
  Qed.

  Lemma states_iso_set' :
    forall ist ist',
      states_iso ist ist' ->
      forall val val', pl_eq val val' ->
                  forall v,
                    states_iso (fstate_set ist v val) (fstate_set ist' v val').
  Proof.
    intros.
    rewrite states_iso_iso' in H. rewrite states_iso_iso'.
    unfold states_iso' in *.
    induction H0.
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists. split; reflexivity.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst.
        + forward_reason. eexists. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; auto.
            rewrite <- fstate_lookup_fm_lookup in H0. eauto.
          * auto.
        + rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; auto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    (* the following three are copy-paste of the previous block *)
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    { intros.
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        specialize (H s).
        consider (fm_lookup ist s); intros; subst.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          forward_reason.
          exists x. split.
          * rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; eauto.
            rewrite fstate_lookup_fm_lookup. eauto.
          * auto.
        + rewrite fstate_lookup_fm_lookup. rewrite H.
          rewrite <- fstate_lookup_fm_lookup.
          erewrite <- fstate_lookup_irrelevant_update; eauto.
          rewrite fstate_lookup_fm_lookup. auto. }
    (* interesting cases again *)
    { intros.
      specialize (IHpl_eq s).
      consider (string_dec v s); intros; subst.
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_update_match in IHpl_eq.
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_update_match in IHpl_eq.
        forward_reason. inversion H1; subst.
        eexists; eauto. 
      - rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_irrelevant_update; [| auto].
        rewrite <- fstate_lookup_fm_lookup in IHpl_eq. rewrite <- fstate_lookup_irrelevant_update in IHpl_eq; [|auto].
        specialize (H s). rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst.
        + rewrite <- fstate_lookup_fm_lookup.
          rewrite <- fstate_lookup_irrelevant_update; [|auto].
          rewrite fstate_lookup_fm_lookup. auto.
        + rewrite <- fstate_lookup_fm_lookup.
          rewrite <- fstate_lookup_irrelevant_update; [|auto].
          rewrite <- fstate_lookup_fm_lookup in H2.
          rewrite <- fstate_lookup_irrelevant_update in H2; auto. }
    { intros. specialize (IHpl_eq1 s). specialize (IHpl_eq2 s).
      consider (string_dec v s); intros; subst.
      - do 2 (rewrite <- fstate_lookup_fm_lookup; rewrite <- fstate_lookup_update_match).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq1; rewrite <- fstate_lookup_update_match in IHpl_eq1).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq2; rewrite <- fstate_lookup_update_match in IHpl_eq2).
        forward_reason.
        inversion H1; subst. inversion H0; subst.
        eexists.
        split; eauto. rewrite <- H2. auto.
      - do 2 (rewrite <- fstate_lookup_fm_lookup; rewrite <- fstate_lookup_irrelevant_update; [|auto]).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq1; rewrite <- fstate_lookup_irrelevant_update in IHpl_eq1; [|auto]).
        do 2 (rewrite <- fstate_lookup_fm_lookup in IHpl_eq2; rewrite <- fstate_lookup_irrelevant_update in IHpl_eq2; [|auto]).
        specialize (H s). rewrite <- fstate_lookup_fm_lookup in H.
        consider (fstate_lookup ist s); intros; subst; eauto. }
  Qed.

  Definition F2OR' (of : option float) : option R :=
    match of with
    | None => None
    | Some f => F2OR f
    end.

  Ltac fwd := forward_reason.

  Definition pl_eq_lift (of1 of2 : option float) : Prop :=
    match of1, of2 with
    | None, None => True
    | Some f1, Some f2 => pl_eq f1 f2
    | _, _ => False
    end.

  Lemma INR_gt_zero :
    forall (n : nat), (INR n >= 0)%R.
  Proof.
    induction n.
    - simpl. lra.
    - simpl.
      destruct n.
      + lra.
      + lra.
  Qed.

  (* heavy use of copypasta in this theorem *)
  (* copied from other pl_eq theorem *)
  

  (* some copypasta in here as well *)
  Lemma pl_eq_finite_eq :
    forall b0 m0 e1 e2 b1 m1 e1' e2',
      let f  := B754_finite custom_prec custom_emax b0 m0 e1 e2 in
      let f' := B754_finite custom_prec custom_emax b1 m1 e1' e2' in
      pl_eq f f' ->
      f = f'.
  Proof.
    intros.
    apply pl_eq_F2OR in H.
    unfold f, f' in *. simpl in H.
    clear f f'.
    inversion H; clear H.
    generalize (Fcore_generic_fmt.canonic_unicity radix2 (Fcore_FLT.FLT_exp (3 - custom_emax - custom_prec) custom_prec)); intro Huni.
    apply Huni in H1.
    { inversion H1; subst.
      consider b0; intros.
      { consider b1; intros.
        { simpl in H1. inversion H1. subst.
          cutrewrite (eq e2 e2'); [reflexivity|].
          generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec). intros. auto. }
        { simpl in H1. inversion H1. } }
      { consider b1; intros.
        { simpl in H1. inversion H1. }
        { simpl in H1. inversion H1. subst.
          cutrewrite (eq e2 e2'); [reflexivity|].
          generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec). intros. auto. } } }
    { eapply canonic_canonic_mantissa.
      pose proof e2 as p2.
      apply Bool.andb_true_iff in p2. fwd. auto. }
    { eapply canonic_canonic_mantissa.
      pose proof e2' as p2'.
      apply Bool.andb_true_iff in p2'. fwd. auto. }
  Qed.
  
  (* For brutal case-analysis *)
  Ltac smash :=
    let rec smash' E :=
        match E with
        | context[match ?X with | _ => _ end] =>
          match X with
          | context[match ?Y with | _ => _ end] =>
            smash' X
          | _ => consider X; intros; idtac X; subst
          end
        | context[if ?X then _ else _] =>
          consider X; intros; idtac X; subst
        end
    in
    match goal with
    | |- ?G => smash' G
    end.

    Ltac smashs := repeat smash.

    Lemma pl_finite_neq_zero :
      forall b0 m e e0 b1,
        ~(pl_eq (B754_finite custom_prec custom_emax b0 m e e0)
                (B754_zero custom_prec custom_emax b1)).
    Proof.
      intros.
      intro.
      apply pl_eq_F2OR in H. simpl in H. inversion H; clear H.
      unfold Fcore_Zaux.cond_Zopp in H1. simpl in H1.
      consider b0; intros; subst.
      { unfold Fcore_defs.F2R in H0. simpl in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
      { unfold Fcore_defs.F2R in H0. simpl in H0.
        rewrite Fcore_Raux.P2R_INR in H0.
        generalize (pos_INR_nat_of_P m); intro Hpinr.
        generalize (bpow_nonzero radix2 e); intro Hbpnz.
        generalize (Rmult_integral_contrapositive (INR (Pos.to_nat m)) (Fcore_Raux.bpow radix2 e)); intro Hric.
        destruct Hric.
        { split. lra. lra. }
        lra. }
    Qed.
    
  Lemma states_iso_fexprD :
    forall ist ist',
      states_iso ist ist' ->
      forall fx, pl_eq_lift (fexprD fx ist) (fexprD fx ist').
  Proof.
    induction fx; rewrite states_iso_iso' in H.
    { simpl. unfold pl_eq_lift.
      consider (fstate_lookup ist v); intros; subst;
      consider (fstate_lookup ist' v); intros; subst; try auto.
      { unfold states_iso' in H. specialize (H v). rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H. forward_reason.
        apply F2OR_pl_eq in H2.
        eapply pl_equ_trans. apply H2.
        rewrite <- fstate_lookup_fm_lookup in H. rewrite H in H1. inversion H1; subst.
        constructor. }
      { unfold states_iso' in H. specialize (H v).
        rewrite <- fstate_lookup_fm_lookup in H.
        rewrite -> H0 in H. fwd.
        rewrite <- fstate_lookup_fm_lookup in H.
        congruence. }
      { unfold states_iso' in H. specialize (H v).
        rewrite <- fstate_lookup_fm_lookup in H.
        rewrite H0 in H.
        rewrite <- fstate_lookup_fm_lookup in H.
        congruence. } }
    { simpl. constructor. }
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      (* begin experiment *)
      unfold fplus, Bplus.
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction].
      apply pl_eq_finite_eq in IHfx1. apply pl_eq_finite_eq in IHfx2.
      inversion IHfx1; inversion IHfx2; subst.
      apply pl_refl. }
    (* copypasta *)
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      (* begin experiment *)
      unfold fminus, Bplus, Bminus, Bplus. (* wtf *)
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence;
                 apply pl_finite_neq_zero in IHfx2; contradiction].
      { unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        inversion H7; subst; clear H7.
        inversion H2; subst; clear H2.
        cutrewrite (eq e0 e2); [apply pl_refl|].
        generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
        intros.
        auto. }
      { unfold Bopp in *; consider f0; consider f2; intros; subst; try congruence.
        apply pl_eq_finite_eq in IHfx1.
        inversion IHfx1; subst; clear IHfx1.
        inversion H2; subst; clear H2.
        inversion H7; subst; clear H7.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        apply pl_refl. } }
    (* copypasta *)
    { simpl.
      unfold pl_eq_lift in IHfx1. unfold pl_eq_lift in IHfx2.
      unfold lift2, pl_eq_lift.
      smashs; try congruence; auto.
      unfold fmult, Bmult.
      smashs; try solve [constructor]; try solve [apply pl_symm; constructor];
      try solve [apply pl_eq_F2OR in IHfx1; simpl in IHfx1; congruence];
      try solve [apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_symm in IHfx1; apply pl_finite_neq_zero in IHfx1; contradiction];
      try solve [apply pl_eq_F2OR in IHfx2; simpl in IHfx2; congruence];
      try solve [apply pl_finite_neq_zero in IHfx2; contradiction];
      try solve [apply pl_symm in IHfx2; apply pl_finite_neq_zero in IHfx2; contradiction].
      { apply pl_eq_finite_eq in IHfx1.
        inversion IHfx1; subst; clear IHfx1.
        apply pl_eq_finite_eq in IHfx2.
        inversion IHfx2; subst; clear IHfx2.
        cutrewrite (eq e0 e4).
        { cutrewrite (eq e2 e6).
          { apply pl_refl. }
          { generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
            intros.
            auto. } }
        { generalize (Coq.Logic.Eqdep_dec.UIP_dec Bool.bool_dec).
          intros.
          auto. } } }
  Qed.
  
  Lemma eval_det3 :
    forall prg isti isti' istf,
      (states_iso isti isti') ->
      eval isti prg istf ->
      exists istf', states_iso istf istf' /\ eval isti' prg istf'.
  Proof.
    induction prg.
    - intros. inversion H0; subst; clear H0.
      specialize (IHprg1 _ _ _ H H4). forward_reason.
      specialize (IHprg2 _ _ _ H0 H6). forward_reason.
      eexists. split; eauto.
      econstructor; eauto.
    - intros.
      inversion H0; subst; clear H0.
      eexists; split; eauto. econstructor.
    - intros.
      inversion H0; subst; clear H0.
      generalize (states_iso_fexprD _ _ H f); intro Hsif.
      unfold pl_eq_lift in Hsif.
      rewrite H5 in Hsif.
      consider (fexprD f isti'); intros; try contradiction.
      exists (fstate_set isti' v f0).
      split.
      + eapply states_iso_set'; auto.
      + econstructor; auto.
    - intros.
      generalize (states_iso_fexprD _ _ H f); intro Hsif.
      inversion H0; subst; clear H0.
      + specialize (IHprg1 _ _ _ H H8).
        forward_reason.
        unfold pl_eq_lift in Hsif.
        rewrite H5 in Hsif.
        consider (fexprD f isti'); intros; try contradiction.
        exists x; split; eauto.
        eapply FEIteT; eauto.
        apply pl_eq_F2OR in Hsif.
        unfold float_lt in *.
        unfold F2OR in *.
        consider f0; consider f1; intros; subst; auto; simpl in *;
        try lra; try solve [inversion Hsif; lra].
      + specialize (IHprg2 _ _ _ H H8).
        forward_reason.
        unfold pl_eq_lift in Hsif.
        rewrite H5 in Hsif.
        consider (fexprD f isti'); intros; try contradiction.
        exists x; split; auto.
        eapply FEIteF; eauto.
        apply pl_eq_F2OR in Hsif.
        unfold float_ge in *.
        unfold F2OR in *.
        consider f0; consider f1; intros; subst; auto; simpl in *;
        try lra; try solve [inversion Hsif; lra].
    - intros.
      inversion H0.
  Qed.

  Lemma asReal_det1 :
    forall (p : pl_data) (r r' : R),
      asReal p r ->
      asReal p r' ->
      r = r'.
  Proof.
    unfold asReal.
    intros. rewrite H in H0. inversion H0. auto.
  Qed.

  Lemma asReal_det2 :
    forall (p : pl_data) (r r' : R),
      r = r' ->
      asReal p r ->
      asReal p r'.
  Proof.
    intros. subst. auto.
  Qed.

  (* TODO find a different axiom to allow us to prove models_det1 *)
  
  Lemma asReal_det3 :
    forall (p p' : pl_data) (r : R),
      asReal p r ->
      asReal p' r ->
      pl_eq p p'.
  Proof.
    unfold asReal.
    intros. rewrite <- H in H0.
    apply F2OR_pl_eq in H0. apply pl_symm. auto.
  Qed.

  Lemma asReal_det4 :
    forall (p p' : pl_data) (r : R),
      pl_eq p p' ->
      asReal p r ->
      asReal p' r.
  Proof.
    intros. unfold asReal in *.
    rewrite <- H0. apply pl_eq_F2OR.
    apply pl_symm. auto.
  Qed.

  Definition models (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).

  Definition embedding : Type := list string -> ast -> Syntax.Formula.

  Definition embedding_correct1 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is is' : istate) (ls ls' : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      Semantics.eval_formula
        (embed v prg)
        (Stream.Cons ls (Stream.Cons ls' tr)).

  Definition embedding_correct2 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is : istate) (ls : Syntax.state) (tr : Stream.stream Syntax.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(Semantics.eval_formula
        (Enabled (embed v prg))
        (Stream.Cons ls tr)).

  (* Here is a correct embedding function.
     Note that its correctness depends on the semantics being
     deterministic *)
  Definition embed_ex (v : list string) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).


  (** Next, some definitions for Hoare-style reasoning about programs.
      We use this to implement weakest-precondition.
   **)
  Section Hoare.
    Variables (P : istate -> Prop) (c : ast) (Q : istate -> Prop).

    Definition HoareProgress : Prop :=
      forall s, P s -> exists s', eval s c s'.

    Definition HoarePreservation : Prop :=
      forall s, P s ->
           forall s', eval s c s' ->
                 Q s'.

    (* safety no longer needed *)

    Definition Hoare' : Prop :=
      (HoareProgress /\ HoarePreservation)%type.

    Definition Hoare : Prop :=
      (forall s, P s ->
            (exists s', eval s c s') /\
            (forall s', eval s c s' -> Q s'))%type.

  End Hoare.
  
(*End FloatEmbed.*)

  (* Convert a float state to a real state *)
  (* Assumes the floats are valid. *)

  End FloatEmbed. 
  Require Import bound.
  Import FloatEmbed.

  (* More aggressive forward reasoning tactic *)
  Ltac fwd :=
    forward_reason;
    repeat (match goal with
            | |- let '(_) := ?x in _ => consider x
            end).

  Definition fm_lookupR (fst : fstate) (v : Var) : option R :=
    match fm_lookup fst v with
    | None => None
    | Some f => F2OR f
    end.

  Definition asReal_float (f : float) (r : R) : Prop :=
    (F2OR f = Some r)%type.

  Check models.

  Definition vmodels := models.

  (** This is the semantic side condition **)
  (* slightly different way of stating models_det facts *)
  Definition SEMR (vs : list Var) (P : Syntax.state -> Prop) : Prop :=
    forall (c : istate) (a b : Syntax.state), vmodels vs c a -> vmodels vs c b -> P a -> P b.

  Definition Hoare_ := Hoare.

  (* These are no longer used; we're performing the abstraction at the level
   of fwp rather than here. This was due to underlying changes to bound.v *)
  Definition HoareA_all (vs : list string)
             (P : Syntax.state -> Prop) (c : ast) (Q : Syntax.state -> Prop)
    : Prop :=
    Hoare_ (fun fst => forall rst : Syntax.state, vmodels vs fst rst -> P rst)%type
           c
           (fun fst => forall rst : Syntax.state, vmodels vs fst rst -> Q rst)%type.

  Definition HoareA_ex (vs : list string)
             (P : Syntax.state -> Prop) (c : ast) (Q : Syntax.state -> Prop)
    : Prop :=
    Hoare_ (fun fst => exists rst : Syntax.state, vmodels vs fst rst /\ P rst)%type
           c
           (fun fst => exists rst : Syntax.state, vmodels vs fst rst /\ Q rst)%type.

  Definition fembed_ex :=
    embed_ex. 

  (*
Lemma HoareA_all_embed :
  forall P c Q vs,
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
   *)

  Require Import bound.
  Lemma Hoare__embed :
    forall P c Q vs,
      Hoare_ P c Q ->
      (|-- fembed_ex vs c -->>
           Embed (fun st st' =>
                    exists fst,
                      vmodels vs fst st /\
                      (P fst ->
                       exists fst',
                         vmodels vs fst' st' /\
                         Q fst'))).
  Proof.
    simpl. intros. unfold tlaEntails. simpl.
    intros.
    fwd.
    unfold Hoare_, Hoare in H.
    exists x. unfold vmodels. split; auto.
    intros.
    exists x0.
    split; auto.
    specialize (H _ H4). fwd.
    auto.
  Qed.

  Lemma Hoare__skip :
    forall (P : istate -> Prop),
      Hoare_ P FSkip P.
  Proof.
    red. red. intros.
    split.
    { eexists; constructor. }
    { intros. inversion H0. subst. auto. }
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
      specialize (H0 _ (H2 _ H1)).
      forward_reason.
      eexists. econstructor; eauto. }
    { intros. inversion H2; subst; clear H2.
      specialize (H _ H1). fwd.
      specialize (H2 _ H6).
      specialize (H0 _ H2).
      fwd; auto. }
  Qed.
  
  (* this plus consequence should be enough to get our real assignment rule
   that talks about bounds *)
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
    - intros. inversion H1; subst; clear H1.
      rewrite H6 in H. inversion H; subst; clear H. assumption.
  Qed.

  Require Import bound.

  (*
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
   *)

  (* Calculating bounds for expressions *)
  Fixpoint fexpr_to_NowTerm (fx : fexpr) : NowTerm :=
    match fx with
    (*| FVar v   => VarNowN (vtrans_flt2tla ivs v)*)
    | FVar v => VarNowN v
    | FConst f => FloatN f
    | FPlus fx1 fx2 =>
      PlusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    | FMinus fx1 fx2 =>
      MinusN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    | FMult fx1 fx2 =>
      MultN (fexpr_to_NowTerm fx1) (fexpr_to_NowTerm fx2)
    end.

  Definition bound_fexpr (fx : fexpr) : list singleBoundTerm :=
    bound_term (fexpr_to_NowTerm fx).

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

  Lemma fexpr_NowTerm_related_eval :
    forall fst,
    forall fx f,
      fexprD fx fst = Some f ->
      eval_NowTerm fst (fexpr_to_NowTerm fx) = Some f.
  Proof.
    induction fx; eauto;
    try (intros; simpl; simpl in *; fwd;
         unfold lift2 in *;
           consider (fexprD fx1 fst); intros; try congruence;
         consider (fexprD fx2 fst); intros; try congruence;
         erewrite IHfx1; eauto;
         erewrite IHfx2; eauto).
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
  Lemma bound_fexpr_sound : forall fx sbts,
      bound_fexpr fx = sbts ->
      (*varmap_check_fexpr ivs fx ->*)
      List.Forall (fun sbt =>
                     forall (fst : fstate) f,
                       fexprD fx fst = Some f ->
                       let '(P,Pr) := bounds_to_formula sbt fst in
                       P -> exists fval, fexprD fx fst = Some fval
                                   /\ exists val,
                             F2OR fval = Some val /\ Pr val)%type
                  sbts.
  Proof.
    intros.
    generalize (bound_proof'). intro Hbp.
    apply Forall_forall. intros.
    specialize (Hbp (fexpr_to_NowTerm fx) fst).
    fwd. intros.
    unfold bounds_to_formula, denote_singleBoundTermNew in H2.  simpl in H2.
    inversion H2; subst; clear H2.
    exists f.
    split; auto.
    unfold boundDef' in Hbp. simpl in Hbp.
    generalize (fexpr_NowTerm_related_eval _ _ _ H1); intro Hentfxd.
    rewrite Hentfxd in Hbp.
    apply Forall_forall with (x := x) in Hbp.
    - consider (floatToReal f); intros.
      + exists r. split.
        * rewrite <- H. reflexivity.
        * forward_reason. auto.
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

  (*
Lemma vmodels_irrelevant_update :
  forall (vs : list string) (v v' : Var) (s : fstate)
         (x : Syntax.state) (x1 : R) (val : float),
    vmodels vs s x ->
    ~In 
    List.Forall (fun (v : string) =>
              let '(lv, rv) := vv in 
              lv <> v' /\ rv <> v)%type vs ->
    vmodels vs (fupdate x v' x1) (fstate_set s v val).
   *)

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

  Print fstate.
  Check fstate_set.
  Check fm_update.

  Lemma fstate_set_fm_update :
    forall (f : fstate) (v : Var) (d : float),
      fstate_set f v d = fm_update f v d.
  Proof.
    induction f.
    - intros. reflexivity.
    - intros. simpl. destruct a.
      consider (v ?[eq] v0); consider (string_dec v v0); intros; subst.
      + reflexivity.
      + congruence.
      + congruence.
      + rewrite IHf. reflexivity.
  Qed.

  Lemma fstate_lookup_fm_lookup :
    forall (f : fstate) (v : Var),
      fstate_lookup f v = fm_lookup f v.
  Proof.
    induction f.
    - reflexivity.
    - intros. simpl. destruct a.
      consider (v ?[eq] v0); consider (string_dec v v0); intros; subst.
      + reflexivity.
      + congruence.
      + congruence.
      + apply IHf.
  Qed.

  (* this one is no longer true... *)
  (*
Lemma vmodels_irrelevant_update :
  forall (vs : list string) (v : Var) (s : fstate)
         (x : Syntax.state) (x1 : R) (val : float),
    vmodels vs s x ->
    List.Forall (fun (v' : string) => v <> v')%type vs ->
    vmodels vs (fstate_set s v val) (fupdate x v x1).
Proof.
  induction 2.
  - unfold vmodels, models in *. intros.
    split.
    + intros. inversion H0.
    + intros. specialize (H s0). fwd.
      
      consider (string_dec v s0).
      * subst. rewrite <- H1. rewrite <- fstate_lookup_fm_lookup. rewrite <- fstate_lookup_update_match.
      
    split.
    + intros. specialize (H s). fwd.
      congruence.
    + intros. specialize (H s).
      fwd.
      consider (string_dec s v).
      * subst.
  
  induction vs.
  - simpl. unfold vmodels, models. simpl. intros.
    split.
    + intros. contradiction.
    + intros. specialize (H v). fwd.
  
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
   *)

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

  (*
Lemma _fupdate_match :
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
   *)

  (*
Lemma varmap_check_contradiction :
  forall (vs : list string) (fe : fexpr)
         (fst : fstate) (ss : Syntax.state),
    varmap_check_fexpr vs fe ->
    vmodels vs ss fst ->
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
   *)

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

  (*
(* Checks to ensure an fstate matches given variable map *)
Fixpoint varmap_check_fstate (vs : list (Var * Var)) (fst : fstate) : Prop :=
  match vs with
  | nil => True
  | (vl, vr) :: vs' =>
    isVarValid vr fst /\ varmap_check_fstate vs' fst
  end.
   *)

  Lemma floatConstValid_toR :
    forall val,
      isFloatConstValid val -> exists r,
        (F2OR val = Some r)%type.
  Proof.
    intros.
    unfold isFloatConstValid in H.
    destruct val; try contradiction; solve [eexists; reflexivity].
  Qed.

  (*
Lemma varmap_check_contra' :
  forall (ivs : list (Var * Var)) (fst : fstate) (e : fexpr),
    varmap_check_fexpr ivs e ->
    varmap_check_fstate ivs fst ->
    exists r, (fexprD e fst = Some r)%type.
Proof.
  induction e.
  - intros. simpl in *.
    induction ivs.
    + simpl in *. fwd. contradiction.
    + fwd. simpl in *. destruct a. fwd.
      destruct H.
      * inversion H; subst; clear H.
        unfold isVarValid in H0.
        consider (fstate_lookup fst v); intros; try contradiction.
        eexists. reflexivity.
      * eapply IHivs; eauto.
  - intros.
    simpl in *. eexists. reflexivity.
  (* recursive cases; all same *)
  - simpl. intros. fwd.
    unfold lift2. rewrite H3. rewrite H2.
    eexists. reflexivity.
  - simpl. intros. fwd.
    unfold lift2. rewrite H3. rewrite H2.
    eexists. reflexivity.
  - simpl. intros. fwd.
    unfold lift2. rewrite H3. rewrite H2.
    eexists. reflexivity.
Qed.
   *)

  Print fexprD.

  (* to do: what notion of float -> R to use?? *)
  (* to do: is left or right var fstate? *)
  Lemma Hoare__bound_asn :
    forall (P : _ -> Prop) v e,
      (*var_spec_valid' ivs ->
    varmap_check_fexpr ivs e ->
    In (v, v') ivs ->*)
      Hoare_ (fun fst : fstate =>
                exists res, fexprD e fst = Some res /\
                       AnyOf (List.map (fun sbt =>
                                          let '(pred,bound) := bounds_to_formula sbt fst in
                                          pred /\ forall (val : float) (r : R),
                                              F2OR val = Some r ->
                                              bound r ->
                                              P (fstate_set fst v val))
                                       (bound_fexpr e)))%type
             (FAsn v e)
             P.
  Proof.
    intros. red; red. intros.
    fwd.
    split.
    { consider (fexprD e s); intros.
      - eexists. econstructor. eassumption.
      - congruence. }
    { intros. inversion H1; subst; clear H1.
      simpl in H0.
      generalize (bound_fexpr_sound e _ eq_refl). intro Hbfs.
      induction (bound_fexpr e).
      { simpl in *. contradiction. }
      { simpl in *. destruct H0.
        { clear IHl.
          inversion Hbfs. fwd.
          subst.
          specialize (H3 _ _ H6 H0). fwd.
          rewrite H in H1. inversion H1. subst. clear H1.
          eapply H5.
          - rewrite H in H6. inversion H6. subst. eauto.
          - lra. }
        { inversion Hbfs; subst; clear Hbfs.
          eapply IHl; eauto. } } }
  Qed.        

  (*
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
   *)

  Lemma Hoare__conseq :
    forall (P P' Q Q' : fstate -> Prop) (c : fcmd),
      (forall (st : fstate), P st  -> P' st) ->
      (forall (st : fstate), Q' st -> Q  st) ->
      Hoare_ P' c Q' ->
      Hoare_ P c Q.
  Proof.
    intros. unfold Hoare_, Hoare in *.
    intros. apply H in H2. apply H1 in H2. fwd.
    split; try eexists; eauto.
  Qed.

  (*
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
   *)

  (* perhaps unneeded *)
  (*
Lemma vmodels_must_exist :
  forall (ivs : list (Var * Var)),
    var_spec_valid' ivs ->
    forall x v,
      In (x, v) ivs ->
      forall s x0,
      vmodels ivs x0 s ->
      exists y, (fstate_lookup s v = Some y)%type.
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
   *)

  (*
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
   *)

  (* A couple of lemmas used for ITE rule *)
  Lemma Hoare__or :
    forall (P1 P2 Q : _ -> Prop) c,
      Hoare_ P1 c Q ->
      Hoare_ P2 c Q ->
      Hoare_ (fun st => P1 st \/ P2 st)%type c Q.
  Proof.
    intros.
    unfold Hoare_, Hoare in *.
    intros.
    destruct H1; eauto.
  Qed.    

  Lemma Hoare__False :
    forall (P : _ -> Prop) c,
      Hoare_ (fun _ => False) c P.
  Proof.
    intros.
    unfold Hoare_, Hoare. intros. contradiction.
  Qed.

  (*
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
   *)

  (* auxiliary functions for HoareA ITE rule *)
  (*
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
   *)


  Definition maybe_lt0 (sbts : list singleBoundTerm) (fst : fstate) : Prop :=
    AnyOf (List.map
             (fun sbt =>
                (lb sbt fst <  0)%R /\
                (premise sbt fst)) sbts).

  Definition maybe_ge0 (sbts : list singleBoundTerm) (fst : fstate) : Prop :=
    AnyOf (List.map
             (fun sbt =>
                (ub sbt fst >=  0)%R /\
                (premise sbt fst)) sbts).

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

  Lemma Hoare__bound_ite :
    forall ex (P Q1 Q2 : _ -> Prop) c1 c2,
      Hoare_ Q1 c1 P ->
      Hoare_ Q2 c2 P ->
      Hoare_ (fun fst =>
                exists res, fexprD ex fst = Some res /\
                       let bs := bound_fexpr ex in
                       (maybe_lt0 bs fst -> Q1 fst) /\
                       (maybe_ge0 bs fst -> Q2 fst) /\
                       (AnyOf (List.map
                                 (fun sbt => let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                 bs)))%type
             (FIte ex c1 c2)
             P.
  Admitted.
  (* re-prove later. *)
  (*
Proof.
  intros.
  generalize (bound_fexpr_sound ivs ex _ eq_refl H H0).
  induction 1.
  { simpl. eapply Hoare__conseq.
    3: eapply Hoare__False.
    - simpl. tauto.
    - exact (fun _ x => x). }
  { simpl. eapply Hoare__conseq.
    2: exact (fun _ x => x).
    unfold maybe_lt0. unfold maybe_ge0.
    simpl. intros.
    repeat rewrite or_distrib_imp in H5.
    repeat rewrite and_distrib_or in H5.
    eapply H5.
    eapply Hoare__conseq.
    2: exact (fun _ x => x).
    2: eapply Hoare__or.
    3: eapply IHForall.
    simpl.
    intros.
    destruct H5.
    { fwd.
      left.
      exact  (conj H8 (conj H5 (conj H6 H7))). }
    { right. tauto. }
    do 2 red. intros.
    fwd.
    generalize (varmap_check_contra' _ _ _ H0 H6); intro Hvmcc.
    fwd.
    do 2 red in H1, H2.
    specialize (H1 s). specialize (H2 s).
    specialize (H3 _ _ H9).
    simpl in H3.
    specialize (H3 H5). fwd.
    assert (x1 = x0).
    { rewrite H9 in H3. inversion H3; auto. }
    subst. clear H3.
    destruct (float_lt_ge_trichotomy x0 fzero).
    { destruct H1.
      { eapply H7.
        split; auto.
        unfold float_lt in H3.
        simpl in H3.
        unfold FloatToR in H3. unfold F2OR in H10.
        destruct x0; try congruence.
        { simpl in *. lra. }
        { simpl in *.
          inversion H10; subst; clear H10.
          lra. } }
      { split.
        { fwd. eexists. eapply FEIteT; eauto. }
        split.
        { fwd. intro. inversion H15; subst; clear H15; eauto.
          - rewrite H20 in H9. inversion H9; subst. unfold float_ge, float_lt in *. lra.
          - congruence. }
        { intros. fwd.
          eapply H15.
          inversion H14; subst; clear H14.
          - eassumption.
          - rewrite H20 in H9. inversion H9; subst; clear H9.
            unfold float_ge, float_lt in *.
            lra. } } }
    { destruct H2.
      { eapply H8.
        split; auto.
        unfold float_ge in H3.
        unfold FloatToR in H3.
        simpl in *.
        unfold F2OR in H10.
        destruct x0; try congruence.
        { simpl in *.
          inversion H10; subst; clear H10.
          lra. }
        { simpl in *. inversion H10; subst; clear H10. lra. } }
      { split.
        { fwd. eexists. eapply FEIteF; eauto. }
        split.
        { fwd. intro. inversion H15; subst; clear H15; eauto.
          - rewrite H20 in H9. inversion H9; subst. unfold float_ge, float_lt in *. lra.
          - congruence. }
        { intros. fwd.
          eapply H15.
          inversion H14; subst; clear H14.
          - rewrite H20 in H9. inversion H9; subst; clear H9.
            unfold float_ge, float_lt in *.
            lra.
          - eassumption. } } } }
Qed.
   *)

  (* Weakest-precondition calcluation function for fcmd language *)
  Fixpoint fwp (c : fcmd)
           (P : fstate  -> Prop) : fstate -> Prop :=
    match c with
    | FSkip => P
    | FSeq c1 c2 => fwp c1 (fwp c2 P)
    | FAsn v e => (fun fst  =>
                    exists res, fexprD e fst = Some res /\
                           AnyOf
                             (map
                                (fun sbt : singleBoundTerm =>
                                   let '(pred, bound) := bounds_to_formula sbt fst in
                                   pred /\
                                   (forall (val : float) (r : R),
                                       F2OR val = Some r ->
                                       bound r -> P (fstate_set fst v val)))
                                (bound_fexpr e)))
    | FFail => fun fst => False
    | FIte e c1 c2 => (fun fst =>
                        exists res, fexprD e fst = Some res /\
                               (let bs := bound_fexpr e in
                                (maybe_lt0 bs fst -> fwp c1 P fst) /\
                                (maybe_ge0 bs fst -> fwp c2 P fst) /\
                                AnyOf
                                  (map
                                     (fun sbt : singleBoundTerm =>
                                        let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                                     bs)))
    end.

  (*
Fixpoint fwp (ivs : list (Var * Var)) (c : fcmd)
         (P : {fst : fstate | varmap_check_fstate ivs fst }  -> Prop) :
  {fst : fstate | varmap_check_fstate ivs fst} -> Prop :=
  match c with
  | FSkip => P
  | FSeq c1 c2 => fwp ivs c1 (fwp ivs c2 P)
  | FAsn v e => (fun fst'  =>
                   let '(exist fst _) := fst' in
                   var_spec_valid' ivs /\
                   varmap_check_fexpr ivs e /\
                   varmap_check_fstate ivs fst /\                   
                   exists v',
                     In (v, v') ivs /\                        
                     AnyOf
                       (map
                          (fun sbt : singleBoundTerm =>
                             let '(pred, bound) := bounds_to_formula sbt fst in
                             pred /\
                             (forall (val : float) (r : R),
                                 F2OR val = Some r ->
                                 bound r -> P (fstate_set fst v' val)))
                          (bound_fexpr e ivs)))
  | FFail => fun fst' => False
  | FHavoc v => fun fst' => False
  | FIte ex c1 c2 => (fun fst' =>
                        var_spec_valid' ivs /\
                        varmap_check_fexpr ivs ex /\
                        varmap_check_fstate ivs fst /\                   
                        (let bs := bound_fexpr ex ivs in
                         (maybe_lt0 bs fst -> fwp ivs c1 P fst) /\
                         (maybe_ge0 bs fst -> fwp ivs c2 P fst) /\
                         AnyOf
                           (map
                              (fun sbt : singleBoundTerm =>
                                 let '(prem, _) := denote_singleBoundTermNew fst sbt in prem)
                              bs)))
  end.
   *)

  Lemma fwp_correct :
    forall c P,
      Hoare_ (fwp c P)
             c
             P.
  Proof.
    intros c.
    induction c; intros; eauto using Hoare__False.
    { eapply Hoare__seq.
      Focus 2.
      eapply IHc2; eauto.
      simpl.
      eapply Hoare__conseq.
      3: eapply IHc1; eauto.
      2: exact (fun _ x => x).
      intros; eassumption.
    }
    { eapply Hoare__skip. }
    { eapply Hoare__bound_asn. }
    { eapply Hoare__bound_ite; eauto. }
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
   *)

  (*
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

