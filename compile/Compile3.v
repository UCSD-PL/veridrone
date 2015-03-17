Require Import source.

(*Require Import bound.*)
Require Import Coq.micromega.Psatz.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import TLA.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Traversable. (* for sequence function *)
Require Import ExtLib.Data.List.
Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.

Local Close Scope HP_scope.
Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.

Require Import bound.

(*Axiom getBound : NowTerm -> list (Term * Term * Formula)%type.*)

(* need a predicate for "begins with a transition from s1 to s2" *)
Fixpoint stream_begins {A : Type} (astream : stream A) (alist : list A) : Prop :=
  match alist with
    | nil => True
    | a :: rest =>
      match astream with
        | Cons a' rest' => and (a = a') (stream_begins rest' rest)
      end
  end.

(* vignesh's correctness lemma takes
   - trace
   - NowTerm
   - newBound expr (Semantics.hd tr) (Semantics.hd (Semantics.tl tr))
   - newBound :: NowTerm -> Semantics.state -> Semantics.trace -> Prop
*)

(* c_ means "concrete" *)
Definition c_asReal (s : fstate) (v : Var) : option R :=
  match fstate_lookup s v with
    | Some f => Some (FloatToR f)
    | None   => None
  end.

Definition c_eval (si : fstate) (pr : SrcProg) (sf : fstate) : Prop :=
  (eval_SrcProg pr si = Some sf)%type.

Require Import Embed.

Definition c_models (vars : list (Var * Var)) (tla_st : Syntax.state) (fst : fstate) : Prop :=
  Embed.models Var fstate c_asReal vars tla_st fst.

Require Import bound.

(* generate an identity var-map for use by models *)
Fixpoint gen_id_varmap (fst : fstate) : list (Var * Var) :=
  match fst with
    | nil => nil
    | (hvar, _) :: t =>
      (hvar, hvar) :: gen_id_varmap t
  end.

(* We can define real_st_subsumes_float_st in terms of Embed primitives, or not.
   For now, let's not. *)
(*
Definition real_st_subsumes_float_st (tla_st : Syntax.state) (fst : fstate) : Prop :=
  c_models (gen_id_varmap fst) tla_st fst.
*)

Definition real_st_subsumes_float_st
           (tla_st : Syntax.state) (fst : fstate) : Prop :=
  forall (v : Var) (f : source.float),
  In (v, f) fst -> Some (tla_st v) = floatToReal f.

Notation "a ~=~ b" := (real_st_subsumes_float_st a b) (at level 80).

(*
  Forall (fun vf => let '(v, f) := vf in
                    eq (FloatToR f) (tla_st v)) fst.
*)

Notation "a ::: b" := (Cons _ a b) (at level 79, right associativity).

Lemma fstate_lookup_In :
  forall (flst : fstate) (x : Var) (y : source.float),
    fstate_lookup flst x = Some y -> In (x, y) flst.
Proof.
  
  induction flst.
  intros. simpl. inversion H.
  {
    intros.
    simpl in H.
    destruct a eqn:Ha.
    destruct (RelDec.rel_dec x v) eqn:Hrd.
    {
      inversion H.
      subst.
      unfold RelDec.rel_dec in Hrd.
      simpl in Hrd.
      apply String.string_dec_sound in Hrd.
      subst.
      constructor.
      reflexivity.
    }
    {
      simpl. right.
      apply IHflst. auto.
    }
  }
Qed.

Lemma related_subsumption :
  forall (flst : fstate) (rst : Syntax.state),
    rst ~=~ flst -> related flst rst.
Proof.
  intros. unfold related.
  intros.
  unfold real_st_subsumes_float_st in H.
  apply H.
  simpl.
  apply fstate_lookup_In.
  assumption.
Qed.

Lemma getBound_correct: 
  forall (nt : NowTerm) (bounds : list singleBoundTerm)
         (bound : singleBoundTerm),
    bound_term nt = bounds ->
    In bound bounds ->
    forall flst rst rst_next tr float_res real_res,
      rst ~=~ flst ->
      eval_formula (premise bound) (rst ::: rst_next ::: tr) ->
      eval_NowTerm flst nt = Some float_res ->
      floatToReal float_res = Some real_res ->
      (eval_term (lb bound) rst rst_next <=
       real_res <=
       eval_term (ub bound) rst rst_next)%R.
Proof.
  generalize bound_proof'. intro BP.
  intros.
  specialize (BP (rst ::: rst_next ::: tr) nt flst).
  simpl in BP.
  apply related_subsumption in H1.
  generalize H1. intro H1'.
  apply BP in H1.
  unfold boundDef' in H1.
  rewrite H3 in H1.
  rewrite H4 in H1.
  eapply Forall_forall in H1.
  unfold denote_singleBoundTerm in H1. simpl in H1.
  eapply H1. eassumption.
  subst. eassumption.
Qed.

Fixpoint bounds_to_formula (bounds : list singleBoundTerm) (center : Term) : Formula :=
  match bounds with
    | nil => TRUE
    | (mkSBT lb ub side) :: bounds' =>
      And (bounds_to_formula bounds' center)
          (Imp side (And (Comp lb center Le)
                         (Comp center ub Le)))
  end.
      


(* Fold a list with its first element as starting accumulator
Takes function and list, as well as default element to return if list is nil *)
Definition self_foldr {A : Type} (f : A -> A -> A) (l : list A) (dflt : A) : A :=
  match l with
    | nil => dflt
    | h :: t =>
      List.fold_right f h t
  end.

(* bound comparison operation with a single bound *)
Definition singleBound_comp (op : CompOp) (t1 t2 : singleBoundTerm) : list Formula :=
  match op with
    | Gt => Comp (ub t1) (lb t2) Gt
    | Ge => Comp (ub t1) (lb t2) Ge
    | Lt => Comp (lb t1) (ub t2) Lt
    | Le => Comp (lb t1) (ub t2) Le
    | Eq => And
              (Comp (ub t1) (lb t2) Ge)
              (Comp (ub t2) (lb t1) Ge)
  end :: nil.

(* Emit bounds for a comparison, guarding a body *)
Definition bound_comp (op : CompOp) (t1 t2 : NowTerm) : Formula :=
  let forms :=
      cross (singleBound_comp op) (bound_term t1) (bound_term t2)
  in self_foldr And forms FALSE.

(* TODO we can probably do a smarter job with these bounds
   for AND and OR (we aren't using all the information we
   potentially have, thought we may not need to)*)
Fixpoint abstr_if (conds : FlatFormula) (body : Formula) : Formula :=
  match conds with
    | FTRUE          => body
    | FFALSE         => TRUE
    | FComp t1 t2 op => And (bound_comp op t1 t2) body 
    | FAnd  f1 f2    => And (abstr_if f1 body)
                            (abstr_if f2 body)
    | FOr   f1 f2    => Or  (abstr_if f1 body)
                            (abstr_if f2 body)
  end.

(* previous attempts at abstraction function for old source language *)
(*
Definition abstr_assn (assn : progr_assn) : Formula :=
  match assn with
    | mk_progr_assn var term => bounds_to_formula (bound_term term)
                                                  (VarNextT var)
  end.

Fixpoint abstr_assns (assns : list progr_assn) : Formula :=
  match assns with
    | nil         => TRUE
    | a :: assns' =>
      And (abstr_assn a)
          (abstr_assns assns')
  end.


Definition abstr_progr_stmt (stmt : progr_stmt) : Formula :=
  match stmt with
    | mk_progr_stmt conds assns =>
      abstr_if conds (abstr_assns assns)
  end.

Fixpoint abstr_progr_stmts (stmts : list progr_stmt) : Formula :=
  match stmts with
    | nil => TRUE
    | st :: rest =>
      Or (abstr_progr_stmt st)
         (abstr_progr_stmts rest)
  end.
*)

(* Lemma relating behavior of boundDef to bounds_to_formula *)
Lemma forall_cons_iff : 
  forall T P l ls,
    @Forall T P (l :: ls) <->
    P l /\ @Forall T P ls.
Proof.
  intros.
  split; inversion 1. subst; tauto.
  constructor; tauto.
Qed.

Lemma boundDef_bounds_to_formula :
  forall (tr : trace) (t : Term) (bounds : list singleBoundTerm),
    List.Forall (fun sbt => eval_formula 
                              (Imp sbt.(premise) (And (Comp sbt.(lb) t Le)
                                                      (Comp t sbt.(ub) Le))) tr) bounds
    <->
    eval_formula (bounds_to_formula bounds t) tr.
Proof.
induction bounds.
{
  split; constructor.
}
{
  rewrite forall_cons_iff.
  rewrite IHbounds.
  destruct a.
  simpl.
  rewrite and_comm.
  reflexivity.
}
Qed.

Lemma in_fstate_set :
  forall sf v f,
    In (v, f) (fstate_set sf v f).
Proof.
intros.
induction sf; simpl; intuition.
destruct (RelDec.rel_dec v a0); simpl; tauto.
Qed.

Lemma fstate_set_subsumed :
  forall (sr' : Syntax.state) (sf : fstate) (v : Var) (f : source.float) (r : R),
    sr' ~=~ fstate_set sf v f ->
    Some r = floatToReal f ->
    sr' v = r.
Proof.
  intros.
  unfold real_st_subsumes_float_st in H.
  cut (Some (sr' v) = Some r).
  {
    intro H'. inversion H'. reflexivity.
  }
  rewrite H0.
  apply H.
  apply in_fstate_set.
Qed.

Require Import RelDec.

(* compute "not" of a Flat Formula *)
Fixpoint FlatFormula_not (ff : FlatFormula) : FlatFormula :=
  match ff with
    | FTRUE            => FFALSE
    | FFALSE           => FTRUE
    | FAnd f1 f2       => FOr  (FlatFormula_not f1) (FlatFormula_not f2)
    | FOr  f1 f2       => FAnd (FlatFormula_not f1) (FlatFormula_not f2)
    | FComp lhs rhs op =>
      match op with
        | Gt => FComp lhs rhs Le
        | Ge => FComp lhs rhs Lt
        | Lt => FComp lhs rhs Ge
        | Le => FComp lhs rhs Gt
        | Eq => FOr (FComp lhs rhs Gt)
                    (FComp lhs rhs Lt)
      end
  end.

(* TODO make sure this actually works well *)
Definition sp_ITE_comp (op : CompOp) (lhsb rhsb : singleBoundTerm) : list Formula :=
  let '(mkSBT llo lup lprem) := lhsb in
  let '(mkSBT rlo rup rprem) := rhsb in
  Imp (And lprem rprem)
      (match op with
        | Gt => Comp rlo lup Lt
        | Ge => Comp rlo lup Le
        | Lt => Comp llo rup Lt
        | Le => Comp llo rup Le
        | Eq => And (Comp lup rlo Ge)
                    (Comp rup llo Ge)
      end) :: nil.

(* Helper function for computing strongest postcondition for conditionals *)
Fixpoint sp_ITE (cond : FlatFormula) (P : Syntax.state -> Formula) : Syntax.state -> Formula :=
  match cond with
    | FTRUE            => P
    | FFALSE           => fun s => FALSE
    | FAnd f1 f2       => fun s => And (sp_ITE f1 P s) (sp_ITE f2 P s)
    | FOr  f1 f2       => fun s => Or  (sp_ITE f2 P s) (sp_ITE f2 P s)
    | FComp lhs rhs op =>
      fun s =>
        And
          (P s)
          (fold_right And TRUE
                      (cross (sp_ITE_comp op) (bound_term lhs) (bound_term rhs)))
  end.

(* Strongest-postcondition calculation for source-language programs *)
Fixpoint sp_SrcProg (sp : SrcProg) (P : Syntax.state -> Formula) : Syntax.state -> Formula :=
  match sp with
    | SAssn lhs rhs  =>
      (fun s =>
         Syntax.Exists R (fun (v : R) =>
                            And (bounds_to_formula (bound_term rhs) (s lhs))
                                (P (fun x' => if lhs ?[ eq ] x' then v else s x'))))

    | SSkip          => P
    | SSeq sp1 sp2   => sp_SrcProg sp2 (sp_SrcProg sp1 P)
    | SITE c sp1 sp2 => (* TODO - can we do better on these bounds for conditional? *)
      (fun s =>
         Syntax.Or
           (sp_SrcProg sp1 (sp_ITE c                   P) s)
           (sp_SrcProg sp2 (sp_ITE (FlatFormula_not c) P) s))
  end.

Local Open Scope string_scope.

Definition testProg :=
   (SIF ("a" < "c") STHEN "a" !!= "b" SELSE SSkip)%SL.

Eval simpl in
    (sp_SrcProg testProg (fun _ => TRUE)).

(* old SP implementations; deprecated *)
(*
Definition sp_assn (assn : progr_assn) (P : Syntax.state -> Formula) : Syntax.state -> Formula :=
  let '(mk_progr_assn x e) := assn in
  (fun s =>
     Syntax.Exists R (fun (v : R) =>
                        And (Comp (denowify e) (RealT v) Eq)
                            (P (fun x' => if x ?[ eq ] x' then v else s x')))).

Fixpoint sp_assns (assns : list progr_assn) (P : Syntax.state -> Formula) : Syntax.state -> Formula :=
  match assns with
    | nil => fun _ => TRUE
    | assn :: rest => sp_assns rest (sp_assn assn P)
  end.

Print progr_stmt.

Definition sp_if (ps : progr_stmt) (P : Syntax.state -> Formula) : Syntax.state -> Formula :=
  let '(mk_progr_stmt cond assns) := ps in
  (fun s =>
     Syntax.Or
       (subst_progr_assn_seq)
       (Imp (deflatten_formula conds) FALSE)).
*)
(* I'm still working on getting this lemma to the point where
   it is provable --Mario *)
(*
Lemma compile_assn_correct :
  forall (assn : progr_assn) (sf sf' : fstate),
    assn_update_state assn sf = Some sf' ->
    forall (tr : Semantics.trace)
           (sr sr' : Syntax.state),
      sr  ~=~ sf  ->
      sr' ~=~ sf' ->
      eval_formula (abstr_assn assn) (sr ::: sr' ::: tr).
Proof.
intros.
destruct assn eqn:Hassn; simpl.
Check getBound_correct.
specialize (fun (bound : singleBoundTerm)
                (Hin : In bound (bound_term pa_source))
                (fl_res : source.float) (r_res : R)  =>
              getBound_correct pa_source (bound_term pa_source)
                               bound eq_refl
                               Hin sf sr sr' tr fl_res r_res H0).
intro Hgb_corr.

unfold assn_update_state in H.
destruct (eval_NowTerm sf (source.pa_source (pa_dest !!= pa_source))) eqn:Hevalsf;
try (solve [inversion H]).
inversion H; clear H; subst sf'.
simpl in Hevalsf.
apply boundDef_bounds_to_formula.
apply Forall_forall. intros.
simpl. intro.
destruct (floatToReal f) eqn:F2Rf.
{
  specialize (Hgb_corr x H f r H2 Hevalsf).
  unfold eval_comp.
  cut ((eval_term (pa_dest!)%HP sr sr') = r).
  {
    intro. rewrite H3.
    auto.
  }
  simpl.
  eapply fstate_set_subsumed.
  apply H1. symmetry. assumption.
}
{
  elimtype False.
  unfold real_st_subsumes_float_st in H1.
  cut (exists v, (eq (Some (sr' v)) (floatToReal f))).
  {
    intros.
    inversion H3.
    rewrite <- H4 in F2Rf.
    inversion F2Rf.
  }
  eexists.
  apply H1.
  apply in_fstate_set.
}
Qed.
*)  

(**************************************************************
Beyond this is mostly dead code...
***************************************************************)
                        
(*
Definition subst_progr_assn (assn : progr_assn) (P : (Var -> NowTerm) -> Formula) (subs : Var -> NowTerm) : Formula :=
  let '(mk_progr_assn x e) := assn in
  let newsubs :=
      (fun (v : Var) => if  v ?[ eq ] x then e else subs v)
  in
  Syntax.Exists Var
    (fun x_old =>
       And
         (P newsubs)
         (Comp (VarNowT x)
               (denowify (subst_NowTerm e x x_old)) Eq)).

Fixpoint subst_progr_assn_seq (assns : list progr_assn) (P : (Var -> NowTerm) -> Formula) (subs : Var -> NowTerm) : Formula :=
  match assns with
    | nil       => P subs
    | a :: rest =>
      subst_progr_assn_seq
        rest (subst_progr_assn a P) subs
  end.

Print progr_stmt.
Print Formula.

Definition subst_progr_assn_if (ps : progr_stmt) (P : (Var -> NowTerm) -> Formula) (subs : Var -> NowTerm) : Formula :=
  let '(mk_progr_stmt conds assns) := ps in
  Or
    (subst_progr_assn_seq
       assns (fun subs' => And (P subs')
                               (deflatten_formula conds)) subs)
    (Imp (deflatten_formula conds) FALSE).

And (fun subs' => P subs') ())

(* insert x into bounds for e. but i need to do substitution first *)
(* function to do substitution in NowTerms needed *)

Fixpoint subst_progr_assns (assns : list progr_assn) (P : (Var -> NowTerm) -> Formula) (subs : Var -> NowTerm) : Formula :=
  match assns with
    | nil          => P subs
    | assn :: rest => 
      subst_progr_assns rest (subst_progr_assn assn P) subs
  end.

(* exists xold, p[lhs -> xold] /\ lhs = rhs[lhs -> xold] *)

Definition compile_assns'

Print compile_assns.
Print compile_assn.
Print bounds_to_formula.
Print assns_update_state.
Definition strongest_postcondition_assn (progr_assn -> 


(* well formedness of assns? *)
Lemma compile_assns_correct :
  forall (assns : list progr_assn) (sf sf' : fstate),
    assns_update_state assns sf = Some sf' ->
    forall (int tr : Semantics.trace)
           (sr sr' : Syntax.state),
      sr  ~=~ sf  ->
      sr' ~=~ sf' ->
      eval_formula (compile_assns assns) (sr ::: sr' ::: tr).
Proof.
induction assns.
simpl; constructor.
{
  intros.
  unfold assns_update_state in H.
  destruct (assn_update_state a sf) eqn:Haus.
  {
    fold assns_update_state in H.
    unfold compile_assns.
    fold compile_assns.
    simpl.
    split.
    {
      (* need to compute some update real states? *)
      eapply compile_assn_correct.
      eassumption.
      eassumption.
eassumption.
      
      
    apply IHassns with (sr := sr) (sr' := sr') (tr := tr) in H.
    - split.
      {
        apply compile_assn_correct with (sf := sf) (sf' := f).
        - assumption.
        - assumption.
        - admit.
      }
    -
  
  
}
*)
