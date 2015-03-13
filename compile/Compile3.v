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

Definition c_eval (si : fstate) (pr : progr) (sf : fstate) : Prop :=
  (eval_progr pr si = Some sf)%type.

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
      

(* TODO strict or non-strict inequalities? *)
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

Print Formula.
Print singleBoundTerm.
Check bound_term.

Check cross.

Check fold_right.

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


(* Strongest postcondition calculation, starting from TRUE.
   We need a language of assertions that supports rewriting *)

(* alternate idea: have abstractor produce not a formula, but
   a (String -> Expr) -> Formula. Parameterized over substitution. *)

(* do this weird language thing and then yeah soundness *)

(* or, dont do the language thing. Need sp function for strongest
   postcondition calculation (src -> (tlastate -> prop) -> (tlastate -> prop)).
   or even use Formula instead of prop. Maybe (var -> expr) -> formula *)

(* strongest postcondition calculations *)
Print progr_assn.

(* x gets xold; otherwise apply subs *)
(* need to do rewriting in nowterms *)

(* strongest precondition calculation for a single program assignment *)
Require Import ExtLib.Core.RelDec.
Print mk_progr_assn.

(* better to think of this type as assn -> ((Var -> NowTerm) -> Formula) : (Var -> NowTerm) -> Formula *)

(* build a C-style language - assignment, sequencing, ITE *)
                                             
(* Perform substitution for a single program assignment *)

Print Formula.
Print Syntax.Term.
Check Comp.
Print CompOp.
Check Syntax.Exists.
Print fstate_set.
Print Syntax.state.

Definition sp_assn (assn : progr_assn) (P : Syntax.state -> Formula) : Syntax.state -> Formula :=
  let '(mk_progr_assn x e) := assn in
  (fun s =>
     Syntax.Exists R (fun (v : R) =>
                        And (Comp (denowify e) (RealT v) Eq)
                            (P (fun x' => if x ?[ eq ] x' then v else s x')))).
                                       

(* original proposal, with fstate as a function *)
(* (P (fun x' => if x ?[ eq ] x' then v else fs x')))).*)

(**************************************************************
Beyond this is mostly dead code...
***************************************************************)
                        

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
intros.
        

Lemma compile_progr_stmt_correct :
  forall (sf sf' : fstate) (stmt : progr_stmt),
    eval_progr_stmt stmt sf = Some sf' ->
    forall (tr : Semantics.trace)
           (sr sr' : Syntax.state),
      sr  ~=~ sf  ->
      sr' ~=~ sf' ->
      eval_formula (compile_progr_stmt stmt) (sr ::: sr' ::: tr).
Proof.
intros.
destruct stmt eqn:Hstmt; simpl.
specialize (

(* have program compile trivially (FALSE or TRUE) if you fail a check
   that is, if you try to look up undefined variables in the float state
   or you try to assign two values into the same variable at once *)


(*
(* updates all the states in the given real state with values drawn from
   finite map new_sf *)

Definition update_floats (sr : Syntax.state) (new_sf : fstmap) : Syntax.state :=
  match new_sf with
    | nil => sr
    | (name, val) :: rest =>
      (fun v =>
         if String.string_dec v name
         then FloatToR val
         else sr v)
  end.
*)

Require Import ExtLib.Core.RelDec.

(* compilation to TLA *)
(* TODO need to be able to handle conditionals to do this *)
(*
Fixpoint progr_stmts_to_tla (stmts : list progr_stmt) (st : rbstate) : Formula :=
  match pss with
    | mk_progr_stmt conds assns =>
      let conjuncts :=
          List.app (List.map convert_assn assns)
                   [(deflatten_formula conds)] in
      self_foldr And conjuncts FALSE
  end.

Definition progr_to_tla (pr : progr) : Formula :=
  let disjuncts :=
      List.map progr_stmt_to_tla pr in
  self_foldr Or disjuncts FALSE.
*)

(*
Definition derp : progr :=
  ([PIF (FTRUE  /\
        (FloatN 1 = FloatN 1))
   PTHEN ["ab" !!= FloatN 1]])%SL.
*)

