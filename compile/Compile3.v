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
  forall (v : Var) (f : Floats.float),
  In (v, f) fst -> tla_st v = FloatToR f.

Notation "a ~=~ b" := (real_st_subsumes_float_st a b) (at level 80).

(*
  Forall (fun vf => let '(v, f) := vf in
                    eq (FloatToR f) (tla_st v)) fst.
*)

Notation "a ::: b" := (Cons _ a b) (at level 79, right associativity).


Axiom getBound_correct: 
  forall (nt : NowTerm) (bounds : list singleBoundTerm)
         (bound : singleBoundTerm),
    bound_term nt = bounds ->
    In bound bounds ->
    forall flst rst rst_next tr res,
      rst ~=~ flst ->
      eval_formula (premise bound) (rst ::: rst_next ::: tr) ->
      eval_NowTerm flst nt = Some res ->
      (eval_term (lb bound) rst rst_next <=
       FloatToR res <=
       eval_term (ub bound) rst rst_next)%R.  

Fixpoint bounds_to_formula (bounds : list singleBoundTerm) (center : Term) : Formula :=
  match bounds with
    | nil => TRUE
    | (mkSBT lb ub side) :: bounds' =>
      And (bounds_to_formula bounds' center)
          (Imp side (And (Comp lb center Le)
                         (Comp center ub Le)))
  end.
      

(* TODO strict or non-strict inequalities? *)
Definition compile_assn (assn : progr_assn) : Formula :=
  match assn with
    | mk_progr_assn var term => bounds_to_formula (bound_term term) (VarNextT var)
  end.

Fixpoint compile_assns (assns : list progr_assn) : Formula :=
  match assns with
    | nil         => TRUE
    | a :: assns' =>
      And (compile_assn a)
          (compile_assns assns')
  end.

Definition compile_progr_stmt (stmt : progr_stmt) : Formula :=
  match stmt with
    | mk_progr_stmt conds assns =>
      And (deflatten_formula conds)
          (compile_assns assns)
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

Lemma compile_assn_correct :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update_state assn sf = Some sf' ->
    forall (tr : Semantics.trace)
           (sr sr' : Syntax.state),
      sr  ~=~ sf ->
      sr' ~=~ sf' ->
      eval_formula (compile_assn assn) (sr ::: sr' ::: tr).
Proof.
intros.
destruct assn eqn:Hassn; simpl.
specialize (fun (bound : singleBoundTerm)
                (Hin : In bound (bound_term pa_source))
                (res : Floats.float)  =>
              getBound_correct pa_source (bound_term pa_source)
                               bound eq_refl
                               Hin sf sr sr' tr res H0).
intro Hgb_corr.

unfold assn_update_state in H.
destruct (eval_NowTerm sf (source.pa_source (pa_dest !!= pa_source))) eqn:Hevalsf;
try (solve [inversion H]).
inversion H; clear H; subst sf'.
simpl in Hevalsf.
apply boundDef_bounds_to_formula.
apply Forall_forall. intros.
simpl. intro.
specialize (Hgb_corr x H f H2 Hevalsf).
unfold eval_comp.
cut ((eval_term (pa_dest!)%HP sr sr') = FloatToR f).
{
  intro. rewrite H3.
  assumption.
}
simpl.
apply H1.


apply in_fstate_set.
Qed.

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
