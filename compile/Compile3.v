Require Import source.

(*Require Import bound.*)

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

Check @Embed.models.

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


Axiom getBound_correct: 
  forall (nt : NowTerm) (bounds : list singleBoundTerm)
         (bound : singleBoundTerm),
    bound_term nt = bounds ->
    In bound bounds ->
    forall flst rst rst_next tr res,
      rst ~=~ flst ->
      stream_begins tr [rst; rst_next] ->
      eval_formula (premise bound) tr ->
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

Print boundDef'.
Check Forall.
Check bound_term.

(* Lemma relating behavior of boundDef to bounds_to_formula *)
Lemma boundDef_bounds_to_formula :
  forall (nt : NowTerm) (tr : trace) (fst : fstate),
    boundDef' nt tr fst <->
    eval_formula (bounds_to_formula (bound_term nt)) tr.

Check c_models.
Print boundDef.
(* define c_models so its stronger  *)
Lemma compile_assn_correct :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update_state assn sf = Some sf' ->
    forall (tr : Semantics.trace)
           (sr sr' : Syntax.state)
           (vm : list (Var * Var)),
      sr  ~=~ sf ->
      sr' ~=~ sf' ->
      stream_begins tr [sr; sr'] ->
      eval_formula (compile_assn assn) tr.
Proof.
intros.
destruct assn; simpl; subst.
remember tr as tr0.
destruct tr as [t1 [t2 tr]].
generalize H2; intro Hbeg.
simpl in H2. rewrite Heqtr0 in H2. destruct H2 as [Hsr [Hsr' _]].
subst sr sr'.
specialize (fun (bound : singleBoundTerm)
                (Hin : In bound (bound_term pa_source))
                (res : Floats.float)  =>
              getBound_correct pa_source (bound_term pa_source) bound eq_refl
                               Hin sf t1 t2 tr0 res H0 Hbeg).
intro Hgb_corr.

unfold assn_update_state in H.
destruct (eval_NowTerm sf (source.pa_source (pa_dest !!= pa_source))) eqn:Hevalsf;
try (solve [inversion H]).
{
  inversion H; clear H; subst sf'.
  simpl in Hevalsf.
  unfold real_st_subsumes_float_st in H0, H1.
  subst.
  Print eval_NowTerm.
  unfold bounds_to_formula.
  unfold eval_formula.
  
  induction pa_source. simpl.
  split. constructor.
  intro. unfold eval_comp.
  eapply Hgbc.
  unfold bounds_to_formula.
  simpl.
}
{
  inversion H.
}
  
Destr
Print assn_update_state.

unfold eval_formula.
simpl.

(* we need float_bounds *)

(* problem this only works for the discrete part of our state *)

(* we need to bridge tla and c basically. we need to treat tla variables
   and c variables separately *)


(* have program compile trivially (FALSE or TRUE) if you fail a check
   that is, if you try to look up undefined variables in the float state
   or you try to assign two values into the same variable at once *)

Definition fstmap := list (Var * Floats.float).

(*
Definition real_st_subsumes_float_st (sr : Semantics.state) (sf : fstmap) : Prop :=
  forall (v : Var),
    in_fstmap sf v ->
    real_in_float (sr v) (sf v).
*)


(* updates all the states in the given real state with values drawn from
   finite map new_sf *)

SearchAbout (String.string -> String.string -> _).

Definition update_floats (sr : Syntax.state) (new_sf : fstmap) : Syntax.state :=
  match new_sf with
    | nil => sr
    | (name, val) :: rest =>
      (fun v =>
         if String.string_dec v name
         then FloatToR val
         else sr v)
  end.

(* THIS IS THE RIGHT ONE *)
(*
Lemma compile_assn_correct_new :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update sf = sf' ->
    forall (tr : trace) (sr : Syntax.state),
      real_st_subsumes_float_st sr sf ->
      stream_begins tr [sr; update_floats sr sf'] ->
      forall (rbst : rbstate),
        float_st_in_bound_st sf rbst ->
        eval_formula (convert_assn assn rbst) tr.
*)

Require Import ExtLib.Core.RelDec.

Definition float_st_to_real_st (sf : fstate) : Syntax.state :=
  (fun v => FloatToR (sf v)).

Lemma convert_assn_correct :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update_state assn sf = sf' ->
    forall (tr : Semantics.trace)
           (sr : Syntax.state),
      real_st_in_float_st sr  sf ->
      stream_begins tr [sr; float_st_to_real_st sf'] -> (*TODO implement *)
      forall (rbst : rbstate),
        float_st_in_bound_st sf rbst ->
        eval_formula (convert_assn assn rbst) tr.

Proof.
intros.
destruct assn; subst; simpl.
destruct (getBound rbst pa_source) eqn:gb.
Check gb.
destruct p.
simpl.
intro.
destruct tr as [nowst [nextst trt]].
simpl. simpl in H1.
inversion H1; clear H1. inversion H4. clear H4. clear H5.
subst.
unfold Semantics.eval_comp.
simpl.
eapply getBound_correct with
  (nt := pa_source)
  (flst := sf) (rst_next := nextst)
  in gb.
  (* first, prove our conclusion from conclusion of
     getBound_correct *)
  - inversion gb. clear gb.
    split.
    induction t.
    simpl. simpl in H2.
    unfold real_st_in_float_st in *.
    specialize H0 with v.

    SearchAbout real_in_float.
    apply real_in_float_
.
    Check real_in_float_correct.
    
    (* FUNDAMENTALLY right now my issue is
       strict or non-strict inequality *)
    
(*
    unfold float_st_in_bound_st in *.
    eapply H3 in H0.
*)

    assert (FloatToR (eval_NowTerm pa_source0 sf) = eval_term t nowst nextst).
    admit.
    split.
    rewrite <- H5.
    split.
    + 

(* need a way to do lookup in nextst *)

(* real_st_in_float_st_correct :

real_in_float r f ->


      unfold real_st_
      extensionality.

FloatToR??real_st_in_float_st st sf ->
eval_term t st nextst <= 

      (* need axiom relating real_in_float
         to *)

      (* we want to show
evaluating t with trel1 and trel2 as context
  is less than the value of pa_dest0 in trel2.

         we know
evaluating t with sf and trel2 as context is less
  than the value of pa_source0 with sf as context.

trel1 is contained in sf
trel2 is contained in "update sf setting pa_dest0 to pa_source0"
     
      induction t; simpl in *.
      unfold real_st_in_float_st in H0.

      (* need an exchange lemma relating real and float states *)
      
      


      simpl.
      unfold eval_term.
unfold real_st_in_float_st in H1.


assert ((fun v : Var => sf v) = sf). admit. (* functional extensionality *)
      Set Printing All.
      
      
      rewrite H5 in H2.
    
    real_in_float k trace ->
    

  + unfold Semantics.eval_comp.
    unfold real_st_in_float_st in H1.
    (* need H1 to relate sf to tr1 *)
    unfold real_st_in_float_st in H0.
    

    (* needs functional extensionality *)
    (fun (v : Var) => sf v) = ())

    real_in_float x y ->
    
    
    apply H2.
      

split; simpl.
- Check getBound_correct.
  inversion H.
  destruct t. simpl.
  
Print Semantics.eval_comp.



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

Coercion denowify : NowTerm >-> Term.
Coercion progr_to_tla : progr >-> Formula.


Local Open Scope string_scope.

Definition derp : progr :=
  ([PIF (FTRUE  /\
        (FloatN 1 = FloatN 1))
   PTHEN ["ab" !!= FloatN 1]])%SL.

