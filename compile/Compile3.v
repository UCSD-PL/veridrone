Require Import source.

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


Axiom getBound : rbstate -> NowTerm -> (Term * Term * Formula)%type.

(* reasoning about bounds membership - including
   states being within bounds specified by other states
   (when variables are considered pointwise) *)

Axiom real_in_float : R -> Floats.float -> Prop.

(* this is a very weak condition but hopefully
   it's all that we need *)
(* "introduction" rule *)
Axiom real_in_float_correct0 :
  forall (r : R) (f : Floats.float),
    FloatToR f = r ->
    real_in_float r f.

(* "elimination" rules *)
(* say conservative things about floats relative to real #s *)
Axiom real_in_float_correct1lt :
  forall (r : R) (f f' : Floats.float),
    real_in_float r f ->
    (FloatToR f < FloatToR f')%R -> 
    (r < FloatToR f')%R.

(* these commented out ones are wrong. i think you can
   only do this for strict inequalities *)
(*
Axiom real_in_float_correct1le :
  forall (r : R) (f f' : Floats.float),
    real_in_float r f ->
    (FloatToR f <= FloatToR f')%R -> 
    (r <= FloatToR f')%R.
*)

Axiom real_in_float_correct1gt :
  forall (r : R) (f f' : Floats.float),
    real_in_float r f ->
    (FloatToR f > FloatToR f')%R -> 
    (r > FloatToR f')%R.

(*
Axiom real_in_float_correct1ge :
  forall (r : R) (f f' : Floats.float),
    real_in_float r f ->
    (FloatToR f >= FloatToR f')%R -> 
    (r >= FloatToR f')%R.
*)

Definition real_st_in_float_st (rst : Syntax.state) (fst : fstate) : Prop :=
  forall (v : Var), real_in_float (rst v) (fst v).

Definition real_st_in_bound_st (rst : Syntax.state) (rbst : rbstate) : Prop :=
  forall (v : Var),
    let (lb, ub) := rbst v in
    (lb <= rst v <= ub)%R.

(* expresses that all possible real values a float could represent
   lie in a specific bound - except lifted pointwise over states *)
Definition float_st_in_bound_st (fst : fstate) (rbst : rbstate) : Prop :=
  forall (v : Var) (rst : Syntax.state),
    real_st_in_float_st rst fst -> real_st_in_bound_st rst rbst.

CoFixpoint infStr {A : Type} (a : A) : stream A :=
  Semantics.Cons A a (infStr a).

Check eval_term.

Print stream.
(* need a predicate for "begins with a transition from s1 to s2" *)
Fixpoint stream_begins {A : Type} (astream : stream A) (alist : list A) : Prop :=
  match alist with
    | nil => True
    | a :: rest =>
      match astream with
        | Cons a' rest' => and (a = a') (stream_begins rest' rest)
      end
  end.

Axiom getBound_correct :
  forall (bst : rbstate) (nt : NowTerm) (lb ub : Term) (side : Formula),
    getBound bst nt = (lb, ub, side) ->
    forall flst rst_next tr, float_st_in_bound_st flst bst ->
                let rst := (fun v => FloatToR (flst v)) in
                stream_begins tr [rst] ->
                eval_formula side tr ->
                (eval_term lb rst rst_next <= FloatToR (eval_NowTerm nt flst) <= eval_term ub rst rst_next)%R.  

(* TODO strict or non-strict inequalities? *)
Definition convert_assn (assn : progr_assn) (st : rbstate) : Formula :=
  match assn with
    | mk_progr_assn var term =>
      let '(lb, ub, side) := getBound st term in
      Imp side
          (And (Comp lb (VarNextT var) Le)
               (Comp (VarNextT var) ub Le))
  end.

Require Import FunctionalExtensionality.

(* correctness for convert_assn *)
(*
Lemma convert_assn_correct :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update_state assn sf = sf' ->
    forall (tr : Semantics.trace)
           (sr sr' : Semantics.state),
      real_st_in_float_st sr  sf ->
      real_st_in_float_st sr' sf' ->
      stream_begins tr [sr; sr'] ->
      forall (rbst : rbstate),
        float_st_in_bound_st sf rbst ->
        eval_formula (convert_assn assn rbst) tr.
*)

(* we need float_bounds *)

(* problem this only works for the discrete part of our state *)

(* we need to bridge tla and c basically. we need to treat tla variables
   and c variables separately *)

(* choice: change theorem, or let TLA have heterogeneous states *)

(* or, add a premise to the state invariant that says that discrete
   variables "are actually floats"... do we need a toFloat axiom? *)

(* reading floats written in previous state is WEIRD...
   we need to split the state. 
   alternative: compile discrete program into continuous (in terms of states being continuous variables - reals)
   continuous transitions and discrete real-valued transitions that can be nondeterministic...
   when we compile, give semantics in terms of hybrid world*)

(* update compiler so it adds boundedness of variables 
   to TLA formula. change rbst to rbspec, of type Var * (R * R) 
   (dont make it a map) *)

(* say states are related just on discrete variables
   have user label which variables are discrete
   *)

(* fstmap is a float state, expressed as a finite map. we will need to rewrite
   these other functions to use fstmaps for float state *)

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


Lemma compile_assn_correct_new :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update sf = sf' ->
    forall (tr : trace) (sr : Syntax.state),
      real_st_subsumes_float_st sr sf ->
      stream_begins tr [sr; update_floats sr sf'] ->
      forall (rbst : rbstate),
        float_st_in_bound_st sf rbst ->
        eval_formula (compile_assn assn rbst) tr.

Lemma convert_assn_correct :
  forall (sf sf' : fstate) (assn : progr_assn),
    assn_update_state assn sf = sf' ->
    forall (tr : Syntax.trace)
           (sr : Syntax.state),
      real_st_in_float_st sr  sf ->
      stream_begins tr [sr; float_st_to_real_st sf'] -> (*TODO implement *)
      forall (rbst : rbstate),
        float_st_in_bound_st sf rbst ->
        eval_formula (convert_assn assn rbst) tr.

Print rbstate.
Proof.
intros.
destruct assn; subst; simpl.
destruct (getBound rbst pa_source0) eqn:gb.
Check gb.
destruct p.
simpl.
intro.
destruct tr as [nowst [nextst trt]].
simpl. simpl in H2.
inversion H2; clear H2. inversion H5. clear H5. clear H6.
subst.
unfold Semantics.eval_comp.
simpl.
Check getBound_correct.
eapply getBound_correct with
  (nt := pa_source0)
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

