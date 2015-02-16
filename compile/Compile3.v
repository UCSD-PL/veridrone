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

(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
(*| NatN : nat -> NowTerm*)
(*| RealN : Rdefinitions.R -> NowTerm*)
| FloatN : Floats.float -> NowTerm
| PlusN : NowTerm -> NowTerm -> NowTerm
| MinusN : NowTerm -> NowTerm -> NowTerm
| MultN : NowTerm -> NowTerm -> NowTerm.
(*| InvN : NowTerm -> NowTerm.*)

Require Import ExtLib.Programming.Extras.
Import FunNotation.

(* peeled from Syntax.v *)
Infix "+" := (PlusN) : SrcLang_scope.
Infix "-" := (MinusN) : SrcLang_scope.
Notation "-- x" := (MinusN (FloatN 0) x)
                     (at level 0) : SrcLang_scope.
(*Notation "/ x" := (InvN x) : SrcLang_scope.
Notation "x / y" := (MultN x (InvN y)) : SrcLang_scope.*)
Infix "*" := (MultN) : SrcLang_scope.
(*Definition NatC (n:nat) : NowTerm :=
  NatN n.
Coercion NatC : nat >-> NowTerm.*)
Definition FloatC (f:Floats.float) : NowTerm :=
  FloatN f.
Coercion FloatC : Floats.float >-> NowTerm.
Definition VarC (x:String.string) : NowTerm :=
  VarNowN x.
Coercion VarC : String.string >-> NowTerm.

(* convenient coercions between number formats *)
Definition nat_to_int (n : nat) : int :=
  Int.repr $ Z.of_nat n.

Definition nat_to_float (n : nat) : Floats.float :=
  Floats.Float.of_int $ nat_to_int n.

Definition FloatToR : Floats.float -> R := B2R 53 1024.

Coercion nat_to_int : nat >-> int.
Coercion nat_to_float : nat >-> Floats.float.
Coercion Pos.of_nat : nat >-> positive.
Coercion FloatToR : Floats.float >-> R.

Fixpoint pow (t : NowTerm) (n : nat) :=
  match n with
  | O => FloatN 1
  | S n => MultN t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : SrcLang_scope.

(* we probably need to define more convenience methods/notations
   for this representation *)
Fixpoint denowify (nt : NowTerm) : Term :=
  match nt with
    | VarNowN v => VarNowT v
    (*| NatN n => NatT n*)
    | FloatN f => RealT f
    (*| InvN t => InvT (denowify t)*)
    | PlusN t1 t2 => PlusT (denowify t1) (denowify t2)
    | MinusN t1 t2 => MinusT (denowify t1) (denowify t2)
    | MultN t1 t2 => MultT (denowify t1) (denowify t2)
  end.

(* Formula, sans the things we don't need to worry about
   compiling, and without and and or *)
Inductive FlatFormula :=
| FTRUE : FlatFormula
| FFALSE : FlatFormula
| FComp : NowTerm -> NowTerm -> CompOp -> FlatFormula
| FAnd : FlatFormula -> FlatFormula -> FlatFormula
| FOr : FlatFormula -> FlatFormula -> FlatFormula.

(* Comparisons *)
Notation "t1 > t2" := (FComp t1 t2 Gt) : SrcLang_scope.
Notation "t1 >= t2" := (FComp t1 t2 Ge) : SrcLang_scope.
Notation "t1 < t2" := (FComp t1 t2 Lt) : SrcLang_scope.
Notation "t1 <= t2" := (FComp t1 t2 Le) : SrcLang_scope.
Notation "t1 = t2" := (FComp t1 t2 Eq) : SrcLang_scope.
Notation "x <= y <= z" :=
  (And (FComp x y Le) (FComp y z Le)) : SrcLang_scope.

(* Propositional Logic *)
Infix "/\" := (FAnd) : SrcLang_scope.
Infix "\/" := (FOr) : SrcLang_scope.

(* Convert a formula to a flat one *)
(*Definition flatten_formula (tla : Formula) : option FlatFormula :=
  match tla with
    | TRUE => Some FTRUE
    | FALSE => Some FFALSE
    | Comp a b c => Some (FComp a b c)
    | _ => None
  end.*)

Fixpoint deflatten_formula (ff : FlatFormula) : Formula :=
  match ff with
    | FTRUE => TRUE
    | FFALSE => FALSE
    | FComp a b c => Comp (denowify a) (denowify b) c
    | FAnd ff1 ff2 => And (deflatten_formula ff1)
                          (deflatten_formula ff2)
    | FOr ff1 ff2 => Or (deflatten_formula ff1)
                        (deflatten_formula ff2)
  end.

(* Captures the structure we want each term in our IR to have
   Basically, a list of simultaneous assignments, and a
   list of conditions guarding (all of) those assigments.
   Our program will be a list of these statements. *)

Record progr_assn : Set :=
  mk_progr_assn {
      pa_dest : Var;
      pa_source : NowTerm
    }.

(* for now we omit "unknown" case for simplicity *)
Record progr_stmt : Set :=
  mk_progr_stmt {
      ps_conds : FlatFormula;
      ps_assns : list progr_assn
    }.

Notation "a !!= b" := (mk_progr_assn a b) (at level 40) : SrcLang_scope.

Notation "'PIF' cs 'PTHEN' yas" :=
  (mk_progr_stmt cs yas) (at level 60) : SrcLang_scope.

(*
Notation "'PIF' cs 'PTHEN' yas 'PUNKNOWN' unas" := 
  (mk_progr_stmt cs yas unas) (at level 59).
*)

Definition progr : Set := list progr_stmt.

(* definition of trace *)
Require Import compcert.common.Events.
Require Import compcert.cfrontend.ClightBigstep.

(* Fold a list with its first element as starting accumulator
   Takes function and list, as well as default element to return if list is nil *)
Definition self_foldr {A : Type} (f : A -> A -> A) (l : list A) (dflt : A) : A :=
  match l with
    | nil => dflt
    | h :: t =>
      List.fold_right f h t
  end.

(* state giving bounds on variables *)
Definition rbstate := Var -> (R * R)%type.

(* standin for Vignesh's bound function *)
(*Axiom getBound (init : rbstate) (ff : FlatFormula) : (Term * Term * Formula).*)
(* result is (lower bound, upper bound, side conditions)
   side conditions are things like no overflow, etc. *)

(* Semantics *)
Definition fstate := Var -> Floats.float.
Print FlatFormula.
Print NowTerm.
Print CompOp.

SearchAbout (Floats.float -> Floats.float -> _).
Print comparison.
Check Floats.Float.cmp.

(* denotation of NowTerm *)
Fixpoint eval_NowTerm (nt : NowTerm) (st : fstate) : Floats.float :=
  match nt with
    | VarNowN v  => st v
    | FloatN f   => f
    | PlusN l r  => Floats.Float.add (eval_NowTerm l st) (eval_NowTerm r st)
    | MinusN l r => Floats.Float.sub (eval_NowTerm l st) (eval_NowTerm r st)
    | MultN l r  => Floats.Float.mul (eval_NowTerm l st) (eval_NowTerm r st)
  end.

(* denotation of comparison functions *)
Definition eval_comp (op : CompOp) (lhs rhs : NowTerm) (st : fstate) : bool :=
  let elhs := eval_NowTerm lhs st in
  let erhs := eval_NowTerm rhs st in
  let cmp := match op with
               | Gt => Cgt
               | Ge => Cge
               | Lt => Clt
               | Le => Cle
               | Eq => Ceq
             end in
  Floats.Float.cmp cmp elhs erhs.

(* denotation of conditionals *)
Fixpoint progr_cond_holds (conds : FlatFormula) (st : fstate) : bool :=
  match conds with
    | FTRUE => true
    | FFALSE => false
    | FComp lhs rhs op => eval_comp op lhs rhs st
    | FAnd p1 p2 => andb (progr_cond_holds p1 st) (progr_cond_holds p2 st)
    | FOr  p1 p2 => orb  (progr_cond_holds p1 st) (progr_cond_holds p2 st)
  end.

SearchAbout (String.string -> String.string -> bool).
(* String.string_dec *)

(* update state as per an assignment *)
(* TODO rename these to eval_something *)
Definition assn_update_state (assn : progr_assn) (st : fstate) : fstate :=
  fun v =>
    if String.string_dec v $ pa_dest assn
    then eval_NowTerm (pa_source assn) st
    else st v.

Fixpoint assn_update_states (assns: list progr_assn) (init : fstate) : fstate :=
  match assns with
      | nil => init
      | h :: t =>
        let news := assn_update_state h init in
        assn_update_states t news
  end.

(* denotation of a single program statement *)
Fixpoint eval_progr_stmt (ps : progr_stmt) (init : fstate) : fstate :=
  match ps with
    | mk_progr_stmt conds assns =>
      if progr_cond_holds conds init
      then assn_update_states assns init
      else init
  end.  

Fixpoint eval_progr (p : progr) (init : fstate) : fstate :=
  match p with
    | nil => init
    | h :: t =>
      let news := eval_progr_stmt h init in
      eval_progr t news
  end.


Axiom getBound : rbstate -> NowTerm -> (Term * Term * Formula)%type.

(* reasoning about bounds membership - including
   states being within bounds specified by other states
   (when variables are considered pointwise) *)

Axiom real_in_float : R -> Floats.float -> Prop.

(*Axiom real_in_float_correct :
  forall (r : R) (f : Floats.float),
    real_in_float r f <-> 
    FloatToR f = r.*)

Definition real_st_in_float_st (rst : Semantics.state) (fst : fstate) : Prop :=
  forall (v : Var), real_in_float (rst v) (fst v).

Definition real_st_in_bound_st (rst : Semantics.state) (rbst : rbstate) : Prop :=
  forall (v : Var),
    let (lb, ub) := rbst v in
    (lb <= rst v <= ub)%R.

(* expresses that all possible real values a float could represent
   lie in a specific bound - except lifted pointwise over states *)
Definition float_st_in_bound_st (fst : fstate) (rbst : rbstate) : Prop :=
  forall (v : Var) (rst : Semantics.state),
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

(* correctness for convert_assn *)
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
Proof.
intros.
destruct assn; subst; simpl.
destruct (getBound rbst pa_source0) eqn:gb.
Check gb.
destruct p.
simpl.
intro.
destruct tr as [now [next trt]].

simpl. simpl in H2.
inversion H2; clear H2. inversion H5. clear H5. clear H6.
subst.
unfold Semantics.eval_comp.
simpl.
Check getBound_correct.
eapply getBound_correct with
  (bst := rbst) (nt := pa_source0) (lb := t) (ub := t0)
  (flst := sf) (rst_next := next)
  in gb.
  (* first, prove our conclusion from conclusion of
     getBound_correct *)
  - inversion gb. clear gb.
    split.
    +

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

