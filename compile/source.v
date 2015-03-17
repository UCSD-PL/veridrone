Require Import compcert.cfrontend.Clight.
Require Import Coq.micromega.Psatz.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Integers.
Require Import Coq.Reals.Rdefinitions.
Require Import List.
Import ListNotations.
Require Import TLA.Syntax.
Require Import TLA.Semantics.
Require Import TLA.Lib.
Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.

Require Import ExtLib.Programming.Extras.
Import FunNotation.

Local Close Scope HP_scope.
Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.


Variable prec:Z.
Variable emax:Z.
Variable emin:Z.
Hypothesis precGe1: (prec >= 1)%Z.
Hypothesis precLtEmax : (prec < emax)%Z.
Hypothesis nan : binary_float prec emax -> binary_float prec emax -> bool * nan_pl prec.
Locate FLT_exp.
Hypothesis precThm : forall k : Z,
    (emin < k)%Z ->
    (prec <=
     k - Fcore_FLT.FLT_exp (3 - emax - prec) prec k)%Z.
Definition custom_prec := prec.
Definition custom_emax:= emax.
Definition custom_float_zero := B754_zero custom_prec custom_emax false.
Definition custom_emin := emin.
Definition float := binary_float custom_prec custom_emax.
Lemma custom_precGe1: (custom_prec >= 1)%Z.
unfold custom_prec.
apply precGe1.
Qed.
Print Floats.float.
Print binary64.
Print binary_float.

(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
| NatN : nat -> NowTerm
(*| RealN : Rdefinitions.R -> NowTerm*)
| FloatN : float -> NowTerm
| PlusN : NowTerm -> NowTerm -> NowTerm
| MinusN : NowTerm -> NowTerm -> NowTerm
| MultN : NowTerm -> NowTerm -> NowTerm.
(*| InvN : NowTerm -> NowTerm.*)

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
Definition FloatC (f:float) : NowTerm :=
FloatN f.
Definition VarC (x:String.string) : NowTerm :=
VarNowN x.
Coercion VarC : String.string >-> NowTerm.
(* convenient coercions between number formats *)
Definition nat_to_int (n : nat) : int :=
Int.repr $ Z.of_nat n.

Lemma custom_precGt0 : Fcore_FLX.Prec_gt_0 custom_prec.
unfold Fcore_FLX.Prec_gt_0.
unfold custom_prec.
pose proof precGe1. 
lia.
Qed.

Lemma custom_precLtEmax : (custom_prec < custom_emax)%Z.
unfold custom_emax, custom_prec.
apply precLtEmax.
Qed.

Print nan.

Definition custom_nan:float -> float -> bool * nan_pl custom_prec := nan.
 
Definition nat_to_float (n : nat) : float :=
Fappli_IEEE_extra.BofZ custom_prec custom_emax custom_precGt0 custom_precLtEmax (Z.of_nat n).

Definition FloatToR : (float) -> R := B2R custom_prec custom_emax.
Coercion nat_to_int : nat >-> int.

Coercion Pos.of_nat : nat >-> positive.
(*Coercion FloatToR : Floats.float >-> R.*)

Print binary_float.

(* inject  *)
Fixpoint denowify (nt : NowTerm) : Term :=
  match nt with
    | VarNowN v => VarNowT v
    | NatN n => NatT n
    | FloatN f => RealT $ FloatToR f
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

(* inject FlatFormula into Formula *)
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

Inductive SrcProg : Set :=
| SAssn : Var -> NowTerm -> SrcProg
| SSkip : SrcProg
| SSeq  : SrcProg -> SrcProg -> SrcProg
| SITE  : FlatFormula -> SrcProg -> SrcProg -> SrcProg
.

(* These are the old implementation of the source language.
   They have since been replaced *)
(*
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
*)

Notation "a !!= b" := (SAssn a b) (at level 59) : SrcLang_scope.
Notation "'SIF' c 'STHEN' s1 'SELSE' s2" :=
(SITE c s1 s2) (at level 60) : SrcLang_scope.
Notation "'SIF' c 'STHEN' s" :=
(SITE c s SSkip) (at level 61) : SrcLang_scope.

Notation "s1 ;; s2" :=
(SSeq s1 s2) (at level 58) : SrcLang_scope.

(*
Check (SIF FTRUE STHEN SSkip SELSE SSkip ;; SSkip).
*)

(*
Notation "'PIF' cs 'PTHEN' yas 'PUNKNOWN' unas" :=
(mk_progr_stmt cs yas unas) (at level 59).
*)
Local Open Scope string_scope.
Definition testProg :=
  ("a" !!= "b" + (NatN 3))%SL.

Definition testProg2 :=
  (SIF FTRUE STHEN "a" !!= "b").

(* Fold a list with its first element as starting accumulator
Takes function and list, as well as default element to return if list is nil *)
Definition self_foldr {A : Type} (f : A -> A -> A) (l : list A) (dflt : A) : A :=
  match l with
    | List.nil => dflt
    | h :: t =>
      List.fold_right f h t
  end.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Option.


(* Semantics *)
Definition fstate := list (Var * (float)).

Fixpoint fstate_lookup (f : fstate) (v : Var) : option (float) :=
  match f with
  | List.nil          => None
  | (v',b) :: fs =>
    if v ?[ eq ] v' then
      Some b
    else fstate_lookup fs v
  end.

Fixpoint fstate_set (f : fstate) (v : Var) (val : float) : fstate :=
  match f with
    | List.nil           => (v, val) :: List.nil
    | (v', b) :: fs =>
      if v ?[ eq ] v' then
        (v, val) :: fs
      else
        (v', b) :: fstate_set fs v val
  end.

Definition lift2 {T U V : Type} (f : T -> U -> V) (a : option T) (b : option U) : option V :=
  match a , b with
  | Some a , Some b => Some (f a b)
  | _ , _ => None
  end.


Section eval_expr.
  Variable st : fstate.

  (* denotation of NowTerm *)
  Print Floats.Float.binop_pl.
  
  Print Floats.Float.transform_quiet_pl.

  Print Archi.default_pl_64.

Definition try := (fun pl : positive =>
   ((PreOmega.Z_of_nat' (S (Fcore_digits.digits2_Pnat pl)) <? 53)%Z = true)%type).

Print Bplus.

Fixpoint eval_NowTerm (t:NowTerm) :=
  match t with
  | VarNowN var => fstate_lookup st var
  | NatN n => Some (nat_to_float n)
  | FloatN f => Some f
  | PlusN t1 t2 =>
    lift2 (Bplus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE)
          (eval_NowTerm t1) (eval_NowTerm t2)
  | MinusN t1 t2 =>
    lift2 (Bminus custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE)
          (eval_NowTerm t1) (eval_NowTerm t2)
  | MultN t1 t2 =>
    lift2 (Bmult custom_prec custom_emax custom_precGt0 custom_precLtEmax custom_nan mode_NE)
          (eval_NowTerm t1) (eval_NowTerm t2)
  end.

  (* denotation of comparison functions *)



Definition custom_cmp (c : comparison) (f1 : float) (f2 : float) := Floats.cmp_of_comparison c (Fappli_IEEE_extra.Bcompare custom_prec custom_emax f1 f2).

  Definition eval_comp (op : CompOp) (lhs rhs : NowTerm) : option bool :=
    let elhs := eval_NowTerm lhs in
    let erhs := eval_NowTerm rhs in
    let cmp := match op with
               | Gt => Cgt
               | Ge => Cge
               | Lt => Clt
               | Le => Cle
               | Eq => Ceq
               end in
    lift2 (custom_cmp cmp) elhs erhs.

  (* denotation of conditionals *)
  Fixpoint progr_cond_holds (conds : FlatFormula) : option bool :=
    match conds with
    | FTRUE => Some true
    | FFALSE => Some false
    | FComp lhs rhs op => eval_comp op lhs rhs
    | FAnd p1 p2 => lift2 andb (progr_cond_holds p1) (progr_cond_holds p2)
    | FOr p1 p2 => lift2 orb (progr_cond_holds p1) (progr_cond_holds p2)
    end.
End eval_expr.



(* String.string_dec *)
(* update state as per an assignment *)
(* TODO rename these to eval_something *)
Definition assn_update_state (v : Var) (nt : NowTerm) (st : fstate) : option fstate :=
  match eval_NowTerm st nt with
  | Some val => Some (fstate_set st v val)
  | None => None
  end.

(*
Fixpoint assns_update_state (assns: list progr_assn) (acc : fstate) : option fstate :=
  match assns with
  | List.nil => Some acc
  | h :: t =>
    match assn_update_state h acc with
    | Some news => assns_update_state t news
    | _ => None
    end
  end.
*)

Print SrcProg.
SearchAbout FlatFormula.

Fixpoint eval_SrcProg (sp : SrcProg) (init : fstate) : option fstate :=
  match sp with
    | SAssn v nt   => assn_update_state v nt init
    | SSkip        => Some init
    | SSeq p1 p2   => 
      match eval_SrcProg p1 init with
        | Some nxt => eval_SrcProg p2 nxt
        | None     => None
      end
    | SITE c p1 p2 => 
      match progr_cond_holds init c with
        | Some true  => eval_SrcProg p1 init
        | Some false => eval_SrcProg p2 init
        | None       => None
      end
  end.

(* Previous denotation functions for source language *)

(*
(* denotation of a single program statement *)
Fixpoint eval_progr_stmt (ps : progr_stmt) (init : fstate) : option fstate :=
  match ps with
  | mk_progr_stmt conds assns =>
    match progr_cond_holds init conds with
    | Some true => assns_update_state assns init
    | Some false => Some init
    | None => None
    end
  end.

(* denotation of a source language program *)
Fixpoint eval_progr (p : progr) (init : fstate) : option fstate :=
  match p with
  | List.nil => Some init
  | h :: t =>
    match eval_progr_stmt h init with
    | Some news => eval_progr t news
    | None => None
    end
  end.
*)
