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
Require Import compcert.flocq.Core.Fcore_defs.
Require Import compcert.flocq.Appli.Fappli_IEEE.
Require Import compcert.flocq.Appli.Fappli_IEEE_bits.

Require Import ExtLib.Programming.Extras.
Import FunNotation.

Local Close Scope HP_scope.
Delimit Scope SrcLang_scope with SL.
Local Open Scope SrcLang_scope.

(* Term, sans the next operator *)
Inductive NowTerm : Type :=
| VarNowN : Var -> NowTerm
| NatN : nat -> NowTerm
(*| RealN : Rdefinitions.R -> NowTerm*)
| FloatN : Floats.float -> NowTerm
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
(*Coercion FloatToR : Floats.float >-> R.*)

Fixpoint pow (t : NowTerm) (n : nat) :=
  match n with
    | O => FloatN 1
    | S n => MultN t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : SrcLang_scope.

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

(* Fold a list with its first element as starting accumulator
Takes function and list, as well as default element to return if list is nil *)
Definition self_foldr {A : Type} (f : A -> A -> A) (l : list A) (dflt : A) : A :=
  match l with
    | nil => dflt
    | h :: t =>
      List.fold_right f h t
  end.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Option.


(* Semantics *)
Definition fstate := list (Var * Floats.float).

Fixpoint fstate_lookup (f : fstate) (v : Var) : option Floats.float :=
  match f with
  | nil => None
  | (v',f) :: fs =>
    if v ?[ eq ] v then
      Some f
    else fstate_lookup fs v
  end.

(** This should change **)
Fixpoint fstate_set (f : fstate) (v : Var) (val : Floats.float) : fstate :=
  (v,val) :: f.

Definition lift2 {T U V : Type} (f : T -> U -> V) (a : option T) (b : option U) : option V :=
  match a , b with
  | Some a , Some b => Some (f a b)
  | _ , _ => None
  end.

Definition custom_prec := 53%Z.
Definition custom_emax:= 1024%Z.
Definition custom_float_zero := B754_zero custom_prec custom_emax true.

Section eval_expr.
  Variable st : fstate.

  (* denotation of NowTerm *)
  Fixpoint eval_NowTerm (t:NowTerm) :=
    match t with
    | VarNowN var => fstate_lookup st var
    | NatN n => Some (nat_to_float n)
    | FloatN f => Some f
    | PlusN t1 t2 =>
      lift2 (Bplus custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE)
            (eval_NowTerm t1) (eval_NowTerm t2)
    | MinusN t1 t2 =>
      lift2 (Bminus custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE)
            (eval_NowTerm t1) (eval_NowTerm t2)
    | MultN t1 t2 =>
      lift2 (Bmult custom_prec custom_emax eq_refl eq_refl Floats.Float.binop_pl mode_NE)
            (eval_NowTerm t1) (eval_NowTerm t2)
    end.

  (* denotation of comparison functions *)
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
    lift2 (Floats.Float.cmp cmp) elhs erhs.

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
Definition assn_update_state (assn : progr_assn) (st : fstate) : option fstate :=
  match eval_NowTerm st assn.(pa_source) with
  | Some val => Some (fstate_set st assn.(pa_dest) val)
  | None => None
  end.

Fixpoint assn_update_states (assns: list progr_assn) (acc : fstate) : option fstate :=
  match assns with
  | nil => Some acc
  | h :: t =>
    match assn_update_state h acc with
    | Some news => assn_update_states t news
    | _ => None
    end
  end.

(* denotation of a single program statement *)
Fixpoint eval_progr_stmt (ps : progr_stmt) (init : fstate) : option fstate :=
  match ps with
  | mk_progr_stmt conds assns =>
    match progr_cond_holds init conds with
    | Some true => assn_update_states assns init
    | Some false => Some init
    | None => None
    end
  end.

(* denotation of a source language program *)
Fixpoint eval_progr (p : progr) (init : fstate) : option fstate :=
  match p with
  | nil => Some init
  | h :: t =>
    match eval_progr_stmt h init with
    | Some news => eval_progr t news
    | None => None
    end
  end.