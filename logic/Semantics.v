Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rtrigo_def.
Require Import Coq.Reals.Ranalysis1.
Require Export Logic.Syntax.
Require Import Logic.Stream.
Require Export ChargeCore.Logics.ILogic.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Ratan.


(* The semantics of our restricted Logic *)

(* A behavior, called a trace *)
Definition flow := R -> state.
Definition trace := stream state.

(* Semantics of real valued terms *)
Fixpoint eval_term (t:Term) (s1 s2:state) : R :=
  (match t with
     | VarNowT x => s1 x
     | VarNextT x => s2 x
     | NatT n => Raxioms.INR n
     | RealT r => r
     | PlusT t1 t2 =>
       (eval_term t1 s1 s2) + (eval_term t2 s1 s2)
     | MinusT t1 t2 =>
       (eval_term t1 s1 s2) - (eval_term t2 s1 s2)
     | MultT t1 t2 =>
       (eval_term t1 s1 s2) * (eval_term t2 s1 s2)
     | InvT t =>
       / (eval_term t s1 s2)
     | CosT t => cos (eval_term t s1 s2)
     | SinT t => sin (eval_term t s1 s2)
     | SqrtT t => sqrt (eval_term t s1 s2)
     | ArctanT t => atan (eval_term t s1 s2)
     | ExpT t => exp (eval_term t s1 s2)
     | MaxT t1 t2 =>
       Rbasic_fun.Rmax (eval_term t1 s1 s2)
                       (eval_term t2 s1 s2)
     | Unop f t => f (eval_term t s1 s2)
     | Binop f t1 t2 => f (eval_term t1 s1 s2)
                          (eval_term t2 s1 s2)
   end)%R.

(* Semantics of comparison operators *)
Definition eval_comp (t1 t2:Term) (op:CompOp) (s1 s2:state) :
  Prop :=
  match op with
  | Gt => Rgt
  | Ge => Rge
  | Lt => Rlt
  | Le => Rle
  | Eq => eq
  end (eval_term t1 s1 s2) (eval_term t2 s1 s2).

Definition subst_state (s : RenameMap) : state -> state :=
  fun st x => eval_term (s x) st st.

Definition subst_flow (s : RenameMap) (f : flow) : flow :=
  fun t => subst_state s (f t).

(* Semantics of temporal formulas *)
Fixpoint eval_formula (F:Formula) (tr:trace) :=
  match F with
    | TRUE => True
    | FALSE => False
    | Comp t1 t2 op =>
      eval_comp t1 t2 op (hd tr) (hd (tl tr))
    | And F1 F2 => eval_formula F1 tr /\
                   eval_formula F2 tr
    | Or F1 F2 => eval_formula F1 tr \/
                  eval_formula F2 tr
    | Imp F1 F2 => eval_formula F1 tr ->
                   eval_formula F2 tr
    | PropF P => P
    | Syntax.Exists _ F => exists x, eval_formula (F x) tr
    | Syntax.Forall _ F => forall x, eval_formula (F x) tr
    | Enabled F => exists tr', eval_formula F (Cons (hd tr) tr')
    | Always F => forall n, eval_formula F (nth_suf n tr)
    | Eventually F => exists n, eval_formula F (nth_suf n tr)
    | Embed P =>
      P (hd tr) (hd (tl tr))
    | Rename s F =>
      eval_formula F (stream_map (subst_state s) tr)
  end.

(*
Notation "|- F" := (forall tr, eval_formula F tr)
                     (at level 100) : HP_scope.
*)

(** Formulas are Logics *)
Definition tlaEntails (P Q : Formula) : Prop :=
  forall tr, eval_formula P tr -> eval_formula Q tr.

Global Instance ILogicOps_Formula : ILogicOps Formula :=
{ lentails := tlaEntails
; ltrue    := TRUE
; lfalse   := FALSE
; land     := And
; lor      := Or
; limpl    := Imp
; lforall  := Syntax.Forall
; lexists  := Syntax.Exists
}.

Global Instance ILogic_Formula : ILogic Formula.
Proof.
  constructor;
  try solve [ cbv beta iota zeta delta - [ eval_formula ];
              simpl; intros; intuition eauto ].
  { unfold lentails. simpl. unfold tlaEntails.
    constructor; intuition. }
  { cbv beta iota zeta delta - [ eval_formula ];
    simpl; intros; intuition eauto.
    destruct H0. eauto. }
Qed.

Definition term_equiv (t1 t2:Term) : Prop :=
  forall st1 st2, eval_term t1 st1 st2 =
                  eval_term t2 st1 st2.

Global Instance Reflexive_term_equiv : Reflexive term_equiv.
Proof. repeat red; reflexivity. Qed.

Global Instance Transitive_term_equiv : Transitive term_equiv.
Proof. repeat red; etransitivity. eapply H. eapply H0. Qed.

Global Instance Reflexive_pointwise_refl {T U} (R : U -> U -> Prop) (ReflR : Reflexive R) : Reflexive (pointwise_relation T R).
Proof. repeat red. reflexivity. Qed.
