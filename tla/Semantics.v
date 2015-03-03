Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rtrigo_def.
Require Import TLA.Syntax.
Require Import TLA.Stream.
Require Export Charge.Logics.ILogic.

(* The semantics of our restricted TLA *)

(* A TLA behavior, called a trace *)
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
   end)%R.

(* Semantics of comparison operators *)
Definition eval_comp (t1 t2:Term) (op:CompOp) (s1 s2:state) :
  Prop :=
  let (e1, e2) := (eval_term t1 s1 s2, eval_term t2 s1 s2) in
  let op := match op with
              | Gt => Rgt
              | Ge => Rge
              | Lt => Rlt
              | Le => Rle
              | Eq => eq
            end in
  op e1 e2.

(* Semantics of temporal formulas *)
Fixpoint eval_formula (F:Formula) (tr:trace) :=
  match F with
    | TRUE => True
    | FALSE => False
    | Comp t1 t2 op => eval_comp t1 t2 op (hd tr) (hd (tl tr))
    | And F1 F2 => eval_formula F1 tr /\
                   eval_formula F2 tr
    | Or F1 F2 => eval_formula F1 tr \/
                  eval_formula F2 tr
    | Imp F1 F2 => eval_formula F1 tr ->
                   eval_formula F2 tr
    | PropF P => P
    | Syntax.Exists _ F => exists x, eval_formula (F x) tr
    | Syntax.Forall _ F => forall x, eval_formula (F x) tr
    | Always F => forall n, eval_formula F (nth_suf n tr)
    | Eventually F => exists n, eval_formula F (nth_suf n tr)
    | Embed P => P (hd tr) (hd (tl tr))
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
  cbv beta iota zeta delta - [ eval_formula ];
              simpl; intros; intuition eauto.
  destruct H0. eauto.
Qed.