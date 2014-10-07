Require Import TLA.Syntax.
Require Import Coq.Reals.Rdefinitions.

CoInductive stream (A:Type) :=
| Cons : A -> stream A -> stream A.

Definition hd {A} (s:stream A) : A :=
  match s with
    | Cons a _ => a
  end.

Definition tl {A} (s:stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.

Fixpoint nth_suf {A} (n:nat) (s:stream A) : stream A :=
  match n with
    | O => s
    | S n => nth_suf n (tl s)
  end.

(* All variables are real-valued. *)
Definition state := Var -> R.

Definition trace := stream state.

(* Semantics of real valued terms *)
Fixpoint eval_term (t:Term) (st:state) : R :=
  (match t with
     | VarT x => st x
     | RealT r => r
     | PlusT t1 t2 => (eval_term t1 st) + (eval_term t2 st)
     | MinusT t1 t2 => (eval_term t1 st) - (eval_term t2 st)
     | MultT t1 t2 => (eval_term t1 st) * (eval_term t2 st)
   end)%R.

Definition eval_aterm (t:ActionTerm) (tr:trace) : R :=
  match t with
    | TermNow t => eval_term t (hd tr)
    | TermNext t => eval_term t (hd (tl tr))
  end.

(* Semantics of comparison operators *)
Definition eval_comp (t1 t2:ActionTerm) (op:CompOp) (tr:trace) :
  Prop :=
  let (e1, e2) := (eval_aterm t1 tr, eval_aterm t2 tr) in
  let op := match op with
              | Gt => Rgt
              | Ge => Rge
              | Lt => Rlt
              | Le => Rle
              | Eq => eq
            end in
  op e1 e2.

Fixpoint eval_formula (F:Formula) (tr:trace) :=
  match F with
    | TRUE => True
    | FALSE => False
    | Comp t1 t2 op => eval_comp t1 t2 op tr
    | And F1 F2 => eval_formula F1 tr /\
                   eval_formula F2 tr
    | Or F1 F2 => eval_formula F1 tr \/
                  eval_formula F2 tr
    | Imp F1 F2 => eval_formula F1 tr ->
                   eval_formula F2 tr
    | PropF P => P
    | Exists _ F => exists x, eval_formula (F x) tr
    | Always F => forall n, eval_formula F (nth_suf n tr)
    | Eventually F => exists n, eval_formula F (nth_suf n tr)
  end.

Notation "|- F" := (forall tr, eval_formula F tr)
                     (at level 100) : HP_scope.