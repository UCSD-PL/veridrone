Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Ranalysis1.
Require Import String.
Require Import List.
Require Import Sumbool.

(************************************************)
(* The syntax of differential dynamic logic.    *)
(************************************************)
Definition Var := string.

(* Real-valued terms built using variables, constants
   and arithmetic. *)
Inductive Term :=
| VarT : Var -> Term
| RealT : R -> Term
| PlusT : Term -> Term -> Term
| MinusT : Term -> Term -> Term
| MultT : Term -> Term -> Term
| DivideT : Term -> Term -> Term.

(* Programs containing discrete and continuous parts. *)
Inductive HybridProg :=
(* A discrete progam constructor *)
| Assign : Var -> Term -> HybridProg
(* A continuous program constructor that takes a list
   of differential equations. Each differential equation
   is a pair of a variable and a real valued term. For
   example, if variables are strings, then the system
   of differential equations

    x' = 4
    y' = x

   would be represented as

    DiffEq [ ("x", RealT 4); ("y", VarT "x") ]
 *)
| DiffEq : list (Var * Term) -> HybridProg
(* Sequencing programs *)
| Seq : HybridProg -> HybridProg -> HybridProg.

(* Formulas expressing correctness properties of hybrid
   programs. *)
Inductive Formula :=
| Geq : Term -> Term -> Formula
| Imp : Formula -> Formula -> Formula
| ForallState : HybridProg -> Formula -> Formula.

Definition state := Var -> R.

(************************************************)
(* The semantics of differential dynamic logic. *)
(************************************************)
Open Scope R_scope.

(* Semantics of real valued terms *)
Fixpoint eval_term (t:Term) (st:state) : R :=
  match t with
  | VarT x => st x
  | RealT r => r
  | PlusT t1 t2 => (eval_term t1 st) + (eval_term t2 st)
  | MinusT t1 t2 => (eval_term t1 st) - (eval_term t2 st)
  | MultT t1 t2 => (eval_term t1 st) * (eval_term t2 st)
  | DivideT t1 t2 => (eval_term t1 st) / (eval_term t2 st)
  end.

(* Semantics of hybrid programs. *)
Inductive Transition :
  HybridProg -> state -> state -> Prop :=

(* Semantics of assignment. Nothing special here. *)
| Discrete : forall s1 s2 x t,
   (* variable x is assigned to properly *)
   s2 x = eval_term t s1 ->
   (* all other variables stay the same *)
   (forall y, y <> x -> s1 y = s2 y) ->
   Transition (Assign x t) s1 s2

(* Semantics of continuous evolution. The system can
   transition continuously from state s1 to state s2
   according to differential equations diffeqs if
   there exists some function (f : R -> state) which
     1) is equal to s1 at time 0 and equal to s2 at
        some later time
     2) is a solution to diffeqs    
     3) only changes values of variables whose
        derivative is specified in diffeqs
*)
| Continuous : forall s1 s2 diffeqs f r,
   (* (1) f is equal to s1 at time 0 and equal to
          s2 at some later time r *)
   f R0 = s1 -> f r = s2 ->
   (* TODO f is continuous on [0,r] *)
   (* (2) f is a solution to diffeqs *)
   (forall x d pr,
      In (x, d) diffeqs ->
      forall z, R0 < z < r ->
        derive (fun t => f t x) pr z =
        eval_term d (f z)) ->
   (* (3) f does not change other variables *)
   (forall x d,
      ~In (x, d) diffeqs ->
      forall z, R0 < z < r ->
        f z x = s1 x) ->
   Transition (DiffEq diffeqs) s1 s2

(* Semantics of sequencing. Nothing special here. *)
| SeqTrans : forall s1 s2 s3 p1 p2,
   Transition p1 s1 s2 ->
   Transition p2 s2 s3 ->
   Transition (Seq p1 p2) s1 s3.

(* Semantics of formulas. *)
Fixpoint eval_formula (f:Formula) (st:state) : Prop :=
  match f with
  (* Semantics of comparison. Nothing special here. *)
  | Geq t1 t2   => eval_term t1 st >= eval_term t2 st
  (* Semantics of implication. Nothing special here. *)
  | Imp f1 f2 => eval_formula f1 st -> eval_formula f2 st
  (* This is essentially the temporal operator always,
     denoted [] (and sometimes called globally). It means
     that for all states that the program can transition
     to from state st, the given formula holds. *)
  | ForallState p f' => forall st',
     Transition p st st' ->
     eval_formula f' st'
  end.

Close Scope R_scope.

(************************************************)
(* Some notation for the logic.                 *)
(************************************************)
(*Term notation *)
Notation " ` a " := (VarT a) (at level 10) : HP_scope.
Notation "0" := (RealT (INR 0)) (at level 10) : HP_scope.
Notation "1" := (RealT (INR 1)) (at level 10) : HP_scope.
Notation "2" := (RealT (INR 2)) (at level 10) : HP_scope.
Notation "3" := (RealT (INR 3)) (at level 10) : HP_scope.
Notation "4" := (RealT (INR 4)) (at level 10) : HP_scope.
Notation "5" := (RealT (INR 5)) (at level 10) : HP_scope.
Notation "6" := (RealT (INR 6)) (at level 10) : HP_scope.
Infix "+" := (PlusT) : HP_scope.
Infix "-" := (MinusT) : HP_scope.
Infix "*" := (MultT) : HP_scope.
Infix "/" := (DivideT) : HP_scope.
Fixpoint pow (t : Term) (n : nat) :=
  match n with
  | O => RealT 1
  | S n => MultT t (pow t n)
  end.
Notation "t ^^ n" := (pow t n) (at level 10) : HP_scope.

(* HybridProg notation *)
Notation "x ::= t" := (Assign x t)
                        (at level 10) : HP_scope.
Notation "x ' ::= t" := (x, t) (at level 10) : HP_scope.
Notation "|[ x1 , .. , xn ]|" :=
  (DiffEq (cons x1 .. (cons xn nil) .. ))
    (at level 10) : HP_scope.
Notation "p1 ; p2" := (Seq p1 p2)
                        (at level 11) : HP_scope.

(* Formula notation *)
Infix ">=" := (Geq) : DL_scope.
Notation "f1 --> f2" := (Imp f1 f2)
                          (at level 11) : DL_scope.
Notation "[ p ] f" := (ForallState p f)
                        (at level 10) : DL_scope.

(************************************************)
(* Some proof rules.                            *)
(************************************************)
Open Scope HP_scope.
Open Scope DL_scope.

(* Implication introduction *)
Lemma imp_intro : forall f f' st,
  (eval_formula f st ->
   eval_formula f' st) ->
  eval_formula (f --> f') st.
Proof. auto. Qed.

(* Takes a var x and list of differential equations
   and returns Some t if (x' := t) is in the list of
   differential equations. Returns None otherwise. *)
Definition get_deriv (x:Var) (eqs:list (Var * Term))
  : option Term :=
  option_map (@snd Var Term)
    (find (fun p : Var * Term => let (y, t) := p in
          proj1_sig (bool_of_sumbool (string_dec x y))) eqs).

(* Takes the derivative of a term and substitutes in
   the right hand side of differential equations. If
   a variable has no corresponding differential equation
   then 0 is substituted. This is because variables
   without specified derivatives have a derivative of 0. *)
Fixpoint deriv_term (t:Term) (eqs:list (Var * Term))
  : Term :=
  match t with
  | VarT x =>
    match get_deriv x eqs with
      | Some t => t
      | None   => RealT R0
    end
  | RealT r => RealT R0
  | PlusT t1 t2 =>
     (deriv_term t1 eqs) + (deriv_term t2 eqs)
  | MinusT t1 t2 =>
     (deriv_term t1 eqs) - (deriv_term t2 eqs)
  | MultT t1 t2 =>
     ((deriv_term t1 eqs) * t2) + (t1 * (deriv_term t2 eqs))
  | DivideT t1 t2 =>
     (((deriv_term t1 eqs) * t2) - (t1 * (deriv_term t2 eqs)))
     / (t2 * t2)
  end.

(* The derivative of a formula is essentially the derivative
   of each of its terms (with some exceptions not shown
   here). *)
Fixpoint deriv_formula (f:Formula) (eqs:list (Var * Term))
  : Formula :=
  match f with
  | Geq t1 t2 => Geq (deriv_term t1 eqs) (deriv_term t2 eqs)
  | Imp f1 f2 => Imp (deriv_formula f1 eqs)
                     (deriv_formula f2 eqs)
  | ForallState p f => ForallState p (deriv_formula f eqs)
  end.

(* Differential induction *)
Lemma diff_ind : forall diffeqs inv st,
  eval_formula inv st ->
  eval_formula (deriv_formula inv diffeqs) st ->
  eval_formula ([DiffEq diffeqs]inv) st.
Admitted.

Close Scope DL_scope.

(************************************************)
(* Some examples.                               *)
(************************************************)

Open Scope HP_scope.
Open Scope DL_scope.
Open Scope string_scope.

(* Example 3.14 on page 171 of Platzer's textbook. *)
Definition quartic1 := |["x"' ::= `"x"^^4]|.

Definition inv_quartic1 := `"x" >= 1/4.

Theorem inv_quartic1_ok : forall st,
  eval_formula (inv_quartic1 --> [quartic1] inv_quartic1) st.
Proof.
  intro st.
  Arguments string_dec !s1 !s2.
  repeat (intros; match goal with
                    | [ |- _ ] => apply imp_intro
                    | [ |- _ ] => apply diff_ind
                  end); auto; simpl in *; intros.
field_simplify.
 (* We're essentially left with the goal
    forall x, x^4 >= 0 *)
Admitted.

Definition quartic2 := |["x"' ::= `"x"^^4 + `"x"^^2]|.

Definition inv_quartic2 := 3*`"x" >= 1/4.

Theorem inv_quartic2_ok : forall st,
  eval_formula (inv_quartic2 --> [quartic2] inv_quartic2) st.
Proof.
  intro st.
  Arguments string_dec !s1 !s2.
  repeat (intros; match goal with
                    | [ |- _ ] => apply imp_intro
                    | [ |- _ ] => apply diff_ind
                  end); auto; simpl in *; intros.
field_simplify.
(* We're essentially left with the goal
   forall x, 3(x^4 + x^2) >= 0 *)
Admitted.

Definition quartic3 := |["x"' ::= `"x"^^2 - (4*`"x") + 6]|.

Definition inv_quartic3 := 3*`"x" >= 1/4.

Theorem inv_quartic3_ok : forall st,
  eval_formula (inv_quartic3 --> [quartic3] inv_quartic3) st.
Proof.
  intro st.
  Arguments string_dec !s1 !s2.
  repeat (intros; match goal with
                    | [ |- _ ] => apply imp_intro
                    | [ |- _ ] => apply diff_ind
                  end); auto; simpl in *; intros.
field_simplify.
(* We're essentially left with the goal
   forall x, 3(x^2 - 4x + 6) >= 0 *)
Admitted.
