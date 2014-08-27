Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Ranalysis1.
Require Import String.
Require Import List.
Require Import Sumbool.
Require Import Coq.Reals.MVT.

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
| MultT : Term -> Term -> Term.
(*| DivideT : Term -> Term -> Term.*)

(* Programs containing discrete and continuous parts. *)
Inductive HybridProg :=
(* A discrete progam constructor for assignment *)
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
(*  | DivideT t1 t2 => (eval_term t1 st) / (eval_term t2 st)*)
  end.

Definition solves_diffeqs (f : R -> state)
  (diffeqs : list (Var * Term)) (r : R)
  (is_derivable : forall x, derivable (fun t => f t x)) :=
  forall x d,
      List.In (x, d) diffeqs ->
      forall z, R0 < z < r ->
        derive (fun t => f t x) (is_derivable x) z =
        eval_term d (f z).

Definition vars_unchanged (f : R -> state)
  (diffeqs : list (Var * Term)) (r : R) (s : state) :=
  forall x,
      ~(exists d, List.In (x, d) diffeqs) ->
      forall z, R0 < z < r ->
        f z x = s x.

(* Semantics of hybrid programs. Intuitively,
   Transition p st1 st2 should hold if, starting in
   state st1, the system specified by p can evolve to
   state st2. *)
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
| Continuous : forall s1 s2 diffeqs f r is_derivable, 
   (* (1) f is equal to s1 at time 0 and equal to
          s2 at some later time r *)
   (* Should it be R0 < r or R0 <= r ? *)
   R0 < r ->
   f R0 = s1 -> f r = s2 ->
   (* TODO f is continuous on [0,r] *)
   (* (2) f is a solution to diffeqs *)
   solves_diffeqs f diffeqs r is_derivable ->
   (* (3) f does not change other variables *)
   vars_unchanged f diffeqs r s1 ->
   Transition (DiffEq diffeqs) s1 s2

(* Semantics of sequencing. Nothing special here. *)
| SeqTrans : forall s1 s2 s3 p1 p2,
   Transition p1 s1 s2 ->
   Transition p2 s2 s3 ->
   Transition (Seq p1 p2) s1 s3.

(* Semantics of formulas. A formula valid with respect
   to a given state. Below, when we state correctness
   properties of programs, we will quantify over the
   state.  *)
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
Notation "-- x" := (MinusT (RealT R0) x)
                     (at level 9) : HP_scope.
Infix "*" := (MultT) : HP_scope.
(*Infix "/" := (DivideT) : HP_scope.*)
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

Delimit Scope HP_scope with HP.
Delimit Scope DL_scope with DL.

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

(* The following three functions will be used to state
   the differential induction rule (diff_ind) below.
   Essentially, an invariant inv is a differential
   invariant of a system of differential equations
   diffeqs at some state st if
     1) inv holds at st
     2) if one takes the "derivative" of inv
        and substitutes the right hand sides of diffeqs
        into this derivative to form inv', then inv'
        holds on any state st'
   The derivative of a formula and substitution of
   differential equations right hand sides is implemented
   in the following three functions. *)
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
(*  | DivideT t1 t2 =>
     (((deriv_term t1 eqs) * t2) - (t1 * (deriv_term t2 eqs)))
     / (t2 * t2)*)
  end.

(* For some formulas, differential induction does not work,
   so we use the following unprovable formula in those
   cases. *)
Definition FalseFormula := Geq (RealT R0) (RealT (INR 1)).

Lemma FalseFormulaFalse : forall st,
  ~eval_formula FalseFormula st.
Proof.
  intros. simpl. apply Rlt_not_ge.
  apply lt_0_INR with (n := S O). omega.
Qed.

(* The derivative of a formula is essentially the derivative
   of each of its terms (with some exceptions not shown
   here). *)
Fixpoint deriv_formula (f:Formula) (eqs:list (Var * Term))
  : Formula :=
  match f with
  | Geq t1 t2 => Geq (deriv_term t1 eqs) (deriv_term t2 eqs)
  | Imp f1 f2 => FalseFormula
     (*I'm not sure what the condition is in this case
       but I think the following is wrong. *)
     (*Imp (deriv_formula f1 eqs)
           (deriv_formula f2 eqs)*)
  | ForallState p f => FalseFormula
     (*I don't think differential induction works here.*)
     (*ForallState p (deriv_formula f eqs)*)
  end.

(* Now we have a bunch of messy lemmas that we'll use
   to prove the differential induction (diff_ind) rule. *)
Lemma term_is_derivable : forall (f : R -> state) (e : Term),
  (forall x, derivable (fun t => f t x)) ->
  derivable (fun t => eval_term e (f t)).
Proof.
  intros f e.
  induction e; simpl; intro is_derivable.
    - auto.
    - apply derivable_const.
    - apply derivable_plus; auto.
    - apply derivable_minus; auto.
    - apply derivable_mult; auto.
(*    - apply derivable_div; auto.*)
Qed.

Lemma get_deriv_in : forall x eqs t,
  get_deriv x eqs = Some t ->
  List.In (x, t) eqs.
Proof.
  intros x eqs t Hderiv.
  induction eqs.
    - unfold get_deriv in *. simpl in *. discriminate.
    - unfold get_deriv in *. simpl in *. destruct a.
      destruct (string_dec x v) eqn:?; simpl in *;
        intuition congruence.
Qed.

Lemma get_deriv_not_in : forall x eqs,
  get_deriv x eqs = None ->
  ~exists t, List.In (x, t) eqs.
Proof.
  intros x eqs Hderiv.
  induction eqs.
    - intro H. destruct H. auto.
    - intro H. destruct H. simpl in *.
      destruct H.
      + subst a. unfold get_deriv in *. simpl in *.
        destruct (string_dec x x); simpl in *;
        intuition discriminate.
      + unfold get_deriv in *. simpl in *. destruct a.
        destruct (string_dec x v); simpl in *.
        * discriminate.
        * intuition. eauto.
Qed.

Lemma term_deriv : forall (f : R -> state) (e : Term)
  (r : R) (diffeqs : list (Var * Term)) is_derivable s,
  solves_diffeqs f diffeqs r is_derivable ->
  vars_unchanged f diffeqs r s ->
  forall z, 
    (R0 < z < r)%R ->
    derive (fun t => eval_term e (f t))
           (term_is_derivable f e is_derivable) z =
    eval_term (deriv_term e diffeqs) (f z).
Proof.
  intros. unfold derive.
  apply (derive_pt_D_in
           (fun t : R => eval_term e (f t))
           (fun t : R => eval_term (deriv_term e diffeqs)
                                   (f t))).
  induction e; intros; simpl in *.
    - destruct (get_deriv v diffeqs) eqn:?.
      + unfold solves_diffeqs in *.
        unfold derive in *.
        specialize (H v t (get_deriv_in _ _ _ Heqo) z H1).
        apply (derive_pt_D_in
                 (fun t0 : R => f t0 v)
                 (fun t0 : R => eval_term t (f t0))) in H.
        auto.
      + apply (derive_pt_D_in _ _ _
         (term_is_derivable _ (VarT v) is_derivable z)).
        simpl. apply deriv_constant2 with (a := R0) (b := r);
               intuition. unfold vars_unchanged in *.
        specialize (H0 v (get_deriv_not_in v diffeqs Heqo)).
        transitivity (s v). apply H0. intuition.
        symmetry. apply H0. intuition.
    - apply Dconst.
    - apply Dadd; auto.
    - apply Dminus; auto.
    - apply Dmult; auto.
Qed.

(* Differential induction *)
Lemma diff_ind : forall diffeqs inv st,
  eval_formula inv st ->
  (forall st, eval_formula (deriv_formula inv diffeqs) st) ->
  eval_formula ([DiffEq diffeqs]inv) st.
Proof.
  intros diffeqs inv st Hbase Hind.
  simpl; intros st' Htrans; inversion_clear Htrans.
  generalize dependent st.
  generalize dependent st'.
  induction inv; simpl in *; intros.
    - apply Rminus_ge. apply Rge_minus in Hbase.
      cut (eval_term t st - eval_term t0 st <=
           eval_term t st' - eval_term t0 st')%R.
      + intros. apply Rle_ge. apply Rge_le in Hbase.
        apply Rle_trans with
          (r2 := (eval_term t st - eval_term t0 st)%R); auto.
      + subst st. subst st'.
        eapply (derive_increasing_interv_var
                 0 r (fun z =>
                        eval_term t (f z) -
                        eval_term t0 (f z))%R); eauto.
        * intros. specialize (Hind (f t1)).
          apply Rge_minus in Hind. apply Rge_le in Hind.
          erewrite <- term_deriv in Hind; eauto.
          erewrite <- term_deriv in Hind; eauto.
          unfold derive in Hind.
          rewrite <- derive_pt_minus in Hind.
          apply Hind.
        * split; try apply Rle_refl; apply Rlt_le; auto.
        * split; try apply Rle_refl; apply Rlt_le; auto.
    - specialize (Hind (fun _ => R0)). 
      destruct (FalseFormulaFalse st' Hind).
    - specialize (Hind (fun _ => R0)). 
      destruct (FalseFormulaFalse st' Hind).
Qed.

(* A tactic for apply all of our proof rules. *)
Ltac apply_proof_rules :=
  repeat (intros; match goal with
                    | [ |- _ ] => apply imp_intro
                    | [ |- _ ] => apply diff_ind
                  end).

Close Scope DL_scope.

(************************************************)
(* Some examples.                               *)
(************************************************)

Open Scope HP_scope.
Open Scope DL_scope.
Open Scope string_scope.

(* Example 3.14 on page 171 of Platzer's textbook. This
   example includes the following three programs and
   their corresponding differential invariants. *)
Definition quartic1 := |[ "x"' ::= `"x"^^4 ]|.

Definition inv_quartic1 := 4 * `"x" >= 1.

Theorem inv_quartic1_ok : forall st,
  eval_formula (inv_quartic1 --> [quartic1] inv_quartic1) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  field_simplify.
  (* We're essentially left with the goal
     forall x, 4 * x^4 >= 0 *)
Admitted.

Definition quartic2 := |["x"' ::= `"x"^^4 + `"x"^^2]|.

Definition inv_quartic2 := 3 * 4 *`"x" >= 1.

Theorem inv_quartic2_ok : forall st,
  eval_formula (inv_quartic2 --> [quartic2] inv_quartic2) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  field_simplify.
  (* We're essentially left with the goal
     forall x, 12(x^4 + x^2) >= 0 *)
Admitted.

Definition quad := |["x"' ::= `"x"^^2 - (4*`"x") + 6]|.

Definition inv_quad := 3*4*`"x" >= 1.

Theorem inv_quad_ok : forall st,
  eval_formula (inv_quad --> [quad] inv_quad) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  field_simplify.
  (* We're essentially left with the goal
     forall x, 12(x^2 - 4x + 6) >= 0 *)
Admitted.

Definition cubic := |["x"' ::= `"x"^^3]|.

Definition inv_cubic := 3*5*(`"x"^^2) >= 1.

Theorem inv_cubic_ok : forall st,
  eval_formula (inv_cubic --> [cubic] inv_cubic) st.
Proof.
  intro st; apply_proof_rules; auto; simpl in *; intros.
  field_simplify.
  (* We're essentially left with the goal
     forall x, 30x^4 >= 0 *)
Admitted.

(* Here's a more challenging example from section
   12 Assuming Invariants of Platzer's lecture notes
   http://symbolaris.com/course/fcps13/11-diffcut.pdf.
   We'll start with a formula that is not an invariant
   of the system to make sure our proof rules don't
   allow us to prove stuff that's wrong. Eventually,
   I'll implement something that does work. *)
Definition system :=
  |["x"' ::= `"d", "y"' ::= `"e", "d"' ::= `"e",
    "e"' ::= --`"d"]|.

Definition bad_inv p :=
  ((`"x"-1)^^2) + (`"y"-2)^^2 >= (RealT p)^^2.

Theorem bad_inv_ok : forall st p,
  eval_formula ((bad_inv p) --> [system] (bad_inv p)) st.
Proof.
  intros st p; apply_proof_rules; auto; simpl in *; intros.
  field_simplify.
  (* We're essentially left with the goal
     forall x y d e, 2(x-1)d + 2(y-2)e >= 0
     which is unprovable, as it should be. *)
Abort.
