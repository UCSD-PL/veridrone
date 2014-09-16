Require Import Syntax.
Require Import List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Reals.RIneq.
Require Import String.

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
  end.

(* Semantics of comparison operators *)
Definition eval_comp (t1 t2:Term) (st:state) (op:CompOp) :
  Prop :=
  let (e1, e2) := (eval_term t1 st, eval_term t2 st) in
  let op := match op with
              | Gt => Rgt
              | Ge => Rge
              | Lt => Rlt
              | Le => Rle
              | Eq => eq
            end in
  op e1 e2.

(* Semantics of conditionals *)
Fixpoint eval_cond (c:Cond) (st:state) : Prop :=
  match c with
  | CompC t1 t2 op => eval_comp t1 t2 st op
  | AndC c1 c2 => eval_cond c1 st /\ eval_cond c2 st
  | OrC c1 c2 => eval_cond c1 st \/ eval_cond c2 st
  | NegC c => ~eval_cond c st
  end.

(* Expresses the property the a differentiable formula
   is a solution to a list of differential equations
   in the range 0 to r. *)
Definition solves_diffeqs (f : R -> state)
  (diffeqs : list (Var * Term)) (r : R)
  (is_derivable : forall x, derivable (fun t => f t x)) :=
  forall x d,
      List.In (x, d) diffeqs ->
      forall z, R0 <= z <= r ->
        derive (fun t => f t x) (is_derivable x) z =
        eval_term d (f z).

(* Expresses the property that f, in the range 0 to r,
   does not change any variables without differential
   equations in diffeqs. *)
Definition vars_unchanged (f : R -> state)
  (diffeqs : list (Var * Term)) (r : R)
  (is_derivable : forall x, derivable (fun t => f t x)) :=
  forall x,
      ~(exists d, List.In (x, d) diffeqs) ->
      forall z, R0 <= z <= r ->
        derive (fun t => f t x) (is_derivable x) z = R0.
(* Is this equivalent to the following? I think not. *)
(*        f z x = s x.*)

(* Prop expressing that f is a solution to diffeqs in
   [0,r]. *)
Definition is_solution (f : R -> state)
  (diffeqs : list (Var * Term)) (r : R) :=
  exists is_derivable,
    (* (2) f is a solution to diffeqs *)
   solves_diffeqs f diffeqs r is_derivable /\
   (* (3) f does not change other variables *)
   vars_unchanged f diffeqs r is_derivable.

(* Updates state s by setting x to the value of t. *)
Definition update_st (s:state) (x:Var) (t:Term) :=
  fun y => if string_dec x y
           then eval_term t s
           else s y.

(* Semantics of discrete jumps. DiscreteProg p s1 s2 b
   holds if, starting in state s1, p runs in time
   b and produces state s2. *)
Inductive DiscreteJump :
  DiscreteProg -> state -> state -> R -> Prop :=
| SkipD : forall s, DiscreteJump Skip s s R0
| Assign : forall x t b s,
   DiscreteJump (Assign x t b) s (update_st s x t) b
| CondTest : forall c b s,
   eval_cond c s -> DiscreteJump (CondTest c b) s s b.

Definition merge_fun (f1 f2 f3:R->state) b :=
  forall r, R0 <= r <= b -> f3 r = f1 r /\
  forall r, R0 <= r -> f3 (r+b) = f2 r.

(* Semantics of hybrid programs. Intuitively,
   Behavior p f b should hold if p terminates in
   time b and f describes its behavior. *)
Inductive Behavior :
  HybridProg -> (R->state) -> R -> Prop :=
(* Semantics of a discrete program running in
   parallel with a continuous one. *)
| DiscreteB : forall fcp f cp p b,
   DiscreteJump p (f R0) (f b) b ->
   (* fcp solves the system of differential eqns. *)
   is_solution fcp cp b ->
   (* f agrees with fcp in [0,b) *)
   (forall r, R0 <= r < b -> f r = fcp r) ->
   (* the state doesn't change after b *)
   (forall r, b < r -> f r = f b) ->
   Behavior (DiffEqHP2 cp p) f b

(* Semantics of continuous evolution. The system can
   transition continuously from state s1 to state s2
   according to differential equations diffeqs if
   there exists some function (f : R -> state) which
     1) is equal to s1 at time 0 and equal to s2 at
        some later time
     2) is a solution to diffeqs    
     3) only changes values of variables whose
        derivative is specified in diffeqs
  The system evolves for at most b time units.
*)
| DiffEqB : forall f diffeqs r b,
   (* Should it be R0 < r or R0 <= r ? *)
   R0 < r <= b ->
   is_solution f diffeqs r ->
   (* The state doesn't change after r *)
   (forall t, r < t -> f t = f r) ->
   Behavior (DiffEqHP1 diffeqs b) f r

(* Semantics of sequencing. Nothing special here. *)
| SeqB : forall f1 f2 f3 b1 b2 p1 p2,
   Behavior p1 f1 b1 ->
   Behavior p2 f2 b2 ->
   merge_fun f1 f2 f3 b1 ->
   Behavior (Seq p1 p2) f3 (b1 + b2)

(* Branching semantics when first branch is taken. *)
| Branch1B : forall f b p1 p2,
   Behavior p1 f b ->
   Behavior (Branch p1 p2) f b

(* Branching semantics when second branch is taken. *)
| Branch2B : forall f b p1 p2,
   Behavior p2 f b ->
   Behavior (Branch p1 p2) f b

(* Repetition semantics with 0 repetitions. *)
| Rep0 : forall f p,
   Behavior (Rep p) f R0

(* Repetition semantics with at least 1 repetition. *)
| RepN : forall f1 b1 fN bN f p,
   Behavior p f1 b1 ->
   Behavior (Rep p) fN bN ->
   merge_fun f1 fN f b1 ->
   Behavior (Rep p) f (b1 + bN).

(* Semantics of formulas. A formula valid with respect
   to a given behavior. When we state correctness
   properties of programs, we will quantify over the
   behavior.  *)
Fixpoint eval_formula (f:Formula) (beh:R->state) : Prop :=
  match f with
  | CompF t1 t2 op => eval_comp t1 t2 (beh R0) op
  | AndF f1 f2 => eval_formula f1 beh /\ eval_formula f2 beh
  | OrF f1 f2 => eval_formula f1 beh \/ eval_formula f2 beh
  | Imp f1 f2 => eval_formula f1 beh -> eval_formula f2 beh
  | Prog p => exists b, Behavior p beh b
  | Always f' => forall t, eval_formula f' (fun r => beh (r+t))
  | Eventually f' => exists t, eval_formula f' (fun r => beh (r+t))
  end.

(* Adding some notation for evaluation of formulas. *)
Notation "|- f" := (forall beh, eval_formula f beh)
                     (at level 100) : HP_scope.

Close Scope R_scope.