Require Import Syntax.
Require Import List.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Ranalysis1.

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

(* Semantics of conditionals *)
Fixpoint eval_cond (c:Cond) (st:state) : Prop :=
  match c with
  | GtC t1 t2 => eval_term t1 st > eval_term t2 st
  | EqC t1 t2 => eval_term t1 st = eval_term t2 st
  | AndC c1 c2 => eval_cond c1 st /\ eval_cond c2 st
  | OrC c1 c2 => eval_cond c1 st \/ eval_cond c2 st
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

(* Semantics of hybrid programs. Intuitively,
   Transition p st1 st2 should hold if, starting in
   state st1, the system specified by p can evolve to
   state st2. *)
Inductive Transition :
  HybridProg -> state -> state -> Prop :=
(* Semantics of no-op *)
| SkipT : forall s, Transition Skip s s

(* Semantics of assignment. Nothing special here. *)
| AssignT : forall s1 s2 x t,
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
  The system evolves for at most b time units.
*)
| ContinuousT : forall s1 s2 diffeqs f r b is_derivable, 
   (* (1) f is equal to s1 at time 0 and equal to
          s2 at some later time r *)
   (* Should it be R0 < r or R0 <= r ? *)
   R0 < r ->
   f R0 = s1 -> f r = s2 ->
   (* TODO f is continuous on [0,r] *)
   (* (2) f is a solution to diffeqs *)
   solves_diffeqs f diffeqs r is_derivable ->
   (* (3) f does not change other variables *)
   vars_unchanged f diffeqs r is_derivable ->
   (* time bound is satisfied *)
   r <= b ->
   Transition (DiffEq diffeqs b) s1 s2

(* Semantics of sequencing. Nothing special here. *)
| SeqT : forall s1 s2 s3 p1 p2,
   Transition p1 s1 s2 ->
   Transition p2 s2 s3 ->
   Transition (Seq p1 p2) s1 s3

(* Branching semantics when condition is true. *)
| BranchTrueT : forall s1 s2 c p1 p2,
   eval_cond c s1 ->
   Transition p1 s1 s2 ->
   Transition (Branch c p1 p2) s1 s2

(* Branching semantics when condition is false. *)
| BranchFalseT : forall s1 s2 c p1 p2,
   ~eval_cond c s1 ->
   Transition p2 s1 s2 ->
   Transition (Branch c p1 p2) s1 s2

(* While loop semantics when condition is true *)
| WhileTrueT : forall s1 s2 s3 c p,
   eval_cond c s1 ->
   Transition p s1 s2 ->
   Transition (While c p) s2 s3 ->
   Transition (While c p) s1 s3

(* While loop semantics when condition is false *)
| WhileFalseT : forall s c p,
   ~eval_cond c s ->
   Transition (While c p) s s
.

(* Semantics of formulas. A formula valid with respect
   to a given state. Below, when we state correctness
   properties of programs, we will quantify over the
   state.  *)
Fixpoint eval_formula (f:Formula) (st:state) : Prop :=
  match f with
  | GtF t1 t2 => eval_term t1 st > eval_term t2 st
  | EqF t1 t2 => eval_term t1 st = eval_term t2 st
  | AndF c1 c2 => eval_formula c1 st /\ eval_formula c2 st
  | OrF c1 c2 => eval_formula c1 st \/ eval_formula c2 st
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