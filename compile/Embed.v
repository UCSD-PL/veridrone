Require Import Reals.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import TLA.Syntax.
Require Import TLA.Semantics.

(**
 ** This embeds an language into TLA using the state and the
 ** evaluation relation.
 **)
Section embedding.

  Variable var : Type.   (** Programming language variables **)
  Variable ast : Type.   (** Programs **)
  Variable state : Type. (** Programming language states **)

  (** The standard evaluation relation **)
  Variable eval : state -> ast -> state -> Prop.

  (** In the state, the variable is represented as the returned real **)
  Variable asReal : state -> var -> R.

  (** This states that the value in the TLA state is exactly
   ** equal to the value in the program state.
   **)
  Fixpoint models (vars : list (Syntax.Var * var))
           (tla_st : Syntax.state) (st : state) : Prop :=
    match vars with
    | nil => True
    | (v,v') :: vars =>
      tla_st v = asReal st v' /\ models vars tla_st st
    end.

  (** Running the given program in the current state. Only the specified
   ** variables are updated by the program when it is run.
   **)
  Definition embedStep (vars : list (Syntax.Var * var)) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state post_state : state,
                      models vars pre init_state /\
                      eval init_state prg post_state /\
                      models vars post post_state).

End embedding.