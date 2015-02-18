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

  (** In the state, the variable stands for the given real **)
  Variable VarRelated : state -> var -> R -> Prop.
  (** In the state, the variable is represented as the returned real **)
  Variable asReal : state -> var -> R.

  (** The program state is an abstraction of the TLA state **)
  Fixpoint models (vars : list (Syntax.Var * var)) : Syntax.state -> state -> Prop :=
    match vars with
    | nil => fun _ _ => True
    | (v,v') :: vars =>
      let P := models vars in
      fun tla_state st =>
        VarRelated st v' (tla_state v) /\ P tla_state st
    end.

  (** On the output, the program gets to write exactly the given values to the
   ** TLA state, so this function computes the new final state using [asReal]
   **)
  Fixpoint modelsOutput (vars : list (Syntax.Var * var)) (tla_st : Syntax.state) (st : state) : Prop :=
    match vars with
    | nil => True
    | (v,v') :: vars =>
      tla_st v = asReal st v' /\ modelsOutput vars tla_st st
    end.

  (** Running the given program in the current state. Only the specified
   ** variables are updated by the program when it is run.
   **)
  Definition embedStep (vars : list (Syntax.Var * var)) (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state post_state : state,
                      models vars pre init_state /\
                      eval init_state prg post_state /\
                      modelsOutput vars post post_state).

End embedding.