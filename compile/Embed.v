Require Import Coq.Reals.Reals.
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

  (** The standard evaluation relation for the language **)
  Variable eval : state -> ast -> state -> Prop.

  (** In the TLA state, the variable is represented as the returned real **)
  Variable asReal : state -> var -> option R.

  (** This states that the value in the TLA state is exactly
   ** equal to the value in the program state.
   **)
  Fixpoint models (vars : list (Syntax.Var * var))
           (tla_st : Syntax.state) (st : state) : Prop :=
    match vars with
    | nil => True
    | (v,v') :: vars =>
      Some (tla_st v) = asReal st v' /\ models vars tla_st st
    end.

  (** Running the given program in the current state. Only the specified
   ** variables are updated by the program when it is run.
   **)

  (** This version supports predicated refinement, e.g. we can compile
   **   [x = y /\ x! = 3]
   ** as an [if] statement. The problem with it is that it does not
   ** correctly capture the behavior of non-deterministic programs.
   ** I.e. it has angelic non-determinism which is not realistic.
   **
   **)
  Definition embedStep_ex (vars : list (Syntax.Var * var)) (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state post_state : state,
                      models vars pre init_state /\
                      eval init_state prg post_state /\
                      models vars post post_state).

  (** This embeds with a more demonic form of non-determinism,
   ** which is more realistic in practice. However, it does not enjoy
   ** the same expressivity as TLA because it is required to have a
   ** safe step in all instances where it can be run.
   **)
  Definition embedStep (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      exists post_state : state,
                        eval init_state prg post_state /\
                        models post_vars post post_state).

  (** This the the full (progress & preservation) embedding of programs.
   ** It says both that the program terminates and that the result
   ** has the property
   **)
  Definition embedStep_full (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      (exists post_state : state,
                          eval init_state prg post_state) /\
                      (forall post_state : state,
                          eval init_state prg post_state ->
                          models post_vars post post_state)).

  Definition embedStep (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      forall post_state : state,
                        eval init_state prg post_state ->
                        models post_vars post post_state).


End embedding.
