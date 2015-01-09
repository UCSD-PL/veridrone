open Automaton
open Datatypes
open List0
open Specif
open Streams
open Tuples
open Validator_safe

module Make = 
 functor (A:T) ->
 functor (Inter:sig 
  type 'a result =
  | Err
  | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 : ('a1 * 'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  val state_of_stack : A.initstate -> stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack * 'a1) result
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  | Progress_sr of stack * A.GramDefs.token coq_Stream
  
  val step_result_rect :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    coq_Stream -> 'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) ->
    step_result -> 'a1
  
  val step_result_rec :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    coq_Stream -> 'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) ->
    step_result -> 'a1
  
  val prod_action' :
    A.Gram.production -> A.Gram.symbol_semantic_type arrows_right
  
  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> A.GramDefs.token coq_Stream
    -> step_result result
  
  val step :
    A.initstate -> stack -> A.GramDefs.token coq_Stream -> step_result result
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  
  val parse_result_rect :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token coq_Stream -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token coq_Stream -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    A.initstate -> stack -> A.GramDefs.token coq_Stream -> nat ->
    parse_result result
  
  val parse :
    A.initstate -> A.GramDefs.token coq_Stream -> nat -> parse_result result
 end) ->
 struct 
  module Valid = Make(A)
  
  (** val state_stack_of_stack :
      A.initstate -> Inter.stack -> (A.state -> bool) list **)
  
  let state_stack_of_stack init stack0 =
    app
      (map (fun cell -> Valid.singleton_state_pred (A.Ninit (projT1 cell)))
        stack0) ((Valid.singleton_state_pred (A.Init init)) :: [])
  
  (** val symb_stack_of_stack : Inter.stack -> A.Gram.symbol list **)
  
  let symb_stack_of_stack stack0 =
    map (fun cell -> A.last_symb_of_non_init_state (projT1 cell)) stack0
  
  (** val internal_eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)
  
  let internal_eq_rew_dep x f y =
    f
  
  (** val parse_with_safe :
      A.initstate -> A.GramDefs.token coq_Stream -> nat -> Inter.parse_result **)
  
  let parse_with_safe init buffer n_steps =
    let r = Inter.parse init buffer n_steps in
    (match r with
     | Inter.Err -> assert false (* absurd case *)
     | Inter.OK p -> p)
 end

