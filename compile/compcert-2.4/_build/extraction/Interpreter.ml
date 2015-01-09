open Alphabet
open Automaton
open Datatypes
open Specif
open Streams
open Tuples

module Make = 
 functor (A:T) ->
 struct 
  type 'a result =
  | Err
  | OK of 'a
  
  (** val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2 **)
  
  let result_rect f f0 = function
  | Err -> f
  | OK x -> f0 x
  
  (** val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2 **)
  
  let result_rec f f0 = function
  | Err -> f
  | OK x -> f0 x
  
  (** val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result **)
  
  let bind f g =
    match f with
    | Err -> Err
    | OK x -> g x
  
  (** val bind2 :
      ('a1 * 'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result **)
  
  let bind2 f g =
    match f with
    | Err -> Err
    | OK p -> let (x, y) = p in g x y
  
  (** val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream **)
  
  let rec app_str l s =
    match l with
    | [] -> s
    | t :: q -> lazy (Cons (t, (app_str q s)))
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  (** val state_of_stack : A.initstate -> stack -> A.state **)
  
  let state_of_stack init = function
  | [] -> A.Init init
  | s0 :: l -> let Coq_existT (s, n) = s0 in A.Ninit s
  
  (** val pop :
      A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack * 'a1) result **)
  
  let rec pop symbols_to_pop stack_cur action =
    match symbols_to_pop with
    | [] -> OK (stack_cur, (Obj.magic action))
    | t :: q ->
      (match stack_cur with
       | [] -> Err
       | s :: stack_rec ->
         let Coq_existT (state_cur, sem) = s in
         if compare_eqdec A.Gram.coq_SymbolAlph.coq_AlphabetComparable
              (A.last_symb_of_non_init_state state_cur) t
         then pop q stack_rec (Obj.magic action sem)
         else Err)
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  | Progress_sr of stack * A.GramDefs.token coq_Stream
  
  (** val step_result_rect :
      A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
      coq_Stream -> 'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) ->
      step_result -> 'a1 **)
  
  let step_result_rect init f f0 f1 = function
  | Fail_sr -> f
  | Accept_sr (x, x0) -> f0 x x0
  | Progress_sr (x, x0) -> f1 x x0
  
  (** val step_result_rec :
      A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
      coq_Stream -> 'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) ->
      step_result -> 'a1 **)
  
  let step_result_rec init f f0 f1 = function
  | Fail_sr -> f
  | Accept_sr (x, x0) -> f0 x x0
  | Progress_sr (x, x0) -> f1 x x0
  
  (** val prod_action' :
      A.Gram.production -> A.Gram.symbol_semantic_type arrows_right **)
  
  let prod_action' p =
    A.Gram.prod_action p
  
  (** val reduce_step :
      A.initstate -> stack -> A.Gram.production -> A.GramDefs.token
      coq_Stream -> step_result result **)
  
  let reduce_step init stack_cur production0 buffer =
    bind2
      (pop (A.Gram.prod_rhs_rev production0) stack_cur
        (prod_action' production0)) (fun stack_new sem ->
      match A.goto_table (state_of_stack init stack_new)
              (A.Gram.prod_lhs production0) with
      | Some s ->
        OK (Progress_sr (((Coq_existT (s, sem)) :: stack_new), buffer))
      | None ->
        (match stack_new with
         | [] ->
           if compare_eqdec A.Gram.coq_NonTerminalAlph.coq_AlphabetComparable
                (A.Gram.prod_lhs production0) (A.start_nt init)
           then OK (Accept_sr (sem, buffer))
           else Err
         | s :: l -> Err))
  
  (** val step :
      A.initstate -> stack -> A.GramDefs.token coq_Stream -> step_result
      result **)
  
  let step init stack_cur buffer =
    match A.action_table (state_of_stack init stack_cur) with
    | A.Default_reduce_act production0 ->
      reduce_step init stack_cur production0 buffer
    | A.Lookahead_act awt ->
      let Coq_existT (term, sem) = hd buffer in
      (match awt term with
       | A.Shift_act state_new ->
         OK (Progress_sr (((Coq_existT (state_new, sem)) :: stack_cur),
           (tl buffer)))
       | A.Reduce_act production0 ->
         reduce_step init stack_cur production0 buffer
       | A.Fail_act -> OK Fail_sr)
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  
  (** val parse_result_rect :
      A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
      A.GramDefs.token coq_Stream -> 'a1) -> parse_result -> 'a1 **)
  
  let parse_result_rect init f f0 f1 = function
  | Fail_pr -> f
  | Timeout_pr -> f0
  | Parsed_pr (x, x0) -> f1 x x0
  
  (** val parse_result_rec :
      A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
      A.GramDefs.token coq_Stream -> 'a1) -> parse_result -> 'a1 **)
  
  let parse_result_rec init f f0 f1 = function
  | Fail_pr -> f
  | Timeout_pr -> f0
  | Parsed_pr (x, x0) -> f1 x x0
  
  (** val parse_fix :
      A.initstate -> stack -> A.GramDefs.token coq_Stream -> nat ->
      parse_result result **)
  
  let rec parse_fix init stack_cur buffer = function
  | O -> OK Timeout_pr
  | S it ->
    bind (step init stack_cur buffer) (fun r ->
      match r with
      | Fail_sr -> OK Fail_pr
      | Accept_sr (t, buffer_new) -> OK (Parsed_pr (t, buffer_new))
      | Progress_sr (s, buffer_new) -> parse_fix init s buffer_new it)
  
  (** val parse :
      A.initstate -> A.GramDefs.token coq_Stream -> nat -> parse_result
      result **)
  
  let parse init buffer n_steps =
    parse_fix init [] buffer n_steps
 end

