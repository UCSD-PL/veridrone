open Alphabet
open Automaton
open Datatypes
open List0

module Make = 
 functor (A:T) ->
 struct 
  (** val singleton_state_pred : A.state -> A.state -> bool **)
  
  let singleton_state_pred state0 state' =
    match compare A.coq_StateAlph.coq_AlphabetComparable state0 state' with
    | Eq -> true
    | _ -> false
  
  (** val past_state_of_state : A.state -> (A.state -> bool) list **)
  
  let past_state_of_state = function
  | A.Init i -> []
  | A.Ninit nis -> A.past_state_of_non_init_state nis
  
  (** val head_symbs_of_state : A.state -> A.Gram.symbol list **)
  
  let head_symbs_of_state = function
  | A.Init i -> []
  | A.Ninit s ->
    (A.last_symb_of_non_init_state s) :: (A.past_symb_of_non_init_state s)
  
  (** val head_states_of_state : A.state -> (A.state -> bool) list **)
  
  let head_states_of_state state0 =
    (singleton_state_pred state0) :: (past_state_of_state state0)
  
  (** val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool **)
  
  let rec is_prefix l1 l2 =
    match l1 with
    | [] -> true
    | t1 :: q1 ->
      (match l2 with
       | [] -> false
       | t2 :: q2 ->
         (&&)
           (compare_eqb A.Gram.coq_SymbolAlph.coq_AlphabetComparable t1 t2)
           (is_prefix q1 q2))
  
  (** val is_shift_head_symbs : unit -> bool **)
  
  let is_shift_head_symbs x =
    forallb (fun s ->
      match A.action_table s with
      | A.Default_reduce_act p -> true
      | A.Lookahead_act awp ->
        forallb (fun t ->
          match awp t with
          | A.Shift_act s2 ->
            is_prefix (A.past_symb_of_non_init_state s2)
              (head_symbs_of_state s)
          | _ -> true) (all_list A.Gram.coq_TerminalAlph.coq_AlphabetFinite))
      (all_list A.coq_StateAlph.coq_AlphabetFinite)
  
  (** val is_goto_head_symbs : unit -> bool **)
  
  let is_goto_head_symbs x =
    forallb (fun s ->
      forallb (fun nt ->
        match A.goto_table s nt with
        | Some s0 ->
          is_prefix (A.past_symb_of_non_init_state s0)
            (head_symbs_of_state s)
        | None -> true)
        (all_list A.Gram.coq_NonTerminalAlph.coq_AlphabetFinite))
      (all_list A.coq_StateAlph.coq_AlphabetFinite)
  
  (** val is_prefix_pred :
      (A.state -> bool) list -> (A.state -> bool) list -> bool **)
  
  let rec is_prefix_pred l1 l2 =
    match l1 with
    | [] -> true
    | f1 :: q1 ->
      (match l2 with
       | [] -> false
       | f2 :: q2 ->
         (&&)
           (forallb (fun x -> implb (f2 x) (f1 x))
             (all_list A.coq_StateAlph.coq_AlphabetFinite))
           (is_prefix_pred q1 q2))
  
  (** val is_shift_past_state : unit -> bool **)
  
  let is_shift_past_state x =
    forallb (fun s ->
      match A.action_table s with
      | A.Default_reduce_act p -> true
      | A.Lookahead_act awp ->
        forallb (fun t ->
          match awp t with
          | A.Shift_act s2 ->
            is_prefix_pred (A.past_state_of_non_init_state s2)
              (head_states_of_state s)
          | _ -> true) (all_list A.Gram.coq_TerminalAlph.coq_AlphabetFinite))
      (all_list A.coq_StateAlph.coq_AlphabetFinite)
  
  (** val is_goto_past_state : unit -> bool **)
  
  let is_goto_past_state x =
    forallb (fun s ->
      forallb (fun nt ->
        match A.goto_table s nt with
        | Some s0 ->
          is_prefix_pred (A.past_state_of_non_init_state s0)
            (head_states_of_state s)
        | None -> true)
        (all_list A.Gram.coq_NonTerminalAlph.coq_AlphabetFinite))
      (all_list A.coq_StateAlph.coq_AlphabetFinite)
  
  (** val is_state_valid_after_pop :
      A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool **)
  
  let rec is_state_valid_after_pop state0 to_pop = function
  | [] -> true
  | p :: pl ->
    (match to_pop with
     | [] -> p state0
     | s :: sl -> is_state_valid_after_pop state0 sl pl)
  
  (** val is_valid_for_reduce : A.state -> A.Gram.production -> bool **)
  
  let is_valid_for_reduce state0 prod =
    (&&) (is_prefix (A.Gram.prod_rhs_rev prod) (head_symbs_of_state state0))
      (forallb (fun state_new ->
        if is_state_valid_after_pop state_new (A.Gram.prod_rhs_rev prod)
             (head_states_of_state state0)
        then (match A.goto_table state_new (A.Gram.prod_lhs prod) with
              | Some s -> true
              | None ->
                (match state_new with
                 | A.Init i ->
                   compare_eqb
                     A.Gram.coq_NonTerminalAlph.coq_AlphabetComparable
                     (A.Gram.prod_lhs prod) (A.start_nt i)
                 | A.Ninit n -> false))
        else true) (all_list A.coq_StateAlph.coq_AlphabetFinite))
  
  (** val is_reduce_ok : unit -> bool **)
  
  let is_reduce_ok x =
    forallb (fun s ->
      match A.action_table s with
      | A.Default_reduce_act p -> is_valid_for_reduce s p
      | A.Lookahead_act awp ->
        forallb (fun t ->
          match awp t with
          | A.Reduce_act p -> is_valid_for_reduce s p
          | _ -> true) (all_list A.Gram.coq_TerminalAlph.coq_AlphabetFinite))
      (all_list A.coq_StateAlph.coq_AlphabetFinite)
  
  (** val is_safe : unit -> bool **)
  
  let is_safe x =
    (&&)
      ((&&)
        ((&&) ((&&) (is_shift_head_symbs ()) (is_goto_head_symbs ()))
          (is_shift_past_state ())) (is_goto_past_state ()))
      (is_reduce_ok ())
 end

