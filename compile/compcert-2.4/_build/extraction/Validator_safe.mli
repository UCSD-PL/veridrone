open Alphabet
open Automaton
open Datatypes
open List0

module Make : 
 functor (A:T) ->
 sig 
  val singleton_state_pred : A.state -> A.state -> bool
  
  val past_state_of_state : A.state -> (A.state -> bool) list
  
  val head_symbs_of_state : A.state -> A.Gram.symbol list
  
  val head_states_of_state : A.state -> (A.state -> bool) list
  
  val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool
  
  val is_shift_head_symbs : unit -> bool
  
  val is_goto_head_symbs : unit -> bool
  
  val is_prefix_pred :
    (A.state -> bool) list -> (A.state -> bool) list -> bool
  
  val is_shift_past_state : unit -> bool
  
  val is_goto_past_state : unit -> bool
  
  val is_state_valid_after_pop :
    A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool
  
  val is_valid_for_reduce : A.state -> A.Gram.production -> bool
  
  val is_reduce_ok : unit -> bool
  
  val is_safe : unit -> bool
 end

