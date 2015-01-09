open Alphabet
open Automaton
open Datatypes
open Int0
open Interpreter
open Interpreter_complete
open Interpreter_correct
open Interpreter_safe
open Specif
open Streams
open Tuples

type __ = Obj.t

module Make = 
 functor (Aut:T) ->
 struct 
  module Inter = Interpreter.Make(Aut)
  
  module Safe = Make(Aut)(Inter)
  
  module Correct = Interpreter_correct.Make(Aut)(Inter)
  
  module Complete = Interpreter_complete.Make(Aut)(Inter)
  
  (** val complete_validator : unit -> bool **)
  
  let complete_validator =
    Complete.Valid.is_complete
  
  (** val safe_validator : unit -> bool **)
  
  let safe_validator =
    Safe.Valid.is_safe
  
  (** val parse :
      Aut.initstate -> nat -> Aut.GramDefs.token coq_Stream ->
      Inter.parse_result **)
  
  let parse init n_steps buffer =
    Safe.parse_with_safe init buffer n_steps
 end

