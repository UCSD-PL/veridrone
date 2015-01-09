open AST
open BinNums
open Coqlib
open Datatypes
open FSetAVL
open Int0
open Maps
open Ordered

type reg = positive

module Reg = 
 struct 
  (** val eq : positive -> positive -> bool **)
  
  let eq =
    peq
  
  type typenv = typ PMap.t
 end

module Regset = Make(OrderedPositive)

