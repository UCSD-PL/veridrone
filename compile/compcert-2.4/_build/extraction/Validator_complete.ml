open Alphabet
open Automaton
open Datatypes
open FMapAVL
open FSetAVL
open Int0
open List0

type __ = Obj.t

module Make = 
 functor (A:T) ->
 struct 
  module TerminalComparableM = 
   struct 
    type t = A.Gram.terminal
    
    (** val tComparable : t coq_Comparable **)
    
    let tComparable =
      A.Gram.coq_TerminalAlph.coq_AlphabetComparable
   end
  
  module TerminalOrderedType = OrderedType_from_ComparableM(TerminalComparableM)
  
  module StateProdPosComparableM = 
   struct 
    type t = (A.state * A.Gram.production) * nat
    
    (** val tComparable : t coq_Comparable **)
    
    let tComparable =
      coq_PairComparable
        (coq_PairComparable A.coq_StateAlph.coq_AlphabetComparable
          A.Gram.coq_ProductionAlph.coq_AlphabetComparable) natComparable
   end
  
  module StateProdPosOrderedType = OrderedType_from_ComparableM(StateProdPosComparableM)
  
  module TerminalSet = Make(TerminalOrderedType)
  
  module StateProdPosMap = FMapAVL.Make(StateProdPosOrderedType)
  
  (** val nullable_symb : A.Gram.symbol -> bool **)
  
  let nullable_symb = function
  | A.Gram.T t0 -> false
  | A.Gram.NT nt -> A.nullable_nterm nt
  
  (** val nullable_word : A.Gram.symbol list -> bool **)
  
  let nullable_word word =
    forallb nullable_symb word
  
  (** val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t **)
  
  let first_nterm_set nterm =
    fold_left (fun acc t0 -> TerminalSet.add t0 acc) (A.first_nterm nterm)
      TerminalSet.empty
  
  (** val first_symb_set : A.Gram.symbol -> TerminalSet.t **)
  
  let first_symb_set = function
  | A.Gram.T t0 -> TerminalSet.singleton t0
  | A.Gram.NT nt -> first_nterm_set nt
  
  (** val first_word_set : A.Gram.symbol list -> TerminalSet.t **)
  
  let rec first_word_set = function
  | [] -> TerminalSet.empty
  | t0 :: q ->
    if nullable_symb t0
    then TerminalSet.union (first_symb_set t0) (first_word_set q)
    else first_symb_set t0
  
  (** val future_of_prod : A.Gram.production -> nat -> A.Gram.symbol list **)
  
  let future_of_prod prod dot_pos =
    let rec loop n lst =
      match n with
      | O -> lst
      | S x ->
        (match loop x lst with
         | [] -> []
         | y :: q -> q)
    in loop dot_pos (rev' (A.Gram.prod_rhs_rev prod))
  
  (** val items_map : unit -> TerminalSet.t StateProdPosMap.t **)
  
  let items_map x =
    fold_left (fun acc state0 ->
      fold_left (fun acc0 item ->
        let key0 = ((state0, (A.prod_item item)), (A.dot_pos_item item)) in
        let data =
          fold_left (fun acc1 t0 -> TerminalSet.add t0 acc1)
            (A.lookaheads_item item) TerminalSet.empty
        in
        let old =
          match StateProdPosMap.find key0 acc0 with
          | Some x0 -> x0
          | None -> TerminalSet.empty
        in
        StateProdPosMap.add key0 (TerminalSet.union data old) acc0)
        (A.items_of_state state0) acc)
      (all_list A.coq_StateAlph.coq_AlphabetFinite) StateProdPosMap.empty
  
  (** val find_items_map :
      TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> nat
      -> TerminalSet.t **)
  
  let find_items_map items_map0 state0 prod dot_pos =
    match StateProdPosMap.find ((state0, prod), dot_pos) items_map0 with
    | Some x -> x
    | None -> TerminalSet.empty
  
  (** val forallb_items :
      TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> nat
      -> TerminalSet.t -> bool) -> bool **)
  
  let forallb_items items_map0 p =
    StateProdPosMap.fold (fun key0 set acc ->
      let (p0, pos) = key0 in let (st, p1) = p0 in (&&) acc (p st p1 pos set))
      items_map0 true
  
  (** val is_nullable_stable : unit -> bool **)
  
  let is_nullable_stable x =
    forallb (fun p ->
      implb (nullable_word (rev' (A.Gram.prod_rhs_rev p)))
        (A.nullable_nterm (A.Gram.prod_lhs p)))
      (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite)
  
  (** val is_first_stable : unit -> bool **)
  
  let is_first_stable x =
    forallb (fun p ->
      TerminalSet.subset (first_word_set (rev' (A.Gram.prod_rhs_rev p)))
        (first_nterm_set (A.Gram.prod_lhs p)))
      (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite)
  
  (** val is_start_future : TerminalSet.t StateProdPosMap.t -> bool **)
  
  let is_start_future items_map0 =
    forallb (fun init ->
      forallb (fun prod ->
        if compare_eqb A.Gram.coq_NonTerminalAlph.coq_AlphabetComparable
             (A.Gram.prod_lhs prod) (A.start_nt init)
        then let lookaheads = find_items_map items_map0 (A.Init init) prod O
             in
             forallb (fun t0 -> TerminalSet.mem t0 lookaheads)
               (all_list A.Gram.coq_TerminalAlph.coq_AlphabetFinite)
        else true) (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite))
      (all_list A.coq_InitStateAlph.coq_AlphabetFinite)
  
  (** val is_terminal_shift : TerminalSet.t StateProdPosMap.t -> bool **)
  
  let is_terminal_shift items_map0 =
    forallb_items items_map0 (fun s1 prod pos lset ->
      match future_of_prod prod pos with
      | [] -> true
      | s :: l ->
        (match s with
         | A.Gram.T t0 ->
           (match A.action_table s1 with
            | A.Default_reduce_act p -> false
            | A.Lookahead_act awp ->
              (match awp t0 with
               | A.Shift_act s2 ->
                 TerminalSet.subset lset
                   (find_items_map items_map0 (A.Ninit s2) prod (S pos))
               | _ -> false))
         | A.Gram.NT n -> true))
  
  (** val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool **)
  
  let is_end_reduce items_map0 =
    forallb_items items_map0 (fun s prod pos lset ->
      match future_of_prod prod pos with
      | [] ->
        (match A.action_table s with
         | A.Default_reduce_act p ->
           compare_eqb A.Gram.coq_ProductionAlph.coq_AlphabetComparable p
             prod
         | A.Lookahead_act awt ->
           TerminalSet.fold (fun lookahead acc ->
             match awt lookahead with
             | A.Reduce_act p ->
               (&&) acc
                 (compare_eqb
                   A.Gram.coq_ProductionAlph.coq_AlphabetComparable p prod)
             | _ -> false) lset true)
      | s0 :: l -> true)
  
  (** val is_non_terminal_goto : TerminalSet.t StateProdPosMap.t -> bool **)
  
  let is_non_terminal_goto items_map0 =
    forallb_items items_map0 (fun s1 prod pos lset ->
      match future_of_prod prod pos with
      | [] -> true
      | s :: l ->
        (match s with
         | A.Gram.T t0 -> true
         | A.Gram.NT nt ->
           (match A.goto_table s1 nt with
            | Some s0 ->
              TerminalSet.subset lset
                (find_items_map items_map0 (A.Ninit s0) prod (S pos))
            | None ->
              forallb_items items_map0 (fun s1' prod' pos' x ->
                implb
                  (compare_eqb A.coq_StateAlph.coq_AlphabetComparable s1 s1')
                  (match future_of_prod prod' pos' with
                   | [] -> true
                   | s0 :: l0 ->
                     (match s0 with
                      | A.Gram.T t0 -> true
                      | A.Gram.NT nt' ->
                        negb
                          (compare_eqb
                            A.Gram.coq_NonTerminalAlph.coq_AlphabetComparable
                            nt nt')))))))
  
  (** val is_start_goto : unit -> bool **)
  
  let is_start_goto x =
    forallb (fun init ->
      match A.goto_table (A.Init init) (A.start_nt init) with
      | Some s -> false
      | None -> true) (all_list A.coq_InitStateAlph.coq_AlphabetFinite)
  
  (** val is_non_terminal_closed :
      TerminalSet.t StateProdPosMap.t -> bool **)
  
  let is_non_terminal_closed items_map0 =
    forallb_items items_map0 (fun s1 prod pos lset ->
      match future_of_prod prod pos with
      | [] -> true
      | s :: q ->
        (match s with
         | A.Gram.T t0 -> true
         | A.Gram.NT nt ->
           forallb (fun p ->
             if compare_eqb A.Gram.coq_NonTerminalAlph.coq_AlphabetComparable
                  (A.Gram.prod_lhs p) nt
             then let lookaheads = find_items_map items_map0 s1 p O in
                  (&&)
                    (implb (nullable_word q)
                      (TerminalSet.subset lset lookaheads))
                    (TerminalSet.subset (first_word_set q) lookaheads)
             else true)
             (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite)))
  
  (** val is_complete : unit -> bool **)
  
  let is_complete x =
    let items_map0 = items_map () in
    (&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&) ((&&) (is_nullable_stable ()) (is_first_stable ()))
                (is_start_future items_map0)) (is_terminal_shift items_map0))
            (is_end_reduce items_map0)) (is_start_goto ()))
        (is_non_terminal_goto items_map0))
      (is_non_terminal_closed items_map0)
 end

