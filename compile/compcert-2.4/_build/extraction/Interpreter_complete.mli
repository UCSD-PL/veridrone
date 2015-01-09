open Alphabet
open Automaton
open Datatypes
open Int0
open List0
open Peano
open Specif
open Streams
open Tuples
open Validator_complete

type __ = Obj.t

module Make : 
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
 sig 
  module Valid : 
   sig 
    module TerminalComparableM : 
     sig 
      type t = A.Gram.terminal
      
      val tComparable : t coq_Comparable
     end
    
    module TerminalOrderedType : 
     sig 
      module Alt : 
       sig 
        type t = TerminalComparableM.t
        
        val compare : t -> t -> comparison
       end
      
      type t = Alt.t
      
      val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
      
      val eq_dec : Alt.t -> Alt.t -> bool
     end
    
    module StateProdPosComparableM : 
     sig 
      type t = (A.state * A.Gram.production) * nat
      
      val tComparable : t coq_Comparable
     end
    
    module StateProdPosOrderedType : 
     sig 
      module Alt : 
       sig 
        type t = StateProdPosComparableM.t
        
        val compare : t -> t -> comparison
       end
      
      type t = Alt.t
      
      val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
      
      val eq_dec : Alt.t -> Alt.t -> bool
     end
    
    module TerminalSet : 
     sig 
      module X' : 
       sig 
        type t = TerminalOrderedType.Alt.t
        
        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
        
        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
          comparison
       end
      
      module MSet : 
       sig 
        module Raw : 
         sig 
          type elt = TerminalOrderedType.Alt.t
          
          type tree =
          | Leaf
          | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
          
          val empty : tree
          
          val is_empty : tree -> bool
          
          val mem : TerminalOrderedType.Alt.t -> tree -> bool
          
          val min_elt : tree -> elt option
          
          val max_elt : tree -> elt option
          
          val choose : tree -> elt option
          
          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
          
          val elements_aux :
            TerminalOrderedType.Alt.t list -> tree ->
            TerminalOrderedType.Alt.t list
          
          val elements : tree -> TerminalOrderedType.Alt.t list
          
          val rev_elements_aux :
            TerminalOrderedType.Alt.t list -> tree ->
            TerminalOrderedType.Alt.t list
          
          val rev_elements : tree -> TerminalOrderedType.Alt.t list
          
          val cardinal : tree -> nat
          
          val maxdepth : tree -> nat
          
          val mindepth : tree -> nat
          
          val for_all : (elt -> bool) -> tree -> bool
          
          val exists_ : (elt -> bool) -> tree -> bool
          
          type enumeration =
          | End
          | More of elt * tree * enumeration
          
          val cons : tree -> enumeration -> enumeration
          
          val compare_more :
            TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
            enumeration -> comparison
          
          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison
          
          val compare_end : enumeration -> comparison
          
          val compare : tree -> tree -> comparison
          
          val equal : tree -> tree -> bool
          
          val subsetl :
            (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
          
          val subsetr :
            (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
          
          val subset : tree -> tree -> bool
          
          type t = tree
          
          val height : t -> Z_as_Int.t
          
          val singleton : TerminalOrderedType.Alt.t -> tree
          
          val create : t -> TerminalOrderedType.Alt.t -> t -> tree
          
          val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree
          
          val bal : t -> TerminalOrderedType.Alt.t -> t -> tree
          
          val add : TerminalOrderedType.Alt.t -> tree -> tree
          
          val join : tree -> elt -> t -> t
          
          val remove_min : tree -> elt -> t -> t * elt
          
          val merge : tree -> tree -> tree
          
          val remove : TerminalOrderedType.Alt.t -> tree -> tree
          
          val concat : tree -> tree -> tree
          
          type triple = { t_left : t; t_in : bool; t_right : t }
          
          val t_left : triple -> t
          
          val t_in : triple -> bool
          
          val t_right : triple -> t
          
          val split : TerminalOrderedType.Alt.t -> tree -> triple
          
          val inter : tree -> tree -> tree
          
          val diff : tree -> tree -> tree
          
          val union : tree -> tree -> tree
          
          val filter : (elt -> bool) -> tree -> tree
          
          val partition : (elt -> bool) -> t -> t * t
          
          val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool
          
          val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool
          
          val isok : tree -> bool
          
          module MX : 
           sig 
            module OrderTac : 
             sig 
              module OTF : 
               sig 
                type t = TerminalOrderedType.Alt.t
                
                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
              
              module TO : 
               sig 
                type t = TerminalOrderedType.Alt.t
                
                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end
            
            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
            
            val lt_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
            
            val eqb :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end
          
          type coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * elt option * coq_R_min_elt
          
          type coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * elt option * coq_R_max_elt
          
          module L : 
           sig 
            module MO : 
             sig 
              module OrderTac : 
               sig 
                module OTF : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
                
                module TO : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
              
              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
              
              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
             end
           end
          
          val flatten_e : enumeration -> elt list
          
          type coq_R_bal =
          | R_bal_0 of t * TerminalOrderedType.Alt.t * t
          | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_bal_4 of t * TerminalOrderedType.Alt.t * t
          | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_bal_8 of t * TerminalOrderedType.Alt.t * t
          
          type coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * (t * elt)
             * coq_R_remove_min * t * elt
          
          type coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * elt
          
          type coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * elt
          
          type coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter
          
          type coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff
          
          type coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_union * tree * coq_R_union
         end
        
        module E : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
        
        type elt = TerminalOrderedType.Alt.t
        
        type t_ =
          Raw.t
          (* singleton inductive, whose constructor was Mkt *)
        
        val this : t_ -> Raw.t
        
        type t = t_
        
        val mem : elt -> t -> bool
        
        val add : elt -> t -> t
        
        val remove : elt -> t -> t
        
        val singleton : elt -> t
        
        val union : t -> t -> t
        
        val inter : t -> t -> t
        
        val diff : t -> t -> t
        
        val equal : t -> t -> bool
        
        val subset : t -> t -> bool
        
        val empty : t
        
        val is_empty : t -> bool
        
        val elements : t -> elt list
        
        val choose : t -> elt option
        
        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
        
        val cardinal : t -> nat
        
        val filter : (elt -> bool) -> t -> t
        
        val for_all : (elt -> bool) -> t -> bool
        
        val exists_ : (elt -> bool) -> t -> bool
        
        val partition : (elt -> bool) -> t -> t * t
        
        val eq_dec : t -> t -> bool
        
        val compare : t -> t -> comparison
        
        val min_elt : t -> elt option
        
        val max_elt : t -> elt option
       end
      
      type elt = TerminalOrderedType.Alt.t
      
      type t = MSet.t
      
      val empty : t
      
      val is_empty : t -> bool
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val singleton : elt -> t
      
      val remove : elt -> t -> t
      
      val union : t -> t -> t
      
      val inter : t -> t -> t
      
      val diff : t -> t -> t
      
      val eq_dec : t -> t -> bool
      
      val equal : t -> t -> bool
      
      val subset : t -> t -> bool
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val filter : (elt -> bool) -> t -> t
      
      val partition : (elt -> bool) -> t -> t * t
      
      val cardinal : t -> nat
      
      val elements : t -> elt list
      
      val choose : t -> elt option
      
      module MF : 
       sig 
        val eqb :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
       end
      
      val min_elt : t -> elt option
      
      val max_elt : t -> elt option
      
      val compare : t -> t -> t OrderedType.coq_Compare
      
      module E : 
       sig 
        type t = TerminalOrderedType.Alt.t
        
        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
          TerminalOrderedType.Alt.t OrderedType.coq_Compare
        
        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
       end
     end
    
    module StateProdPosMap : 
     sig 
      module E : 
       sig 
        type t = StateProdPosOrderedType.Alt.t
        
        val compare :
          StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
          StateProdPosOrderedType.Alt.t OrderedType.coq_Compare
        
        val eq_dec :
          StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
          bool
       end
      
      module Raw : 
       sig 
        type key = StateProdPosOrderedType.Alt.t
        
        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
        
        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
        
        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2
        
        val height : 'a1 tree -> Z_as_Int.t
        
        val cardinal : 'a1 tree -> nat
        
        val empty : 'a1 tree
        
        val is_empty : 'a1 tree -> bool
        
        val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool
        
        val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option
        
        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)
        
        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
        
        val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree
        
        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
        
        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }
        
        val triple_rect :
          ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
        
        val triple_rec :
          ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
        
        val t_left : 'a1 triple -> 'a1 tree
        
        val t_opt : 'a1 triple -> 'a1 option
        
        val t_right : 'a1 triple -> 'a1 tree
        
        val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple
        
        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
        
        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list
        
        val elements : 'a1 tree -> (key * 'a1) list
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
        
        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration
        
        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2
        
        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2
        
        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
        
        val equal_more :
          ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
          ('a1 enumeration -> bool) -> 'a1 enumeration -> bool
        
        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool
        
        val equal_end : 'a1 enumeration -> bool
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
        
        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
        
        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
        
        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree
        
        module Proofs : 
         sig 
          module MX : 
           sig 
            module TO : 
             sig 
              type t = StateProdPosOrderedType.Alt.t
             end
            
            module IsTO : 
             sig 
              
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
            
            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
            
            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end
          
          module PX : 
           sig 
            module MO : 
             sig 
              module TO : 
               sig 
                type t = StateProdPosOrderedType.Alt.t
               end
              
              module IsTO : 
               sig 
                
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
              
              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
              
              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
           end
          
          module L : 
           sig 
            module MX : 
             sig 
              module TO : 
               sig 
                type t = StateProdPosOrderedType.Alt.t
               end
              
              module IsTO : 
               sig 
                
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
              
              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
              
              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
            
            module PX : 
             sig 
              module MO : 
               sig 
                module TO : 
                 sig 
                  type t = StateProdPosOrderedType.Alt.t
                 end
                
                module IsTO : 
                 sig 
                  
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
                
                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
                
                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end
            
            type key = StateProdPosOrderedType.Alt.t
            
            type 'elt t = (StateProdPosOrderedType.Alt.t * 'elt) list
            
            val empty : 'a1 t
            
            val is_empty : 'a1 t -> bool
            
            val mem : key -> 'a1 t -> bool
            
            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
               * 'elt coq_R_mem
            
            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
              coq_R_mem -> 'a2
            
            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
              coq_R_mem -> 'a2
            
            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
            
            val find : key -> 'a1 t -> 'a1 option
            
            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt option
               * 'elt coq_R_find
            
            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              option -> 'a1 coq_R_find -> 'a2
            
            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              option -> 'a1 coq_R_find -> 'a2
            
            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
            
            val add : key -> 'a1 -> 'a1 t -> 'a1 t
            
            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
               * 'elt coq_R_add
            
            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_add -> 'a2
            
            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_add -> 'a2
            
            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
            
            val remove : key -> 'a1 t -> 'a1 t
            
            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
               * 'elt coq_R_remove
            
            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
              'a1 coq_R_remove -> 'a2
            
            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
              'a1 coq_R_remove -> 'a2
            
            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2
            
            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            
            val elements : 'a1 t -> 'a1 t
            
            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
            
            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
            | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * 'a
               * ('elt, 'a) coq_R_fold
            
            val coq_R_fold_rect :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> ('a1,
              __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
              'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
            
            val coq_R_fold_rec :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> ('a1,
              __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
              'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
            
            val fold_rect :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 -> 'a2)
              -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
            
            val fold_rec :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 -> 'a2)
              -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
            
            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold
            
            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
            
            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
               * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
               * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
               * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
               * StateProdPosOrderedType.Alt.t OrderedType.coq_Compare
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
            
            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t OrderedType.coq_Compare -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
            
            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t OrderedType.coq_Compare -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
            
            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t
              -> 'a1 -> (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t OrderedType.coq_Compare -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
            
            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t
              -> 'a1 -> (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t OrderedType.coq_Compare -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
            
            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal
            
            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
            
            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
            
            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list
            
            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
            
            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
            
            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t
            
            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t
            
            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3
            
            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list
            
            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option
            
            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end
          
          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          
          val coq_R_mem_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
            'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
          
          val coq_R_mem_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
            'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
          
          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          
          val coq_R_find_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          val coq_R_find_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
          
          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
          
          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
          
          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          
          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
          
          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
          
          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)
          
          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2
          
          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2
          
          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt
          
          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2
          
          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2
          
          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          
          val coq_R_remove_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2
          
          val coq_R_remove_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2
          
          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)
          
          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
          
          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
          
          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          
          val coq_R_split_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1
            tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
            triple -> 'a1 coq_R_split -> 'a2
          
          val coq_R_split_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1
            tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
            triple -> 'a1 coq_R_split -> 'a2
          
          type ('elt, 'elt') coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt' * 'elt' tree
             * ('elt, 'elt') coq_R_map_option * 'elt' tree
             * ('elt, 'elt') coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt' tree * ('elt, 'elt') coq_R_map_option
             * 'elt' tree * ('elt, 'elt') coq_R_map_option
          
          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3
          
          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3
          
          type ('elt, 'elt', 'elt'') coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'elt' tree
          | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
             * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option
             * 'elt' tree * 'elt'' * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'elt' tree * key * 'elt'
             * 'elt' tree * Z_as_Int.t * 'elt' tree * 'elt' option
             * 'elt' tree * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
             * ('elt, 'elt', 'elt'') coq_R_map2_opt
          
          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
          
          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
          
          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
          
          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end
      
      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)
      
      val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
      
      val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
      
      val this : 'a1 bst -> 'a1 Raw.tree
      
      type 'elt t = 'elt bst
      
      type key = StateProdPosOrderedType.Alt.t
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      val remove : key -> 'a1 t -> 'a1 t
      
      val mem : key -> 'a1 t -> bool
      
      val find : key -> 'a1 t -> 'a1 option
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val elements : 'a1 t -> (key * 'a1) list
      
      val cardinal : 'a1 t -> nat
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end
    
    val nullable_symb : A.Gram.symbol -> bool
    
    val nullable_word : A.Gram.symbol list -> bool
    
    val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t
    
    val first_symb_set : A.Gram.symbol -> TerminalSet.t
    
    val first_word_set : A.Gram.symbol list -> TerminalSet.t
    
    val future_of_prod : A.Gram.production -> nat -> A.Gram.symbol list
    
    val items_map : unit -> TerminalSet.t StateProdPosMap.t
    
    val find_items_map :
      TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> nat
      -> TerminalSet.t
    
    val forallb_items :
      TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> nat
      -> TerminalSet.t -> bool) -> bool
    
    val is_nullable_stable : unit -> bool
    
    val is_first_stable : unit -> bool
    
    val is_start_future : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_terminal_shift : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_non_terminal_goto : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_start_goto : unit -> bool
    
    val is_non_terminal_closed : TerminalSet.t StateProdPosMap.t -> bool
    
    val is_complete : unit -> bool
   end
  
  type pt_zipper =
  | Top_ptz
  | Cons_ptl_ptz of A.Gram.symbol * A.GramDefs.token list
     * A.Gram.symbol_semantic_type * A.Gram.symbol list
     * A.GramDefs.token list * tuple * A.GramDefs.parse_tree_list
     * ptl_zipper
  and ptl_zipper =
  | Non_terminal_pt_ptlz of A.Gram.production * A.GramDefs.token list * 
     tuple * pt_zipper
  | Cons_ptl_ptlz of A.Gram.symbol * A.GramDefs.token list
     * A.Gram.symbol_semantic_type * A.GramDefs.parse_tree
     * A.Gram.symbol list * A.GramDefs.token list * tuple * ptl_zipper
  
  val pt_zipper_rect :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    'a1 -> (A.Gram.symbol -> A.GramDefs.token list ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
    list -> tuple -> A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) ->
    A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_zipper -> 'a1
  
  val pt_zipper_rec :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    'a1 -> (A.Gram.symbol -> A.GramDefs.token list ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
    list -> tuple -> A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) ->
    A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_zipper -> 'a1
  
  val ptl_zipper_rect :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (A.Gram.production -> A.GramDefs.token list -> tuple -> pt_zipper -> 'a1)
    -> (A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
    -> A.GramDefs.parse_tree -> A.Gram.symbol list -> A.GramDefs.token list
    -> tuple -> ptl_zipper -> 'a1 -> 'a1) -> A.Gram.symbol list ->
    A.GramDefs.token list -> tuple -> ptl_zipper -> 'a1
  
  val ptl_zipper_rec :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (A.Gram.production -> A.GramDefs.token list -> tuple -> pt_zipper -> 'a1)
    -> (A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
    -> A.GramDefs.parse_tree -> A.Gram.symbol list -> A.GramDefs.token list
    -> tuple -> ptl_zipper -> 'a1 -> 'a1) -> A.Gram.symbol list ->
    A.GramDefs.token list -> tuple -> ptl_zipper -> 'a1
  
  val ptlz_cost :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper -> nat
  
  val ptz_cost :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_zipper -> nat
  
  type pt_dot =
  | Reduce_ptd of ptl_zipper
  | Shift_ptd of A.Gram.terminal * A.Gram.symbol_semantic_type
     * A.Gram.symbol list * A.GramDefs.token list * tuple
     * A.GramDefs.parse_tree_list * ptl_zipper
  
  val pt_dot_rect :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (ptl_zipper -> 'a1) -> (A.Gram.terminal -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1
  
  val pt_dot_rec :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    (ptl_zipper -> 'a1) -> (A.Gram.terminal -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1
  
  val ptd_cost :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_dot -> nat
  
  val ptlz_buffer :
    A.initstate -> A.GramDefs.token list -> A.GramDefs.token coq_Stream ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
    list -> tuple -> ptl_zipper -> A.GramDefs.token coq_Stream
  
  val ptz_buffer :
    A.initstate -> A.GramDefs.token list -> A.GramDefs.token coq_Stream ->
    A.Gram.symbol_semantic_type -> A.Gram.symbol -> A.GramDefs.token list ->
    A.Gram.symbol_semantic_type -> pt_zipper -> A.GramDefs.token coq_Stream
  
  val ptd_buffer :
    A.initstate -> A.GramDefs.token list -> A.GramDefs.token coq_Stream ->
    A.Gram.symbol_semantic_type -> pt_dot -> A.GramDefs.token coq_Stream
  
  val ptlz_prod :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
    A.Gram.production
  
  val ptlz_past :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
    A.Gram.symbol list
  
  val build_pt_dot :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot
  
  val pop_ptlz :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
    A.GramDefs.parse_tree_list -> ptl_zipper -> (A.GramDefs.token list,
    (A.Gram.symbol_semantic_type, pt_zipper * A.GramDefs.parse_tree) sigT)
    sigT
  
  val next_ptd :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    pt_dot -> pt_dot option
  
  val init_ptd :
    A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
    A.GramDefs.parse_tree -> pt_dot
 end

