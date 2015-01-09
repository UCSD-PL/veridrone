open AST
open Archi
open BinNums
open BinPos
open Conventions
open Conventions1
open Coqlib
open Datatypes
open Errors
open FSetAVLplus
open Int0
open Integers
open Kildall
open LTL
open Lattice
open List0
open Locations
open Machregs
open Maps
open Op
open Ordered
open RTL
open RTLtyping
open Registers

type moves = (loc * loc) list

type block_shape =
| BSnop of moves * LTL.node
| BSmove of reg * reg * moves * LTL.node
| BSmakelong of reg * reg * reg * moves * LTL.node
| BSlowlong of reg * reg * moves * LTL.node
| BShighlong of reg * reg * moves * LTL.node
| BSop of operation * reg list * reg * moves * mreg list * mreg * moves
   * LTL.node
| BSopdead of operation * reg list * reg * moves * LTL.node
| BSload of memory_chunk * addressing * reg list * reg * moves * mreg list
   * mreg * moves * LTL.node
| BSloaddead of memory_chunk * addressing * reg list * reg * moves * LTL.node
| BSload2 of addressing * addressing * reg list * reg * moves * mreg list
   * mreg * moves * mreg list * mreg * moves * LTL.node
| BSload2_1 of addressing * reg list * reg * moves * mreg list * mreg * 
   moves * LTL.node
| BSload2_2 of addressing * addressing * reg list * reg * moves * mreg list
   * mreg * moves * LTL.node
| BSstore of memory_chunk * addressing * reg list * reg * moves * mreg list
   * mreg * LTL.node
| BSstore2 of addressing * addressing * reg list * reg * moves * mreg list
   * mreg * moves * mreg list * mreg * LTL.node
| BScall of signature * (reg, ident) sum * reg list * reg * moves
   * (mreg, ident) sum * moves * LTL.node
| BStailcall of signature * (reg, ident) sum * reg list * moves
   * (mreg, ident) sum
| BSbuiltin of external_function * reg list * reg * moves * mreg list
   * mreg list * moves * LTL.node
| BSannot of ident * annot_arg list * reg list * reg * moves * loc list
   * LTL.node
| BScond of condition * reg list * moves * mreg list * LTL.node * LTL.node
| BSjumptable of reg * moves * mreg * LTL.node list
| BSreturn of reg option * moves

val extract_moves : moves -> bblock -> moves * bblock

val check_succ : LTL.node -> bblock -> bool

type operation_kind =
| Coq_operation_Omove of reg
| Coq_operation_Omakelong of reg * reg
| Coq_operation_Olowlong of reg
| Coq_operation_Ohighlong of reg
| Coq_operation_other of operation * reg list

val classify_operation : operation -> reg list -> operation_kind

val pair_instr_block : instruction -> bblock -> block_shape option

val pair_codes : coq_function -> LTL.coq_function -> block_shape PTree.t

val pair_entrypoints : coq_function -> LTL.coq_function -> moves option

type equation_kind =
| Full
| Low
| High

type equation = { ekind : equation_kind; ereg : reg; eloc : loc }

val ekind : equation -> equation_kind

val ereg : equation -> reg

val eloc : equation -> loc

module IndexedEqKind : 
 sig 
  type t = equation_kind
  
  val index : t -> positive
  
  val eq : t -> t -> bool
 end

module OrderedEqKind : 
 sig 
  type t = IndexedEqKind.t
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module OrderedEquation : 
 sig 
  type t = equation
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module OrderedEquation' : 
 sig 
  type t = equation
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module EqSet : 
 sig 
  module X' : 
   sig 
    type t = equation
    
    val eq_dec : equation -> equation -> bool
    
    val compare : equation -> equation -> Datatypes.comparison
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = equation
      
      type tree =
      | Leaf
      | Node of Z_as_Int.t * tree * equation * tree
      
      val empty : tree
      
      val is_empty : tree -> bool
      
      val mem : equation -> tree -> bool
      
      val min_elt : tree -> elt option
      
      val max_elt : tree -> elt option
      
      val choose : tree -> elt option
      
      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
      
      val elements_aux : equation list -> tree -> equation list
      
      val elements : tree -> equation list
      
      val rev_elements_aux : equation list -> tree -> equation list
      
      val rev_elements : tree -> equation list
      
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
        equation -> (enumeration -> Datatypes.comparison) -> enumeration ->
        Datatypes.comparison
      
      val compare_cont :
        tree -> (enumeration -> Datatypes.comparison) -> enumeration ->
        Datatypes.comparison
      
      val compare_end : enumeration -> Datatypes.comparison
      
      val compare : tree -> tree -> Datatypes.comparison
      
      val equal : tree -> tree -> bool
      
      val subsetl : (tree -> bool) -> equation -> tree -> bool
      
      val subsetr : (tree -> bool) -> equation -> tree -> bool
      
      val subset : tree -> tree -> bool
      
      type t = tree
      
      val height : t -> Z_as_Int.t
      
      val singleton : equation -> tree
      
      val create : t -> equation -> t -> tree
      
      val assert_false : t -> equation -> t -> tree
      
      val bal : t -> equation -> t -> tree
      
      val add : equation -> tree -> tree
      
      val join : tree -> elt -> t -> t
      
      val remove_min : tree -> elt -> t -> t * elt
      
      val merge : tree -> tree -> tree
      
      val remove : equation -> tree -> tree
      
      val concat : tree -> tree -> tree
      
      type triple = { t_left : t; t_in : bool; t_right : t }
      
      val t_left : triple -> t
      
      val t_in : triple -> bool
      
      val t_right : triple -> t
      
      val split : equation -> tree -> triple
      
      val inter : tree -> tree -> tree
      
      val diff : tree -> tree -> tree
      
      val union : tree -> tree -> tree
      
      val filter : (elt -> bool) -> tree -> tree
      
      val partition : (elt -> bool) -> t -> t * t
      
      val ltb_tree : equation -> tree -> bool
      
      val gtb_tree : equation -> tree -> bool
      
      val isok : tree -> bool
      
      module MX : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
          
          module TO : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
         end
        
        val eq_dec : equation -> equation -> bool
        
        val lt_dec : equation -> equation -> bool
        
        val eqb : equation -> equation -> bool
       end
      
      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Z_as_Int.t * tree * equation * tree
      | R_min_elt_2 of tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * elt option * coq_R_min_elt
      
      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Z_as_Int.t * tree * equation * tree
      | R_max_elt_2 of tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * elt option * coq_R_max_elt
      
      module L : 
       sig 
        module MO : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = equation
              
              val compare : equation -> equation -> Datatypes.comparison
              
              val eq_dec : equation -> equation -> bool
             end
            
            module TO : 
             sig 
              type t = equation
              
              val compare : equation -> equation -> Datatypes.comparison
              
              val eq_dec : equation -> equation -> bool
             end
           end
          
          val eq_dec : equation -> equation -> bool
          
          val lt_dec : equation -> equation -> bool
          
          val eqb : equation -> equation -> bool
         end
       end
      
      val flatten_e : enumeration -> elt list
      
      type coq_R_bal =
      | R_bal_0 of t * equation * t
      | R_bal_1 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_2 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_3 of t * equation * t * Z_as_Int.t * tree * equation * 
         tree * Z_as_Int.t * tree * equation * tree
      | R_bal_4 of t * equation * t
      | R_bal_5 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_6 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_7 of t * equation * t * Z_as_Int.t * tree * equation * 
         tree * Z_as_Int.t * tree * equation * tree
      | R_bal_8 of t * equation * t
      
      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * equation
         * tree * (t * elt) * coq_R_remove_min * t * elt
      
      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * elt
      
      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * elt
      
      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      
      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      
      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end
    
    module E : 
     sig 
      type t = equation
      
      val compare : equation -> equation -> Datatypes.comparison
      
      val eq_dec : equation -> equation -> bool
     end
    
    type elt = equation
    
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
    
    val compare : t -> t -> Datatypes.comparison
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
   end
  
  type elt = equation
  
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
    val eqb : equation -> equation -> bool
   end
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  module E : 
   sig 
    type t = equation
    
    val compare : equation -> equation -> equation OrderedType.coq_Compare
    
    val eq_dec : equation -> equation -> bool
   end
  
  module Raw : 
   sig 
    type elt = equation
    
    type tree = MSet.Raw.tree =
    | Leaf
    | Node of Z_as_Int.t * tree * equation * tree
    
    val empty : tree
    
    val is_empty : tree -> bool
    
    val mem : equation -> tree -> bool
    
    val min_elt : tree -> elt option
    
    val max_elt : tree -> elt option
    
    val choose : tree -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
    
    val elements_aux : equation list -> tree -> equation list
    
    val elements : tree -> equation list
    
    val rev_elements_aux : equation list -> tree -> equation list
    
    val rev_elements : tree -> equation list
    
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
      equation -> (enumeration -> Datatypes.comparison) -> enumeration ->
      Datatypes.comparison
    
    val compare_cont :
      tree -> (enumeration -> Datatypes.comparison) -> enumeration ->
      Datatypes.comparison
    
    val compare_end : enumeration -> Datatypes.comparison
    
    val compare : tree -> tree -> Datatypes.comparison
    
    val equal : tree -> tree -> bool
    
    val subsetl : (tree -> bool) -> equation -> tree -> bool
    
    val subsetr : (tree -> bool) -> equation -> tree -> bool
    
    val subset : tree -> tree -> bool
    
    type t = tree
    
    val height : t -> Z_as_Int.t
    
    val singleton : equation -> tree
    
    val create : t -> equation -> t -> tree
    
    val assert_false : t -> equation -> t -> tree
    
    val bal : t -> equation -> t -> tree
    
    val add : equation -> tree -> tree
    
    val join : tree -> elt -> t -> t
    
    val remove_min : tree -> elt -> t -> t * elt
    
    val merge : tree -> tree -> tree
    
    val remove : equation -> tree -> tree
    
    val concat : tree -> tree -> tree
    
    type triple = { t_left : t; t_in : bool; t_right : t }
    
    val t_left : triple -> t
    
    val t_in : triple -> bool
    
    val t_right : triple -> t
    
    val split : equation -> tree -> triple
    
    val inter : tree -> tree -> tree
    
    val diff : tree -> tree -> tree
    
    val union : tree -> tree -> tree
    
    val filter : (elt -> bool) -> tree -> tree
    
    val partition : (elt -> bool) -> t -> t * t
    
    val ltb_tree : equation -> tree -> bool
    
    val gtb_tree : equation -> tree -> bool
    
    val isok : tree -> bool
    
    module MX : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = equation
          
          val compare : equation -> equation -> Datatypes.comparison
          
          val eq_dec : equation -> equation -> bool
         end
        
        module TO : 
         sig 
          type t = equation
          
          val compare : equation -> equation -> Datatypes.comparison
          
          val eq_dec : equation -> equation -> bool
         end
       end
      
      val eq_dec : equation -> equation -> bool
      
      val lt_dec : equation -> equation -> bool
      
      val eqb : equation -> equation -> bool
     end
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Z_as_Int.t * tree * equation * tree
    | R_min_elt_2 of tree * Z_as_Int.t * tree * equation * tree * Z_as_Int.t
       * tree * equation * tree * elt option * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Z_as_Int.t * tree * equation * tree
    | R_max_elt_2 of tree * Z_as_Int.t * tree * equation * tree * Z_as_Int.t
       * tree * equation * tree * elt option * coq_R_max_elt
    
    module L : 
     sig 
      module MO : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
          
          module TO : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
         end
        
        val eq_dec : equation -> equation -> bool
        
        val lt_dec : equation -> equation -> bool
        
        val eqb : equation -> equation -> bool
       end
     end
    
    val flatten_e : enumeration -> elt list
    
    type coq_R_bal =
    | R_bal_0 of t * equation * t
    | R_bal_1 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_2 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_3 of t * equation * t * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree
    | R_bal_4 of t * equation * t
    | R_bal_5 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_6 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_7 of t * equation * t * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree
    | R_bal_8 of t * equation * t
    
    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * equation * 
       tree * (t * elt) * coq_R_remove_min * t * elt
    
    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_merge_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * elt
    
    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_concat_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * elt
    
    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_inter_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    
    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_diff_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    
    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_union_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end
  
  val raw_mem_between : (elt -> bool) -> (elt -> bool) -> Raw.tree -> bool
  
  val mem_between : (elt -> bool) -> (elt -> bool) -> t -> bool
  
  val raw_elements_between :
    (elt -> bool) -> (elt -> bool) -> Raw.tree -> Raw.tree
  
  val elements_between : (elt -> bool) -> (elt -> bool) -> t -> t
  
  val raw_for_all_between :
    (elt -> bool) -> (elt -> bool) -> (elt -> bool) -> Raw.tree -> bool
  
  val for_all_between :
    (elt -> bool) -> (elt -> bool) -> (elt -> bool) -> t -> bool
  
  val raw_partition_between :
    (elt -> bool) -> (elt -> bool) -> Raw.tree -> Raw.tree * Raw.tree
  
  val partition_between : (elt -> bool) -> (elt -> bool) -> t -> t * t
 end

module EqSet2 : 
 sig 
  module X' : 
   sig 
    type t = equation
    
    val eq_dec : equation -> equation -> bool
    
    val compare : equation -> equation -> Datatypes.comparison
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = equation
      
      type tree =
      | Leaf
      | Node of Z_as_Int.t * tree * equation * tree
      
      val empty : tree
      
      val is_empty : tree -> bool
      
      val mem : equation -> tree -> bool
      
      val min_elt : tree -> elt option
      
      val max_elt : tree -> elt option
      
      val choose : tree -> elt option
      
      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
      
      val elements_aux : equation list -> tree -> equation list
      
      val elements : tree -> equation list
      
      val rev_elements_aux : equation list -> tree -> equation list
      
      val rev_elements : tree -> equation list
      
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
        equation -> (enumeration -> Datatypes.comparison) -> enumeration ->
        Datatypes.comparison
      
      val compare_cont :
        tree -> (enumeration -> Datatypes.comparison) -> enumeration ->
        Datatypes.comparison
      
      val compare_end : enumeration -> Datatypes.comparison
      
      val compare : tree -> tree -> Datatypes.comparison
      
      val equal : tree -> tree -> bool
      
      val subsetl : (tree -> bool) -> equation -> tree -> bool
      
      val subsetr : (tree -> bool) -> equation -> tree -> bool
      
      val subset : tree -> tree -> bool
      
      type t = tree
      
      val height : t -> Z_as_Int.t
      
      val singleton : equation -> tree
      
      val create : t -> equation -> t -> tree
      
      val assert_false : t -> equation -> t -> tree
      
      val bal : t -> equation -> t -> tree
      
      val add : equation -> tree -> tree
      
      val join : tree -> elt -> t -> t
      
      val remove_min : tree -> elt -> t -> t * elt
      
      val merge : tree -> tree -> tree
      
      val remove : equation -> tree -> tree
      
      val concat : tree -> tree -> tree
      
      type triple = { t_left : t; t_in : bool; t_right : t }
      
      val t_left : triple -> t
      
      val t_in : triple -> bool
      
      val t_right : triple -> t
      
      val split : equation -> tree -> triple
      
      val inter : tree -> tree -> tree
      
      val diff : tree -> tree -> tree
      
      val union : tree -> tree -> tree
      
      val filter : (elt -> bool) -> tree -> tree
      
      val partition : (elt -> bool) -> t -> t * t
      
      val ltb_tree : equation -> tree -> bool
      
      val gtb_tree : equation -> tree -> bool
      
      val isok : tree -> bool
      
      module MX : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
          
          module TO : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
         end
        
        val eq_dec : equation -> equation -> bool
        
        val lt_dec : equation -> equation -> bool
        
        val eqb : equation -> equation -> bool
       end
      
      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Z_as_Int.t * tree * equation * tree
      | R_min_elt_2 of tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * elt option * coq_R_min_elt
      
      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Z_as_Int.t * tree * equation * tree
      | R_max_elt_2 of tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * elt option * coq_R_max_elt
      
      module L : 
       sig 
        module MO : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = equation
              
              val compare : equation -> equation -> Datatypes.comparison
              
              val eq_dec : equation -> equation -> bool
             end
            
            module TO : 
             sig 
              type t = equation
              
              val compare : equation -> equation -> Datatypes.comparison
              
              val eq_dec : equation -> equation -> bool
             end
           end
          
          val eq_dec : equation -> equation -> bool
          
          val lt_dec : equation -> equation -> bool
          
          val eqb : equation -> equation -> bool
         end
       end
      
      val flatten_e : enumeration -> elt list
      
      type coq_R_bal =
      | R_bal_0 of t * equation * t
      | R_bal_1 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_2 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_3 of t * equation * t * Z_as_Int.t * tree * equation * 
         tree * Z_as_Int.t * tree * equation * tree
      | R_bal_4 of t * equation * t
      | R_bal_5 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_6 of t * equation * t * Z_as_Int.t * tree * equation * tree
      | R_bal_7 of t * equation * t * Z_as_Int.t * tree * equation * 
         tree * Z_as_Int.t * tree * equation * tree
      | R_bal_8 of t * equation * t
      
      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * equation
         * tree * (t * elt) * coq_R_remove_min * t * elt
      
      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * elt
      
      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * elt
      
      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      
      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      
      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree * equation * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree * equation * tree
         * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end
    
    module E : 
     sig 
      type t = equation
      
      val compare : equation -> equation -> Datatypes.comparison
      
      val eq_dec : equation -> equation -> bool
     end
    
    type elt = equation
    
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
    
    val compare : t -> t -> Datatypes.comparison
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
   end
  
  type elt = equation
  
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
    val eqb : equation -> equation -> bool
   end
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  module E : 
   sig 
    type t = equation
    
    val compare : equation -> equation -> equation OrderedType.coq_Compare
    
    val eq_dec : equation -> equation -> bool
   end
  
  module Raw : 
   sig 
    type elt = equation
    
    type tree = MSet.Raw.tree =
    | Leaf
    | Node of Z_as_Int.t * tree * equation * tree
    
    val empty : tree
    
    val is_empty : tree -> bool
    
    val mem : equation -> tree -> bool
    
    val min_elt : tree -> elt option
    
    val max_elt : tree -> elt option
    
    val choose : tree -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1
    
    val elements_aux : equation list -> tree -> equation list
    
    val elements : tree -> equation list
    
    val rev_elements_aux : equation list -> tree -> equation list
    
    val rev_elements : tree -> equation list
    
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
      equation -> (enumeration -> Datatypes.comparison) -> enumeration ->
      Datatypes.comparison
    
    val compare_cont :
      tree -> (enumeration -> Datatypes.comparison) -> enumeration ->
      Datatypes.comparison
    
    val compare_end : enumeration -> Datatypes.comparison
    
    val compare : tree -> tree -> Datatypes.comparison
    
    val equal : tree -> tree -> bool
    
    val subsetl : (tree -> bool) -> equation -> tree -> bool
    
    val subsetr : (tree -> bool) -> equation -> tree -> bool
    
    val subset : tree -> tree -> bool
    
    type t = tree
    
    val height : t -> Z_as_Int.t
    
    val singleton : equation -> tree
    
    val create : t -> equation -> t -> tree
    
    val assert_false : t -> equation -> t -> tree
    
    val bal : t -> equation -> t -> tree
    
    val add : equation -> tree -> tree
    
    val join : tree -> elt -> t -> t
    
    val remove_min : tree -> elt -> t -> t * elt
    
    val merge : tree -> tree -> tree
    
    val remove : equation -> tree -> tree
    
    val concat : tree -> tree -> tree
    
    type triple = { t_left : t; t_in : bool; t_right : t }
    
    val t_left : triple -> t
    
    val t_in : triple -> bool
    
    val t_right : triple -> t
    
    val split : equation -> tree -> triple
    
    val inter : tree -> tree -> tree
    
    val diff : tree -> tree -> tree
    
    val union : tree -> tree -> tree
    
    val filter : (elt -> bool) -> tree -> tree
    
    val partition : (elt -> bool) -> t -> t * t
    
    val ltb_tree : equation -> tree -> bool
    
    val gtb_tree : equation -> tree -> bool
    
    val isok : tree -> bool
    
    module MX : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = equation
          
          val compare : equation -> equation -> Datatypes.comparison
          
          val eq_dec : equation -> equation -> bool
         end
        
        module TO : 
         sig 
          type t = equation
          
          val compare : equation -> equation -> Datatypes.comparison
          
          val eq_dec : equation -> equation -> bool
         end
       end
      
      val eq_dec : equation -> equation -> bool
      
      val lt_dec : equation -> equation -> bool
      
      val eqb : equation -> equation -> bool
     end
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Z_as_Int.t * tree * equation * tree
    | R_min_elt_2 of tree * Z_as_Int.t * tree * equation * tree * Z_as_Int.t
       * tree * equation * tree * elt option * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Z_as_Int.t * tree * equation * tree
    | R_max_elt_2 of tree * Z_as_Int.t * tree * equation * tree * Z_as_Int.t
       * tree * equation * tree * elt option * coq_R_max_elt
    
    module L : 
     sig 
      module MO : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
          
          module TO : 
           sig 
            type t = equation
            
            val compare : equation -> equation -> Datatypes.comparison
            
            val eq_dec : equation -> equation -> bool
           end
         end
        
        val eq_dec : equation -> equation -> bool
        
        val lt_dec : equation -> equation -> bool
        
        val eqb : equation -> equation -> bool
       end
     end
    
    val flatten_e : enumeration -> elt list
    
    type coq_R_bal =
    | R_bal_0 of t * equation * t
    | R_bal_1 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_2 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_3 of t * equation * t * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree
    | R_bal_4 of t * equation * t
    | R_bal_5 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_6 of t * equation * t * Z_as_Int.t * tree * equation * tree
    | R_bal_7 of t * equation * t * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree
    | R_bal_8 of t * equation * t
    
    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * equation * 
       tree * (t * elt) * coq_R_remove_min * t * elt
    
    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_merge_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * elt
    
    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_concat_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * elt
    
    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_inter_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    
    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_diff_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    
    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Z_as_Int.t * tree * equation * tree
    | R_union_2 of tree * tree * Z_as_Int.t * tree * equation * tree
       * Z_as_Int.t * tree * equation * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end
  
  val raw_mem_between : (elt -> bool) -> (elt -> bool) -> Raw.tree -> bool
  
  val mem_between : (elt -> bool) -> (elt -> bool) -> t -> bool
  
  val raw_elements_between :
    (elt -> bool) -> (elt -> bool) -> Raw.tree -> Raw.tree
  
  val elements_between : (elt -> bool) -> (elt -> bool) -> t -> t
  
  val raw_for_all_between :
    (elt -> bool) -> (elt -> bool) -> (elt -> bool) -> Raw.tree -> bool
  
  val for_all_between :
    (elt -> bool) -> (elt -> bool) -> (elt -> bool) -> t -> bool
  
  val raw_partition_between :
    (elt -> bool) -> (elt -> bool) -> Raw.tree -> Raw.tree * Raw.tree
  
  val partition_between : (elt -> bool) -> (elt -> bool) -> t -> t * t
 end

type eqs = { eqs1 : EqSet.t; eqs2 : EqSet2.t }

val eqs1 : eqs -> EqSet.t

val eqs2 : eqs -> EqSet2.t

val empty_eqs : eqs

val add_equation : equation -> eqs -> eqs

val remove_equation : equation -> eqs -> eqs

val select_reg_l : reg -> equation -> bool

val select_reg_h : reg -> equation -> bool

val reg_unconstrained : reg -> eqs -> bool

val select_loc_l : loc -> equation -> bool

val select_loc_h : loc -> equation -> bool

val loc_unconstrained : loc -> eqs -> bool

val reg_loc_unconstrained : reg -> loc -> eqs -> bool

val subst_reg : reg -> reg -> eqs -> eqs

val subst_reg_kind :
  reg -> equation_kind -> reg -> equation_kind -> eqs -> eqs

val subst_loc : loc -> loc -> eqs -> eqs option

val sel_type : equation_kind -> typ -> typ

val loc_type_compat : regenv -> loc -> eqs -> bool

val add_equations : reg list -> mreg list -> eqs -> eqs option

val add_equations_args :
  reg list -> typ list -> loc list -> eqs -> eqs option

val add_equations_res : reg -> typ option -> loc list -> eqs -> eqs option

val remove_equations_res : reg -> typ option -> loc list -> eqs -> eqs option

val add_equation_ros :
  (reg, ident) sum -> (mreg, ident) sum -> eqs -> eqs option

val can_undef : mreg list -> eqs -> bool

val can_undef_except : loc -> mreg list -> eqs -> bool

val no_caller_saves : eqs -> bool

val compat_left : reg -> loc -> eqs -> bool

val compat_left2 : reg -> loc -> loc -> eqs -> bool

val ros_compatible_tailcall : (mreg, ident) sum -> bool

val destroyed_by_move : loc -> loc -> mreg list

val well_typed_move : regenv -> loc -> eqs -> bool

val track_moves : regenv -> moves -> eqs -> eqs option

val transfer_use_def :
  reg list -> reg -> mreg list -> mreg -> mreg list -> eqs -> eqs option

val kind_first_word : equation_kind

val kind_second_word : equation_kind

val transfer_aux : coq_function -> regenv -> block_shape -> eqs -> eqs option

val transfer :
  coq_function -> regenv -> block_shape PTree.t -> LTL.node -> eqs res -> eqs
  res

module LEq : 
 sig 
  type t = eqs res
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
 end

module DS : 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    'a1 PTree.t -> ('a1 -> positive list) -> (positive -> L.t -> L.t) -> L.t
    PMap.t option
  
  val fixpoint_allnodes :
    'a1 PTree.t -> ('a1 -> positive list) -> (positive -> L.t -> L.t) -> L.t
    PMap.t option
 end

val successors_block_shape : block_shape -> LTL.node list

val analyze :
  coq_function -> regenv -> block_shape PTree.t -> DS.L.t PMap.t option

val compat_entry : reg list -> typ list -> loc list -> eqs -> bool

val check_entrypoints_aux :
  coq_function -> LTL.coq_function -> regenv -> eqs -> unit option

val check_entrypoints :
  coq_function -> LTL.coq_function -> regenv -> block_shape PTree.t -> LEq.t
  PMap.t -> unit res

val check_function : coq_function -> LTL.coq_function -> regenv -> unit res

val regalloc : coq_function -> LTL.coq_function res

val transf_function : coq_function -> LTL.coq_function res

val transf_fundef : fundef -> LTL.fundef res

val transf_program : program -> LTL.program res

