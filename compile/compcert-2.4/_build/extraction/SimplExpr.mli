open AST
open BinPos
open Clight
open Cop
open Csyntax
open Ctypes
open Datatypes
open Errors
open Integers
open Values

type generator = { gen_next : ident; gen_trail : (ident * coq_type) list }

val gen_next : generator -> ident

val gen_trail : generator -> (ident * coq_type) list

type 'a result =
| Err of errmsg
| Res of 'a * generator

type 'a mon = generator -> 'a result

val first_unused_ident : unit -> ident

val initial_generator : unit -> generator

val gensym : coq_type -> ident mon

val reset_trail : unit mon

val get_trail : (ident * coq_type) list mon

val makeseq_rec :
  Clight.statement -> Clight.statement list -> Clight.statement

val makeseq : Clight.statement list -> Clight.statement

val eval_simpl_expr : Clight.expr -> coq_val option

val makeif :
  Clight.expr -> Clight.statement -> Clight.statement -> Clight.statement

val transl_incrdecr : incr_or_decr -> Clight.expr -> coq_type -> Clight.expr

val chunk_for_volatile_type : coq_type -> memory_chunk option

val make_set : ident -> Clight.expr -> Clight.statement

val transl_valof :
  coq_type -> Clight.expr -> (Clight.statement list * Clight.expr) mon

val make_assign : Clight.expr -> Clight.expr -> Clight.statement

type set_destination =
| SDbase of coq_type * ident
| SDcons of coq_type * ident * set_destination

type destination =
| For_val
| For_effects
| For_set of set_destination

val dummy_expr : Clight.expr

val do_set : set_destination -> Clight.expr -> Clight.statement list

val finish :
  destination -> Clight.statement list -> Clight.expr -> Clight.statement
  list * Clight.expr

val sd_temp : set_destination -> ident

val sd_seqbool_val : ident -> coq_type -> set_destination

val sd_seqbool_set : coq_type -> set_destination -> set_destination

val transl_expr :
  destination -> expr -> (Clight.statement list * Clight.expr) mon

val transl_exprlist :
  exprlist -> (Clight.statement list * Clight.expr list) mon

val transl_expression : expr -> (Clight.statement * Clight.expr) mon

val transl_expr_stmt : expr -> Clight.statement mon

val transl_if :
  expr -> Clight.statement -> Clight.statement -> Clight.statement mon

val is_Sskip : statement -> bool

val transl_stmt : statement -> Clight.statement mon

val transl_lblstmt : labeled_statements -> Clight.labeled_statements mon

val transl_function : coq_function -> Clight.coq_function mon

val transl_fundef : fundef -> Clight.fundef mon

val transl_globdefs :
  (ident * (fundef, coq_type) globdef) list -> generator ->
  (ident * (Clight.fundef, coq_type) globdef) list res

val transl_program : program -> Clight.program res

