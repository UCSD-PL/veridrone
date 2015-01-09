open AST
open BinNums
open Cop
open Ctypes
open Datatypes
open Integers
open List0
open Values

type expr =
| Eval of coq_val * coq_type
| Evar of ident * coq_type
| Efield of expr * ident * coq_type
| Evalof of expr * coq_type
| Ederef of expr * coq_type
| Eaddrof of expr * coq_type
| Eunop of unary_operation * expr * coq_type
| Ebinop of binary_operation * expr * expr * coq_type
| Ecast of expr * coq_type
| Eseqand of expr * expr * coq_type
| Eseqor of expr * expr * coq_type
| Econdition of expr * expr * expr * coq_type
| Esizeof of coq_type * coq_type
| Ealignof of coq_type * coq_type
| Eassign of expr * expr * coq_type
| Eassignop of binary_operation * expr * expr * coq_type * coq_type
| Epostincr of incr_or_decr * expr * coq_type
| Ecomma of expr * expr * coq_type
| Ecall of expr * exprlist * coq_type
| Ebuiltin of external_function * typelist * exprlist * coq_type
| Eloc of block * Int.int * coq_type
| Eparen of expr * coq_type
and exprlist =
| Enil
| Econs of expr * exprlist

(** val coq_Eindex : expr -> expr -> coq_type -> expr **)

let coq_Eindex r1 r2 ty =
  Ederef ((Ebinop (Oadd, r1, r2, (Tpointer (ty, noattr)))), ty)

(** val coq_Epreincr : incr_or_decr -> expr -> coq_type -> expr **)

let coq_Epreincr id l ty =
  Eassignop
    ((match id with
      | Incr -> Oadd
      | Decr -> Osub), l, (Eval ((Vint Int.one), type_int32s)),
    (typeconv ty), ty)

(** val typeof : expr -> coq_type **)

let typeof = function
| Eval (v, ty) -> ty
| Evar (x, ty) -> ty
| Efield (l, f, ty) -> ty
| Evalof (l, ty) -> ty
| Ederef (r, ty) -> ty
| Eaddrof (l, ty) -> ty
| Eunop (op, r, ty) -> ty
| Ebinop (op, r1, r2, ty) -> ty
| Ecast (r, ty) -> ty
| Eseqand (r1, r2, ty) -> ty
| Eseqor (r1, r2, ty) -> ty
| Econdition (r1, r2, r3, ty) -> ty
| Esizeof (ty', ty) -> ty
| Ealignof (ty', ty) -> ty
| Eassign (l, r, ty) -> ty
| Eassignop (op, l, r, tyres, ty) -> ty
| Epostincr (id, l, ty) -> ty
| Ecomma (r1, r2, ty) -> ty
| Ecall (r1, rargs, ty) -> ty
| Ebuiltin (ef, tyargs, rargs, ty) -> ty
| Eloc (b, ofs, ty) -> ty
| Eparen (r, ty) -> ty

type label = ident

type statement =
| Sskip
| Sdo of expr
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Swhile of expr * statement
| Sdowhile of expr * statement
| Sfor of statement * expr * statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of coq_Z option * statement * labeled_statements

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list; fn_body : statement }

(** val fn_return : coq_function -> coq_type **)

let fn_return x = x.fn_return

(** val fn_callconv : coq_function -> calling_convention **)

let fn_callconv x = x.fn_callconv

(** val fn_params : coq_function -> (ident * coq_type) list **)

let fn_params x = x.fn_params

(** val fn_vars : coq_function -> (ident * coq_type) list **)

let fn_vars x = x.fn_vars

(** val fn_body : coq_function -> statement **)

let fn_body x = x.fn_body

(** val var_names : (ident * coq_type) list -> ident list **)

let var_names vars =
  map fst vars

type fundef =
| Internal of coq_function
| External of external_function * typelist * coq_type * calling_convention

(** val type_of_function : coq_function -> coq_type **)

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)

(** val type_of_fundef : fundef -> coq_type **)

let type_of_fundef = function
| Internal fd -> type_of_function fd
| External (id, args, res, cc) -> Tfunction (args, res, cc)

type program = (fundef, coq_type) AST.program

