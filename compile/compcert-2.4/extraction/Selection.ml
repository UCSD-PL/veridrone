open AST
open BinNums
open Cminor
open CminorSel
open Datatypes
open Errors
open Globalenvs
open Integers
open Op
open SelectDiv
open SelectLong
open SelectOp
open Switch

(** val condexpr_of_expr : expr -> condexpr **)

let rec condexpr_of_expr e = match e with
| Eop (o, el) ->
  (match o with
   | Ocmp c -> CEcond (c, el)
   | _ -> CEcond ((Ccompuimm (Cne, Int.zero)), (Econs (e, Enil))))
| Econdition (a, b, c) ->
  CEcondition (a, (condexpr_of_expr b), (condexpr_of_expr c))
| Elet (a, b) -> CElet (a, (condexpr_of_expr b))
| _ -> CEcond ((Ccompuimm (Cne, Int.zero)), (Econs (e, Enil)))

(** val load : memory_chunk -> expr -> expr **)

let load chunk e1 =
  let (mode, args) = addressing chunk e1 in Eload (chunk, mode, args)

(** val store : memory_chunk -> expr -> expr -> stmt **)

let store chunk e1 e2 =
  let (mode, args) = addressing chunk e1 in Sstore (chunk, mode, args, e2)

(** val sel_constant : constant -> expr **)

let sel_constant = function
| Cminor.Ointconst n -> Eop ((Ointconst n), Enil)
| Cminor.Ofloatconst f -> Eop ((Ofloatconst f), Enil)
| Cminor.Osingleconst f -> Eop ((Osingleconst f), Enil)
| Olongconst n -> longconst n
| Oaddrsymbol (id, ofs) -> addrsymbol id ofs
| Oaddrstack ofs -> addrstack ofs

(** val sel_unop : helper_functions -> unary_operation -> expr -> expr **)

let sel_unop hf op arg =
  match op with
  | Cminor.Ocast8unsigned -> cast8unsigned arg
  | Cminor.Ocast8signed -> cast8signed arg
  | Cminor.Ocast16unsigned -> cast16unsigned arg
  | Cminor.Ocast16signed -> cast16signed arg
  | Onegint -> negint arg
  | Onotint -> notint arg
  | Cminor.Onegf -> negf arg
  | Cminor.Oabsf -> absf arg
  | Cminor.Onegfs -> negfs arg
  | Cminor.Oabsfs -> absfs arg
  | Cminor.Osingleoffloat -> singleoffloat arg
  | Cminor.Ofloatofsingle -> floatofsingle arg
  | Cminor.Ointoffloat -> intoffloat arg
  | Ointuoffloat -> intuoffloat arg
  | Cminor.Ofloatofint -> floatofint arg
  | Ofloatofintu -> floatofintu arg
  | Cminor.Ointofsingle -> intofsingle arg
  | Ointuofsingle -> intuofsingle arg
  | Cminor.Osingleofint -> singleofint arg
  | Osingleofintu -> singleofintu arg
  | Onegl -> negl hf arg
  | Onotl -> notl arg
  | Ointoflong -> intoflong arg
  | Olongofint -> longofint arg
  | Olongofintu -> longofintu arg
  | Olongoffloat -> longoffloat hf arg
  | Olonguoffloat -> longuoffloat hf arg
  | Ofloatoflong -> floatoflong hf arg
  | Ofloatoflongu -> floatoflongu hf arg
  | Olongofsingle -> longofsingle hf arg
  | Olonguofsingle -> longuofsingle hf arg
  | Osingleoflong -> singleoflong hf arg
  | Osingleoflongu -> singleoflongu hf arg

(** val sel_binop :
    helper_functions -> binary_operation -> expr -> expr -> expr **)

let sel_binop hf op arg1 arg2 =
  match op with
  | Oadd -> add arg1 arg2
  | Cminor.Osub -> sub arg1 arg2
  | Cminor.Omul -> mul arg1 arg2
  | Cminor.Odiv -> divs arg1 arg2
  | Cminor.Odivu -> divu arg1 arg2
  | Cminor.Omod -> mods arg1 arg2
  | Cminor.Omodu -> modu arg1 arg2
  | Cminor.Oand -> coq_and arg1 arg2
  | Cminor.Oor -> coq_or arg1 arg2
  | Cminor.Oxor -> xor arg1 arg2
  | Cminor.Oshl -> shl arg1 arg2
  | Cminor.Oshr -> shr arg1 arg2
  | Cminor.Oshru -> shru arg1 arg2
  | Cminor.Oaddf -> addf arg1 arg2
  | Cminor.Osubf -> subf arg1 arg2
  | Cminor.Omulf -> mulf arg1 arg2
  | Cminor.Odivf -> divf arg1 arg2
  | Cminor.Oaddfs -> addfs arg1 arg2
  | Cminor.Osubfs -> subfs arg1 arg2
  | Cminor.Omulfs -> mulfs arg1 arg2
  | Cminor.Odivfs -> divfs arg1 arg2
  | Oaddl -> addl hf arg1 arg2
  | Osubl -> subl hf arg1 arg2
  | Omull -> mull hf arg1 arg2
  | Odivl -> divl hf arg1 arg2
  | Odivlu -> divlu hf arg1 arg2
  | Omodl -> modl hf arg1 arg2
  | Omodlu -> modlu hf arg1 arg2
  | Oandl -> andl arg1 arg2
  | Oorl -> orl arg1 arg2
  | Oxorl -> xorl arg1 arg2
  | Oshll -> shll hf arg1 arg2
  | Oshrl -> shrl hf arg1 arg2
  | Oshrlu -> shrlu hf arg1 arg2
  | Cminor.Ocmp c -> comp c arg1 arg2
  | Ocmpu c -> compu c arg1 arg2
  | Ocmpf c -> compf c arg1 arg2
  | Ocmpfs c -> compfs c arg1 arg2
  | Ocmpl c -> cmpl c arg1 arg2
  | Ocmplu c -> cmplu c arg1 arg2

(** val sel_expr : helper_functions -> Cminor.expr -> expr **)

let rec sel_expr hf = function
| Cminor.Evar id -> Evar id
| Econst cst -> sel_constant cst
| Eunop (op, arg) -> sel_unop hf op (sel_expr hf arg)
| Ebinop (op, arg1, arg2) ->
  sel_binop hf op (sel_expr hf arg1) (sel_expr hf arg2)
| Cminor.Eload (chunk, addr) -> load chunk (sel_expr hf addr)

(** val sel_exprlist : helper_functions -> Cminor.expr list -> exprlist **)

let rec sel_exprlist hf = function
| [] -> Enil
| a :: bl -> Econs ((sel_expr hf a), (sel_exprlist hf bl))

type call_kind =
| Call_default
| Call_imm of ident
| Call_builtin of external_function

(** val expr_is_addrof_ident : Cminor.expr -> ident option **)

let expr_is_addrof_ident = function
| Econst c ->
  (match c with
   | Oaddrsymbol (id, ofs) -> if Int.eq ofs Int.zero then Some id else None
   | _ -> None)
| _ -> None

(** val classify_call : genv -> Cminor.expr -> call_kind **)

let classify_call ge e =
  match expr_is_addrof_ident e with
  | Some id ->
    (match Genv.find_symbol ge id with
     | Some b ->
       (match Genv.find_funct_ptr ge b with
        | Some f ->
          (match f with
           | Internal f0 -> Call_imm id
           | External ef ->
             if ef_inline ef then Call_builtin ef else Call_imm id)
        | None -> Call_imm id)
     | None -> Call_imm id)
  | None -> Call_default

(** val compile_switch : coq_Z -> nat -> table -> comptree **)

let compile_switch = Switchaux.compile_switch

(** val sel_switch :
    (expr -> coq_Z -> expr) -> (expr -> coq_Z -> expr) -> (expr -> coq_Z ->
    expr) -> (expr -> expr) -> nat -> comptree -> exitexpr **)

let rec sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg = function
| CTaction act -> XEexit act
| CTifeq (key, act, t') ->
  XEcondition ((condexpr_of_expr (make_cmp_eq (Eletvar arg) key)), (XEexit
    act), (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t'))
| CTiflt (key, t1, t2) ->
  XEcondition ((condexpr_of_expr (make_cmp_ltu (Eletvar arg) key)),
    (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t1),
    (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t2))
| CTjumptable (ofs, sz, tbl, t') ->
  XElet ((make_sub (Eletvar arg) ofs), (XEcondition
    ((condexpr_of_expr (make_cmp_ltu (Eletvar O) sz)), (XEjumptable
    ((make_to_int (Eletvar O)), tbl)),
    (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int (S arg) t'))))

(** val sel_switch_int : nat -> comptree -> exitexpr **)

let sel_switch_int =
  sel_switch (fun arg n ->
    comp Ceq arg (Eop ((Ointconst (Int.repr n)), Enil))) (fun arg n ->
    compu Clt arg (Eop ((Ointconst (Int.repr n)), Enil))) (fun arg ofs ->
    sub arg (Eop ((Ointconst (Int.repr ofs)), Enil))) (fun arg -> arg)

(** val sel_switch_long : helper_functions -> nat -> comptree -> exitexpr **)

let sel_switch_long hf =
  sel_switch (fun arg n -> cmpl Ceq arg (longconst (Int64.repr n)))
    (fun arg n -> cmplu Clt arg (longconst (Int64.repr n))) (fun arg ofs ->
    subl hf arg (longconst (Int64.repr ofs))) lowlong

(** val sel_stmt : helper_functions -> genv -> Cminor.stmt -> stmt res **)

let rec sel_stmt hf ge = function
| Cminor.Sskip -> OK Sskip
| Cminor.Sassign (id, e) -> OK (Sassign (id, (sel_expr hf e)))
| Cminor.Sstore (chunk, addr, rhs) ->
  OK (store chunk (sel_expr hf addr) (sel_expr hf rhs))
| Cminor.Scall (optid, sg, fn, args) ->
  OK
    (match classify_call ge fn with
     | Call_default ->
       Scall (optid, sg, (Coq_inl (sel_expr hf fn)), (sel_exprlist hf args))
     | Call_imm id -> Scall (optid, sg, (Coq_inr id), (sel_exprlist hf args))
     | Call_builtin ef -> Sbuiltin (optid, ef, (sel_exprlist hf args)))
| Cminor.Stailcall (sg, fn, args) ->
  OK
    (match classify_call ge fn with
     | Call_imm id -> Stailcall (sg, (Coq_inr id), (sel_exprlist hf args))
     | _ ->
       Stailcall (sg, (Coq_inl (sel_expr hf fn)), (sel_exprlist hf args)))
| Cminor.Sbuiltin (optid, ef, args) ->
  OK (Sbuiltin (optid, ef, (sel_exprlist hf args)))
| Cminor.Sseq (s1, s2) ->
  (match sel_stmt hf ge s1 with
   | OK x ->
     (match sel_stmt hf ge s2 with
      | OK x0 -> OK (Sseq (x, x0))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Cminor.Sifthenelse (e, ifso, ifnot) ->
  (match sel_stmt hf ge ifso with
   | OK x ->
     (match sel_stmt hf ge ifnot with
      | OK x0 -> OK (Sifthenelse ((condexpr_of_expr (sel_expr hf e)), x, x0))
      | Error msg0 -> Error msg0)
   | Error msg0 -> Error msg0)
| Cminor.Sloop body ->
  (match sel_stmt hf ge body with
   | OK x -> OK (Sloop x)
   | Error msg0 -> Error msg0)
| Cminor.Sblock body ->
  (match sel_stmt hf ge body with
   | OK x -> OK (Sblock x)
   | Error msg0 -> Error msg0)
| Cminor.Sexit n -> OK (Sexit n)
| Cminor.Sswitch (b, e, cases, dfl) ->
  if b
  then let t = compile_switch Int64.modulus dfl cases in
       if validate_switch Int64.modulus dfl cases t
       then OK (Sswitch (XElet ((sel_expr hf e), (sel_switch_long hf O t))))
       else Error
              (msg
                ('S'::('e'::('l'::('e'::('c'::('t'::('i'::('o'::('n'::(':'::(' '::('b'::('a'::('d'::(' '::('s'::('w'::('i'::('t'::('c'::('h'::(' '::('('::('l'::('o'::('n'::('g'::(')'::[])))))))))))))))))))))))))))))
  else let t = compile_switch Int.modulus dfl cases in
       if validate_switch Int.modulus dfl cases t
       then OK (Sswitch (XElet ((sel_expr hf e), (sel_switch_int O t))))
       else Error
              (msg
                ('S'::('e'::('l'::('e'::('c'::('t'::('i'::('o'::('n'::(':'::(' '::('b'::('a'::('d'::(' '::('s'::('w'::('i'::('t'::('c'::('h'::(' '::('('::('i'::('n'::('t'::(')'::[]))))))))))))))))))))))))))))
| Cminor.Sreturn o ->
  (match o with
   | Some e -> OK (Sreturn (Some (sel_expr hf e)))
   | None -> OK (Sreturn None))
| Cminor.Slabel (lbl, body) ->
  (match sel_stmt hf ge body with
   | OK x -> OK (Slabel (lbl, x))
   | Error msg0 -> Error msg0)
| Cminor.Sgoto lbl -> OK (Sgoto lbl)

(** val sel_function :
    helper_functions -> genv -> Cminor.coq_function -> coq_function res **)

let sel_function hf ge f =
  match sel_stmt hf ge f.Cminor.fn_body with
  | OK x ->
    OK { fn_sig = f.Cminor.fn_sig; fn_params = f.Cminor.fn_params; fn_vars =
      f.Cminor.fn_vars; fn_stackspace = f.Cminor.fn_stackspace; fn_body = x }
  | Error msg0 -> Error msg0

(** val sel_fundef :
    helper_functions -> genv -> Cminor.fundef -> fundef res **)

let sel_fundef hf ge f =
  transf_partial_fundef (sel_function hf ge) f

(** val sel_program : Cminor.program -> program res **)

let sel_program p =
  let ge = Genv.globalenv p in
  (match get_helpers ge with
   | OK x -> transform_partial_program (sel_fundef x ge) p
   | Error msg0 -> Error msg0)

