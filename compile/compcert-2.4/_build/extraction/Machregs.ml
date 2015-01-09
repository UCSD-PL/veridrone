open AST
open BinNums
open Coqlib
open Op

type mreg =
| AX
| BX
| CX
| DX
| SI
| DI
| BP
| X0
| X1
| X2
| X3
| X4
| X5
| X6
| X7
| FP0

(** val mreg_eq : mreg -> mreg -> bool **)

let mreg_eq r1 r2 =
  match r1 with
  | AX ->
    (match r2 with
     | AX -> true
     | _ -> false)
  | BX ->
    (match r2 with
     | BX -> true
     | _ -> false)
  | CX ->
    (match r2 with
     | CX -> true
     | _ -> false)
  | DX ->
    (match r2 with
     | DX -> true
     | _ -> false)
  | SI ->
    (match r2 with
     | SI -> true
     | _ -> false)
  | DI ->
    (match r2 with
     | DI -> true
     | _ -> false)
  | BP ->
    (match r2 with
     | BP -> true
     | _ -> false)
  | X0 ->
    (match r2 with
     | X0 -> true
     | _ -> false)
  | X1 ->
    (match r2 with
     | X1 -> true
     | _ -> false)
  | X2 ->
    (match r2 with
     | X2 -> true
     | _ -> false)
  | X3 ->
    (match r2 with
     | X3 -> true
     | _ -> false)
  | X4 ->
    (match r2 with
     | X4 -> true
     | _ -> false)
  | X5 ->
    (match r2 with
     | X5 -> true
     | _ -> false)
  | X6 ->
    (match r2 with
     | X6 -> true
     | _ -> false)
  | X7 ->
    (match r2 with
     | X7 -> true
     | _ -> false)
  | FP0 ->
    (match r2 with
     | FP0 -> true
     | _ -> false)

(** val mreg_type : mreg -> typ **)

let mreg_type = function
| AX -> Tany32
| BX -> Tany32
| CX -> Tany32
| DX -> Tany32
| SI -> Tany32
| DI -> Tany32
| BP -> Tany32
| _ -> Tany64

module IndexedMreg = 
 struct 
  type t = mreg
  
  (** val eq : mreg -> mreg -> bool **)
  
  let eq =
    mreg_eq
  
  (** val index : mreg -> positive **)
  
  let index = function
  | AX -> Coq_xH
  | BX -> Coq_xO Coq_xH
  | CX -> Coq_xI Coq_xH
  | DX -> Coq_xO (Coq_xO Coq_xH)
  | SI -> Coq_xI (Coq_xO Coq_xH)
  | DI -> Coq_xO (Coq_xI Coq_xH)
  | BP -> Coq_xI (Coq_xI Coq_xH)
  | X0 -> Coq_xO (Coq_xO (Coq_xO Coq_xH))
  | X1 -> Coq_xI (Coq_xO (Coq_xO Coq_xH))
  | X2 -> Coq_xO (Coq_xI (Coq_xO Coq_xH))
  | X3 -> Coq_xI (Coq_xI (Coq_xO Coq_xH))
  | X4 -> Coq_xO (Coq_xO (Coq_xI Coq_xH))
  | X5 -> Coq_xI (Coq_xO (Coq_xI Coq_xH))
  | X6 -> Coq_xO (Coq_xI (Coq_xI Coq_xH))
  | X7 -> Coq_xI (Coq_xI (Coq_xI Coq_xH))
  | FP0 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
 end

(** val is_stack_reg : mreg -> bool **)

let is_stack_reg = function
| FP0 -> true
| _ -> false

(** val destroyed_by_op : operation -> mreg list **)

let destroyed_by_op = function
| Ocast8signed -> AX :: []
| Ocast8unsigned -> AX :: []
| Ocast16signed -> AX :: []
| Ocast16unsigned -> AX :: []
| Omulhs -> AX :: (DX :: [])
| Omulhu -> AX :: (DX :: [])
| Odiv -> AX :: (DX :: [])
| Odivu -> AX :: (DX :: [])
| Omod -> AX :: (DX :: [])
| Omodu -> AX :: (DX :: [])
| Oshrximm i -> CX :: []
| Ocmp c -> AX :: (CX :: [])
| _ -> []

(** val destroyed_by_load : memory_chunk -> addressing -> mreg list **)

let destroyed_by_load chunk addr =
  []

(** val destroyed_by_store : memory_chunk -> addressing -> mreg list **)

let destroyed_by_store chunk addr =
  match chunk with
  | Mint8signed -> AX :: (CX :: [])
  | Mint8unsigned -> AX :: (CX :: [])
  | _ -> []

(** val destroyed_by_cond : condition -> mreg list **)

let destroyed_by_cond cond =
  []

(** val destroyed_by_jumptable : mreg list **)

let destroyed_by_jumptable =
  []

(** val builtin_write16_reversed : ident **)

let builtin_write16_reversed =
  ident_of_string
    ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('w'::('r'::('i'::('t'::('e'::('1'::('6'::('_'::('r'::('e'::('v'::('e'::('r'::('s'::('e'::('d'::[]))))))))))))))))))))))))))

(** val builtin_write32_reversed : ident **)

let builtin_write32_reversed =
  ident_of_string
    ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('w'::('r'::('i'::('t'::('e'::('3'::('2'::('_'::('r'::('e'::('v'::('e'::('r'::('s'::('e'::('d'::[]))))))))))))))))))))))))))

(** val destroyed_by_builtin : external_function -> mreg list **)

let destroyed_by_builtin = function
| EF_builtin (id, sg) ->
  if (||) ((fun x -> x) (ident_eq id builtin_write16_reversed))
       ((fun x -> x) (ident_eq id builtin_write32_reversed))
  then CX :: (DX :: [])
  else []
| EF_vstore chunk ->
  (match chunk with
   | Mint8signed -> AX :: (CX :: [])
   | Mint8unsigned -> AX :: (CX :: [])
   | _ -> [])
| EF_vstore_global (chunk, id, ofs) ->
  (match chunk with
   | Mint8signed -> AX :: []
   | Mint8unsigned -> AX :: []
   | _ -> [])
| EF_memcpy (sz, al) ->
  if zle sz (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  then CX :: (X7 :: [])
  else CX :: (SI :: (DI :: []))
| _ -> []

(** val destroyed_at_function_entry : mreg list **)

let destroyed_at_function_entry =
  DX :: (FP0 :: [])

(** val destroyed_by_setstack : typ -> mreg list **)

let destroyed_by_setstack = function
| Tfloat -> FP0 :: []
| Tsingle -> FP0 :: []
| _ -> []

(** val temp_for_parent_frame : mreg **)

let temp_for_parent_frame =
  DX

(** val mregs_for_operation : operation -> mreg option list * mreg option **)

let mregs_for_operation = function
| Omulhs -> (((Some AX) :: (None :: [])), (Some DX))
| Omulhu -> (((Some AX) :: (None :: [])), (Some DX))
| Odiv -> (((Some AX) :: ((Some CX) :: [])), (Some AX))
| Odivu -> (((Some AX) :: ((Some CX) :: [])), (Some AX))
| Omod -> (((Some AX) :: ((Some CX) :: [])), (Some DX))
| Omodu -> (((Some AX) :: ((Some CX) :: [])), (Some DX))
| Oshl -> ((None :: ((Some CX) :: [])), None)
| Oshr -> ((None :: ((Some CX) :: [])), None)
| Oshrximm i -> (((Some AX) :: []), (Some AX))
| Oshru -> ((None :: ((Some CX) :: [])), None)
| _ -> ([], None)

(** val builtin_negl : ident **)

let builtin_negl =
  ident_of_string
    ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('n'::('e'::('g'::('l'::[]))))))))))))))

(** val builtin_addl : ident **)

let builtin_addl =
  ident_of_string
    ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('a'::('d'::('d'::('l'::[]))))))))))))))

(** val builtin_subl : ident **)

let builtin_subl =
  ident_of_string
    ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('s'::('u'::('b'::('l'::[]))))))))))))))

(** val builtin_mull : ident **)

let builtin_mull =
  ident_of_string
    ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('m'::('u'::('l'::('l'::[]))))))))))))))

(** val mregs_for_builtin :
    external_function -> mreg option list * mreg option list **)

let mregs_for_builtin = function
| EF_builtin (id, sg) ->
  if ident_eq id builtin_negl
  then (((Some DX) :: ((Some AX) :: [])), ((Some DX) :: ((Some AX) :: [])))
  else if (||) ((fun x -> x) (ident_eq id builtin_addl))
            ((fun x -> x) (ident_eq id builtin_subl))
       then (((Some DX) :: ((Some AX) :: ((Some CX) :: ((Some BX) :: [])))),
              ((Some DX) :: ((Some AX) :: [])))
       else if ident_eq id builtin_mull
            then (((Some AX) :: ((Some DX) :: [])), ((Some DX) :: ((Some
                   AX) :: [])))
            else ([], [])
| EF_memcpy (sz, al) ->
  if zle sz (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  then (((Some AX) :: ((Some DX) :: [])), [])
  else (((Some DI) :: ((Some SI) :: [])), [])
| _ -> ([], [])

(** val two_address_op : operation -> bool **)

let two_address_op = function
| Omove -> false
| Ointconst i -> false
| Ofloatconst f -> false
| Osingleconst f -> false
| Oindirectsymbol i -> false
| Ocast8signed -> false
| Ocast8unsigned -> false
| Ocast16signed -> false
| Ocast16unsigned -> false
| Omulhs -> false
| Omulhu -> false
| Odiv -> false
| Odivu -> false
| Omod -> false
| Omodu -> false
| Oshrximm i -> false
| Olea addr -> false
| Osingleoffloat -> false
| Ofloatofsingle -> false
| Ointoffloat -> false
| Ofloatofint -> false
| Ointofsingle -> false
| Osingleofint -> false
| Omakelong -> false
| Olowlong -> false
| Ohighlong -> false
| Ocmp c -> false
| _ -> true

