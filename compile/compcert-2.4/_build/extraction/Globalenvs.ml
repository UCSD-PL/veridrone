open AST
open BinInt
open BinNums
open BinPos
open Coqlib
open Datatypes
open Integers
open List0
open Maps
open Memory
open Memtype
open Values

(** val store_zeros :
    Mem.mem -> block -> coq_Z -> coq_Z -> Mem.mem option **)

let rec store_zeros m b p n =
  if zle n Z0
  then Some m
  else (match Mem.store Mint8unsigned m b p coq_Vzero with
        | Some m' ->
          store_zeros m' b (Z.add p (Zpos Coq_xH)) (Z.sub n (Zpos Coq_xH))
        | None -> None)

module Genv = 
 struct 
  type ('f, 'v) t = { genv_symb : block PTree.t; genv_funs : 'f PTree.t;
                      genv_vars : 'v globvar PTree.t; genv_next : block }
  
  (** val genv_symb : ('a1, 'a2) t -> block PTree.t **)
  
  let genv_symb x = x.genv_symb
  
  (** val genv_funs : ('a1, 'a2) t -> 'a1 PTree.t **)
  
  let genv_funs x = x.genv_funs
  
  (** val genv_vars : ('a1, 'a2) t -> 'a2 globvar PTree.t **)
  
  let genv_vars x = x.genv_vars
  
  (** val genv_next : ('a1, 'a2) t -> block **)
  
  let genv_next x = x.genv_next
  
  (** val find_symbol : ('a1, 'a2) t -> ident -> block option **)
  
  let find_symbol ge id =
    PTree.get id ge.genv_symb
  
  (** val symbol_address : ('a1, 'a2) t -> ident -> Int.int -> coq_val **)
  
  let symbol_address ge id ofs =
    match find_symbol ge id with
    | Some b -> Vptr (b, ofs)
    | None -> Vundef
  
  (** val find_funct_ptr : ('a1, 'a2) t -> block -> 'a1 option **)
  
  let find_funct_ptr ge b =
    PTree.get b ge.genv_funs
  
  (** val find_funct : ('a1, 'a2) t -> coq_val -> 'a1 option **)
  
  let find_funct ge = function
  | Vptr (b, ofs) ->
    if Int.eq_dec ofs Int.zero then find_funct_ptr ge b else None
  | _ -> None
  
  (** val invert_symbol : ('a1, 'a2) t -> block -> ident option **)
  
  let invert_symbol ge b =
    PTree.fold (fun res id b' -> if eq_block b b' then Some id else res)
      ge.genv_symb None
  
  (** val find_var_info : ('a1, 'a2) t -> block -> 'a2 globvar option **)
  
  let find_var_info ge b =
    PTree.get b ge.genv_vars
  
  (** val add_global :
      ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) -> ('a1, 'a2) t **)
  
  let add_global ge idg =
    { genv_symb = (PTree.set (fst idg) ge.genv_next ge.genv_symb);
      genv_funs =
      (let filtered_var = snd idg in
       match filtered_var with
       | Gfun f -> PTree.set ge.genv_next f ge.genv_funs
       | Gvar v -> ge.genv_funs); genv_vars =
      (let filtered_var = snd idg in
       match filtered_var with
       | Gfun f -> ge.genv_vars
       | Gvar v -> PTree.set ge.genv_next v ge.genv_vars); genv_next =
      (Pos.succ ge.genv_next) }
  
  (** val add_globals :
      ('a1, 'a2) t -> (ident * ('a1, 'a2) globdef) list -> ('a1, 'a2) t **)
  
  let add_globals ge gl =
    fold_left add_global gl ge
  
  (** val empty_genv : ('a1, 'a2) t **)
  
  let empty_genv =
    { genv_symb = PTree.empty; genv_funs = PTree.empty; genv_vars =
      PTree.empty; genv_next = Coq_xH }
  
  (** val globalenv : ('a1, 'a2) program -> ('a1, 'a2) t **)
  
  let globalenv p =
    add_globals empty_genv p.prog_defs
  
  (** val advance_next :
      (ident * ('a1, 'a2) globdef) list -> positive -> positive **)
  
  let advance_next gl x =
    fold_left (fun n g -> Pos.succ n) gl x
  
  (** val init_data_size : init_data -> coq_Z **)
  
  let init_data_size = function
  | Init_int8 i0 -> Zpos Coq_xH
  | Init_int16 i0 -> Zpos (Coq_xO Coq_xH)
  | Init_int64 i0 -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
  | Init_float64 f -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
  | Init_space n -> Z.max n Z0
  | _ -> Zpos (Coq_xO (Coq_xO Coq_xH))
  
  (** val store_init_data :
      ('a1, 'a2) t -> Mem.mem -> block -> coq_Z -> init_data -> Mem.mem
      option **)
  
  let store_init_data ge m b p = function
  | Init_int8 n -> Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n -> Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n -> Mem.store Mint32 m b p (Vint n)
  | Init_int64 n -> Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n -> Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n -> Mem.store Mfloat64 m b p (Vfloat n)
  | Init_space n -> Some m
  | Init_addrof (symb, ofs) ->
    (match find_symbol ge symb with
     | Some b' -> Mem.store Mint32 m b p (Vptr (b', ofs))
     | None -> None)
  
  (** val store_init_data_list :
      ('a1, 'a2) t -> Mem.mem -> block -> coq_Z -> init_data list -> Mem.mem
      option **)
  
  let rec store_init_data_list ge m b p = function
  | [] -> Some m
  | id :: idl' ->
    (match store_init_data ge m b p id with
     | Some m' ->
       store_init_data_list ge m' b (Z.add p (init_data_size id)) idl'
     | None -> None)
  
  (** val init_data_list_size : init_data list -> coq_Z **)
  
  let rec init_data_list_size = function
  | [] -> Z0
  | i :: il' -> Z.add (init_data_size i) (init_data_list_size il')
  
  (** val perm_globvar : 'a1 globvar -> permission **)
  
  let perm_globvar gv =
    if gv.gvar_volatile
    then Nonempty
    else if gv.gvar_readonly then Readable else Writable
  
  (** val alloc_global :
      ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) -> Mem.mem
      option **)
  
  let alloc_global ge m = function
  | (id, g) ->
    (match g with
     | Gfun f ->
       let (m1, b) = Mem.alloc m Z0 (Zpos Coq_xH) in
       Mem.drop_perm m1 b Z0 (Zpos Coq_xH) Nonempty
     | Gvar v ->
       let init = v.gvar_init in
       let sz = init_data_list_size init in
       let (m1, b) = Mem.alloc m Z0 sz in
       (match store_zeros m1 b Z0 sz with
        | Some m2 ->
          (match store_init_data_list ge m2 b Z0 init with
           | Some m3 -> Mem.drop_perm m3 b Z0 sz (perm_globvar v)
           | None -> None)
        | None -> None))
  
  (** val alloc_globals :
      ('a1, 'a2) t -> Mem.mem -> (ident * ('a1, 'a2) globdef) list -> Mem.mem
      option **)
  
  let rec alloc_globals ge m = function
  | [] -> Some m
  | g :: gl' ->
    (match alloc_global ge m g with
     | Some m' -> alloc_globals ge m' gl'
     | None -> None)
  
  (** val init_mem : ('a1, 'a2) program -> Mem.mem option **)
  
  let init_mem p =
    alloc_globals (globalenv p) Mem.empty p.prog_defs
 end

