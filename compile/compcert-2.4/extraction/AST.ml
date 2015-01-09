open BinNums
open Bool
open Coqlib
open Errors
open Floats
open Integers
open List0

type ident = positive

(** val ident_eq : positive -> positive -> bool **)

let ident_eq =
  peq

(** val ident_of_string : char list -> ident **)

let ident_of_string = fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

(** val typ_eq : typ -> typ -> bool **)

let typ_eq t1 t2 =
  match t1 with
  | Tint ->
    (match t2 with
     | Tint -> true
     | _ -> false)
  | Tfloat ->
    (match t2 with
     | Tfloat -> true
     | _ -> false)
  | Tlong ->
    (match t2 with
     | Tlong -> true
     | _ -> false)
  | Tsingle ->
    (match t2 with
     | Tsingle -> true
     | _ -> false)
  | Tany32 ->
    (match t2 with
     | Tany32 -> true
     | _ -> false)
  | Tany64 ->
    (match t2 with
     | Tany64 -> true
     | _ -> false)

(** val opt_typ_eq : typ option -> typ option -> bool **)

let opt_typ_eq =
  option_eq typ_eq

(** val list_typ_eq : typ list -> typ list -> bool **)

let list_typ_eq =
  list_eq_dec typ_eq

(** val subtype : typ -> typ -> bool **)

let subtype ty1 ty2 =
  match ty1 with
  | Tint ->
    (match ty2 with
     | Tint -> true
     | Tany32 -> true
     | Tany64 -> true
     | _ -> false)
  | Tfloat ->
    (match ty2 with
     | Tfloat -> true
     | Tany64 -> true
     | _ -> false)
  | Tlong ->
    (match ty2 with
     | Tlong -> true
     | Tany64 -> true
     | _ -> false)
  | Tsingle ->
    (match ty2 with
     | Tsingle -> true
     | Tany32 -> true
     | Tany64 -> true
     | _ -> false)
  | Tany32 ->
    (match ty2 with
     | Tany32 -> true
     | Tany64 -> true
     | _ -> false)
  | Tany64 ->
    (match ty2 with
     | Tany64 -> true
     | _ -> false)

(** val subtype_list : typ list -> typ list -> bool **)

let rec subtype_list tyl1 tyl2 =
  match tyl1 with
  | [] ->
    (match tyl2 with
     | [] -> true
     | t :: l -> false)
  | ty1 :: tys1 ->
    (match tyl2 with
     | [] -> false
     | ty2 :: tys2 -> (&&) (subtype ty1 ty2) (subtype_list tys1 tys2))

type calling_convention = { cc_vararg : bool; cc_structret : bool }

(** val cc_default : calling_convention **)

let cc_default =
  { cc_vararg = false; cc_structret = false }

type signature = { sig_args : typ list; sig_res : typ option;
                   sig_cc : calling_convention }

(** val sig_args : signature -> typ list **)

let sig_args x = x.sig_args

(** val sig_res : signature -> typ option **)

let sig_res x = x.sig_res

(** val proj_sig_res : signature -> typ **)

let proj_sig_res s =
  match s.sig_res with
  | Some t -> t
  | None -> Tint

(** val signature_eq : signature -> signature -> bool **)

let signature_eq s1 s2 =
  let { sig_args = x; sig_res = x0; sig_cc = x1 } = s1 in
  let { sig_args = sig_args1; sig_res = sig_res1; sig_cc = sig_cc1 } = s2 in
  if list_typ_eq x sig_args1
  then if opt_typ_eq x0 sig_res1
       then let { cc_vararg = x2; cc_structret = x3 } = x1 in
            let { cc_vararg = cc_vararg1; cc_structret = cc_structret1 } =
              sig_cc1
            in
            if bool_dec x2 cc_vararg1
            then bool_dec x3 cc_structret1
            else false
       else false
  else false

(** val signature_main : signature **)

let signature_main =
  { sig_args = []; sig_res = (Some Tint); sig_cc = cc_default }

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

(** val chunk_eq : memory_chunk -> memory_chunk -> bool **)

let chunk_eq c1 c2 =
  match c1 with
  | Mint8signed ->
    (match c2 with
     | Mint8signed -> true
     | _ -> false)
  | Mint8unsigned ->
    (match c2 with
     | Mint8unsigned -> true
     | _ -> false)
  | Mint16signed ->
    (match c2 with
     | Mint16signed -> true
     | _ -> false)
  | Mint16unsigned ->
    (match c2 with
     | Mint16unsigned -> true
     | _ -> false)
  | Mint32 ->
    (match c2 with
     | Mint32 -> true
     | _ -> false)
  | Mint64 ->
    (match c2 with
     | Mint64 -> true
     | _ -> false)
  | Mfloat32 ->
    (match c2 with
     | Mfloat32 -> true
     | _ -> false)
  | Mfloat64 ->
    (match c2 with
     | Mfloat64 -> true
     | _ -> false)
  | Many32 ->
    (match c2 with
     | Many32 -> true
     | _ -> false)
  | Many64 ->
    (match c2 with
     | Many64 -> true
     | _ -> false)

(** val type_of_chunk : memory_chunk -> typ **)

let type_of_chunk = function
| Mint64 -> Tlong
| Mfloat32 -> Tsingle
| Mfloat64 -> Tfloat
| Many32 -> Tany32
| Many64 -> Tany64
| _ -> Tint

(** val chunk_of_type : typ -> memory_chunk **)

let chunk_of_type = function
| Tint -> Mint32
| Tfloat -> Mfloat64
| Tlong -> Mint64
| Tsingle -> Mfloat32
| Tany32 -> Many32
| Tany64 -> Many64

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of coq_Z
| Init_addrof of ident * Int.int

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : bool }

(** val gvar_info : 'a1 globvar -> 'a1 **)

let gvar_info x = x.gvar_info

(** val gvar_init : 'a1 globvar -> init_data list **)

let gvar_init x = x.gvar_init

(** val gvar_readonly : 'a1 globvar -> bool **)

let gvar_readonly x = x.gvar_readonly

(** val gvar_volatile : 'a1 globvar -> bool **)

let gvar_volatile x = x.gvar_volatile

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type ('f, 'v) program = { prog_defs : (ident * ('f, 'v) globdef) list;
                          prog_main : ident }

(** val prog_defs :
    ('a1, 'a2) program -> (ident * ('a1, 'a2) globdef) list **)

let prog_defs x = x.prog_defs

(** val prog_main : ('a1, 'a2) program -> ident **)

let prog_main x = x.prog_main

(** val transform_program_globdef :
    ('a1 -> 'a2) -> (ident * ('a1, 'a3) globdef) -> ident * ('a2, 'a3)
    globdef **)

let transform_program_globdef transf = function
| (id, g) ->
  (match g with
   | Gfun f -> (id, (Gfun (transf f)))
   | Gvar v -> (id, (Gvar v)))

(** val transform_program :
    ('a1 -> 'a2) -> ('a1, 'a3) program -> ('a2, 'a3) program **)

let transform_program transf p =
  { prog_defs = (map (transform_program_globdef transf) p.prog_defs);
    prog_main = p.prog_main }

(** val transf_globvar :
    ('a1 -> 'a2 res) -> 'a1 globvar -> 'a2 globvar res **)

let transf_globvar transf_var g =
  match transf_var g.gvar_info with
  | OK x ->
    OK { gvar_info = x; gvar_init = g.gvar_init; gvar_readonly =
      g.gvar_readonly; gvar_volatile = g.gvar_volatile }
  | Error msg -> Error msg

(** val transf_globdefs :
    ('a1 -> 'a2 res) -> ('a3 -> 'a4 res) -> (ident * ('a1, 'a3) globdef) list
    -> (ident * ('a2, 'a4) globdef) list res **)

let rec transf_globdefs transf_fun transf_var = function
| [] -> OK []
| p :: l' ->
  let (id, g) = p in
  (match g with
   | Gfun f ->
     (match transf_fun f with
      | OK tf ->
        (match transf_globdefs transf_fun transf_var l' with
         | OK x -> OK ((id, (Gfun tf)) :: x)
         | Error msg -> Error msg)
      | Error msg ->
        Error ((MSG
          ('I'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))))) :: ((CTX
          id) :: ((MSG (':'::(' '::[]))) :: msg))))
   | Gvar v ->
     (match transf_globvar transf_var v with
      | OK tv ->
        (match transf_globdefs transf_fun transf_var l' with
         | OK x -> OK ((id, (Gvar tv)) :: x)
         | Error msg -> Error msg)
      | Error msg ->
        Error ((MSG
          ('I'::('n'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::[]))))))))))))) :: ((CTX
          id) :: ((MSG (':'::(' '::[]))) :: msg)))))

(** val transform_partial_program2 :
    ('a1 -> 'a2 res) -> ('a3 -> 'a4 res) -> ('a1, 'a3) program -> ('a2, 'a4)
    program res **)

let transform_partial_program2 transf_fun transf_var p =
  match transf_globdefs transf_fun transf_var p.prog_defs with
  | OK x -> OK { prog_defs = x; prog_main = p.prog_main }
  | Error msg -> Error msg

(** val transform_partial_program :
    ('a1 -> 'a2 res) -> ('a1, 'a3) program -> ('a2, 'a3) program res **)

let transform_partial_program transf_partial p =
  transform_partial_program2 transf_partial (fun v -> OK v) p

type external_function =
| EF_external of ident * signature
| EF_builtin of ident * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_vload_global of memory_chunk * ident * Int.int
| EF_vstore_global of memory_chunk * ident * Int.int
| EF_malloc
| EF_free
| EF_memcpy of coq_Z * coq_Z
| EF_annot of ident * annot_arg list
| EF_annot_val of ident * typ
| EF_inline_asm of ident
and annot_arg =
| AA_arg of typ
| AA_int of Int.int
| AA_float of float

(** val annot_args_typ : annot_arg list -> typ list **)

let rec annot_args_typ = function
| [] -> []
| a :: targs' ->
  (match a with
   | AA_arg ty -> ty :: (annot_args_typ targs')
   | _ -> annot_args_typ targs')

(** val ef_sig : external_function -> signature **)

let ef_sig = function
| EF_external (name, sg) -> sg
| EF_builtin (name, sg) -> sg
| EF_vload chunk ->
  { sig_args = (Tint :: []); sig_res = (Some (type_of_chunk chunk)); sig_cc =
    cc_default }
| EF_vstore chunk ->
  { sig_args = (Tint :: ((type_of_chunk chunk) :: [])); sig_res = None;
    sig_cc = cc_default }
| EF_vload_global (chunk, id, ofs) ->
  { sig_args = []; sig_res = (Some (type_of_chunk chunk)); sig_cc =
    cc_default }
| EF_vstore_global (chunk, id, ofs) ->
  { sig_args = ((type_of_chunk chunk) :: []); sig_res = None; sig_cc =
    cc_default }
| EF_malloc ->
  { sig_args = (Tint :: []); sig_res = (Some Tint); sig_cc = cc_default }
| EF_free -> { sig_args = (Tint :: []); sig_res = None; sig_cc = cc_default }
| EF_memcpy (sz, al) ->
  { sig_args = (Tint :: (Tint :: [])); sig_res = None; sig_cc = cc_default }
| EF_annot (text, targs) ->
  { sig_args = (annot_args_typ targs); sig_res = None; sig_cc = cc_default }
| EF_annot_val (text, targ) ->
  { sig_args = (targ :: []); sig_res = (Some targ); sig_cc = cc_default }
| EF_inline_asm text ->
  { sig_args = []; sig_res = None; sig_cc = cc_default }

(** val ef_inline : external_function -> bool **)

let ef_inline = function
| EF_external (name, sg) -> false
| EF_malloc -> false
| EF_free -> false
| _ -> true

(** val external_function_eq :
    external_function -> external_function -> bool **)

let external_function_eq ef1 ef2 =
  match ef1 with
  | EF_external (x, x0) ->
    (match ef2 with
     | EF_external (name0, sg0) ->
       if ident_eq x name0 then signature_eq x0 sg0 else false
     | _ -> false)
  | EF_builtin (x, x0) ->
    (match ef2 with
     | EF_builtin (name0, sg0) ->
       if ident_eq x name0 then signature_eq x0 sg0 else false
     | _ -> false)
  | EF_vload x ->
    (match ef2 with
     | EF_vload chunk0 -> chunk_eq x chunk0
     | _ -> false)
  | EF_vstore x ->
    (match ef2 with
     | EF_vstore chunk0 -> chunk_eq x chunk0
     | _ -> false)
  | EF_vload_global (x, x0, x1) ->
    (match ef2 with
     | EF_vload_global (chunk0, id0, ofs0) ->
       if chunk_eq x chunk0
       then if ident_eq x0 id0 then Int.eq_dec x1 ofs0 else false
       else false
     | _ -> false)
  | EF_vstore_global (x, x0, x1) ->
    (match ef2 with
     | EF_vstore_global (chunk0, id0, ofs0) ->
       if chunk_eq x chunk0
       then if ident_eq x0 id0 then Int.eq_dec x1 ofs0 else false
       else false
     | _ -> false)
  | EF_malloc ->
    (match ef2 with
     | EF_malloc -> true
     | _ -> false)
  | EF_free ->
    (match ef2 with
     | EF_free -> true
     | _ -> false)
  | EF_memcpy (x, x0) ->
    (match ef2 with
     | EF_memcpy (sz0, al0) -> if zeq x sz0 then zeq x0 al0 else false
     | _ -> false)
  | EF_annot (x, x0) ->
    (match ef2 with
     | EF_annot (text0, targs0) ->
       if ident_eq x text0
       then list_eq_dec (fun x1 y ->
              match x1 with
              | AA_arg x2 ->
                (match y with
                 | AA_arg ty0 -> typ_eq x2 ty0
                 | _ -> false)
              | AA_int x2 ->
                (match y with
                 | AA_int n0 -> Int.eq_dec x2 n0
                 | _ -> false)
              | AA_float x2 ->
                (match y with
                 | AA_float n0 -> Float.eq_dec x2 n0
                 | _ -> false)) x0 targs0
       else false
     | _ -> false)
  | EF_annot_val (x, x0) ->
    (match ef2 with
     | EF_annot_val (text0, targ0) ->
       if ident_eq x text0 then typ_eq x0 targ0 else false
     | _ -> false)
  | EF_inline_asm x ->
    (match ef2 with
     | EF_inline_asm text0 -> ident_eq x text0
     | _ -> false)

type 'f fundef =
| Internal of 'f
| External of external_function

(** val transf_fundef : ('a1 -> 'a2) -> 'a1 fundef -> 'a2 fundef **)

let transf_fundef transf = function
| Internal f -> Internal (transf f)
| External ef -> External ef

(** val transf_partial_fundef :
    ('a1 -> 'a2 res) -> 'a1 fundef -> 'a2 fundef res **)

let transf_partial_fundef transf_partial = function
| Internal f ->
  (match transf_partial f with
   | OK x -> OK (Internal x)
   | Error msg -> Error msg)
| External ef -> OK (External ef)

