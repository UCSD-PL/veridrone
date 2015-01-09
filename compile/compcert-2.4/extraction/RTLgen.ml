open AST
open BinNums
open BinPos
open Cminor
open CminorSel
open Coqlib
open Datatypes
open Errors
open List0
open Maps
open Op
open RTL
open Registers

type mapping = { map_vars : reg PTree.t; map_letvars : reg list }

(** val map_vars : mapping -> reg PTree.t **)

let map_vars x = x.map_vars

(** val map_letvars : mapping -> reg list **)

let map_letvars x = x.map_letvars

type state = { st_nextreg : positive; st_nextnode : positive; st_code : code }

(** val st_nextreg : state -> positive **)

let st_nextreg x = x.st_nextreg

(** val st_nextnode : state -> positive **)

let st_nextnode x = x.st_nextnode

(** val st_code : state -> code **)

let st_code x = x.st_code

type 'a res =
| Error of errmsg
| OK of 'a * state

type 'a mon = state -> 'a res

(** val handle_error : 'a1 mon -> 'a1 mon -> 'a1 mon **)

let handle_error f g s =
  match f s with
  | Error e -> g s
  | OK (a, s') -> OK (a, s')

(** val init_state : state **)

let init_state =
  { st_nextreg = Coq_xH; st_nextnode = Coq_xH; st_code = PTree.empty }

(** val add_instr : instruction -> node mon **)

let add_instr i s =
  let n = s.st_nextnode in
  OK (n, { st_nextreg = s.st_nextreg; st_nextnode = (Pos.succ n); st_code =
  (PTree.set n i s.st_code) })

(** val reserve_instr : node mon **)

let reserve_instr s =
  let n = s.st_nextnode in
  OK (n, { st_nextreg = s.st_nextreg; st_nextnode = (Pos.succ n); st_code =
  s.st_code })

(** val check_empty_node : state -> node -> bool **)

let check_empty_node s n =
  match PTree.get n s.st_code with
  | Some i -> false
  | None -> true

(** val update_instr : node -> instruction -> unit mon **)

let update_instr n i s =
  if plt n s.st_nextnode
  then if check_empty_node s n
       then OK ((), { st_nextreg = s.st_nextreg; st_nextnode = s.st_nextnode;
              st_code = (PTree.set n i s.st_code) })
       else Error
              (msg
                ('R'::('T'::('L'::('g'::('e'::('n'::('.'::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('i'::('n'::('s'::('t'::('r'::[]))))))))))))))))))))
  else Error
         (msg
           ('R'::('T'::('L'::('g'::('e'::('n'::('.'::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('i'::('n'::('s'::('t'::('r'::[]))))))))))))))))))))

(** val new_reg : reg mon **)

let new_reg s =
  OK (s.st_nextreg, { st_nextreg = (Pos.succ s.st_nextreg); st_nextnode =
    s.st_nextnode; st_code = s.st_code })

(** val init_mapping : mapping **)

let init_mapping =
  { map_vars = PTree.empty; map_letvars = [] }

(** val add_var : mapping -> ident -> (reg * mapping) mon **)

let add_var map name s =
  match new_reg s with
  | Error msg0 -> Error msg0
  | OK (a, s') ->
    OK ((a, { map_vars = (PTree.set name a map.map_vars); map_letvars =
      map.map_letvars }), s')

(** val add_vars : mapping -> ident list -> (reg list * mapping) mon **)

let rec add_vars map names s =
  match names with
  | [] -> OK (([], map), s)
  | n1 :: nl ->
    (match add_vars map nl s with
     | Error msg0 -> Error msg0
     | OK (a, s') ->
       (match add_var (snd a) n1 s' with
        | Error msg0 -> Error msg0
        | OK (a0, s'0) -> OK ((((fst a0) :: (fst a)), (snd a0)), s'0)))

(** val find_var : mapping -> ident -> reg mon **)

let find_var map name s =
  match PTree.get name map.map_vars with
  | Some r -> OK (r, s)
  | None ->
    Error ((MSG
      ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('u'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::[])))))))))))))))))))))))))) :: ((CTX
      name) :: []))

(** val add_letvar : mapping -> reg -> mapping **)

let add_letvar map r =
  { map_vars = map.map_vars; map_letvars = (r :: map.map_letvars) }

(** val find_letvar : mapping -> nat -> reg mon **)

let find_letvar map idx s =
  match nth_error map.map_letvars idx with
  | Some r -> OK (r, s)
  | None ->
    Error
      (msg
        ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('u'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('l'::('e'::('t'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))))))))

(** val alloc_reg : mapping -> expr -> reg mon **)

let alloc_reg map = function
| Evar id -> find_var map id
| Eletvar n -> find_letvar map n
| _ -> new_reg

(** val alloc_regs : mapping -> exprlist -> reg list mon **)

let rec alloc_regs map al s =
  match al with
  | Enil -> OK ([], s)
  | Econs (a, bl) ->
    (match alloc_reg map a s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match alloc_regs map bl s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> OK ((a0 :: a1), s'0)))

(** val alloc_optreg : mapping -> ident option -> reg mon **)

let alloc_optreg map = function
| Some id -> find_var map id
| None -> new_reg

(** val add_move : reg -> reg -> node -> node mon **)

let add_move rs rd nd =
  if Reg.eq rs rd
  then (fun s -> OK (nd, s))
  else add_instr (Iop (Omove, (rs :: []), rd, nd))

(** val transl_expr : mapping -> expr -> reg -> node -> node mon **)

let rec transl_expr map a rd nd s =
  match a with
  | Evar v ->
    (match find_var map v s with
     | Error msg0 -> Error msg0
     | OK (a0, s') -> add_move a0 rd nd s')
  | Eop (op, al) ->
    (match alloc_regs map al s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match add_instr (Iop (op, a0, rd, nd)) s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_exprlist map al a0 a1 s'0))
  | Eload (chunk, addr, al) ->
    (match alloc_regs map al s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match add_instr (Iload (chunk, addr, a0, rd, nd)) s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_exprlist map al a0 a1 s'0))
  | Econdition (a0, b, c) ->
    (match transl_expr map c rd nd s with
     | Error msg0 -> Error msg0
     | OK (a1, s') ->
       (match transl_expr map b rd nd s' with
        | Error msg0 -> Error msg0
        | OK (a2, s'0) -> transl_condexpr map a0 a2 a1 s'0))
  | Elet (b, c) ->
    (match new_reg s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match transl_expr (add_letvar map a0) c rd nd s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_expr map b a0 a1 s'0))
  | Eletvar n ->
    (match find_letvar map n s with
     | Error msg0 -> Error msg0
     | OK (a0, s') -> add_move a0 rd nd s')
  | Ebuiltin (ef, al) ->
    (match alloc_regs map al s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match add_instr (Ibuiltin (ef, a0, rd, nd)) s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_exprlist map al a0 a1 s'0))
  | Eexternal (id, sg, al) ->
    (match alloc_regs map al s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match add_instr (Icall (sg, (Coq_inr id), a0, rd, nd)) s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_exprlist map al a0 a1 s'0))

(** val transl_exprlist :
    mapping -> exprlist -> reg list -> node -> node mon **)

and transl_exprlist map al rl nd s =
  match al with
  | Enil ->
    (match rl with
     | [] -> OK (nd, s)
     | r :: l ->
       Error
         (msg
           ('R'::('T'::('L'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::('l'::('i'::('s'::('t'::[]))))))))))))))))))))))))
  | Econs (b, bs) ->
    (match rl with
     | [] ->
       Error
         (msg
           ('R'::('T'::('L'::('g'::('e'::('n'::('.'::('t'::('r'::('a'::('n'::('s'::('l'::('_'::('e'::('x'::('p'::('r'::('l'::('i'::('s'::('t'::[])))))))))))))))))))))))
     | r :: rs ->
       (match transl_exprlist map bs rs nd s with
        | Error msg0 -> Error msg0
        | OK (a, s') -> transl_expr map b r a s'))

(** val transl_condexpr : mapping -> condexpr -> node -> node -> node mon **)

and transl_condexpr map a ntrue nfalse s =
  match a with
  | CEcond (c, al) ->
    (match alloc_regs map al s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match add_instr (Icond (c, a0, ntrue, nfalse)) s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_exprlist map al a0 a1 s'0))
  | CEcondition (a0, b, c) ->
    (match transl_condexpr map c ntrue nfalse s with
     | Error msg0 -> Error msg0
     | OK (a1, s') ->
       (match transl_condexpr map b ntrue nfalse s' with
        | Error msg0 -> Error msg0
        | OK (a2, s'0) -> transl_condexpr map a0 a2 a1 s'0))
  | CElet (b, c) ->
    (match new_reg s with
     | Error msg0 -> Error msg0
     | OK (a0, s') ->
       (match transl_condexpr (add_letvar map a0) c ntrue nfalse s' with
        | Error msg0 -> Error msg0
        | OK (a1, s'0) -> transl_expr map b a0 a1 s'0))

(** val transl_exit : node list -> nat -> node mon **)

let transl_exit nexits n s =
  match nth_error nexits n with
  | Some ne -> OK (ne, s)
  | None ->
    Error
      (msg
        ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('e'::('x'::('i'::('t'::[])))))))))))))))))))

(** val transl_jumptable : node list -> nat list -> node list mon **)

let rec transl_jumptable nexits tbl s =
  match tbl with
  | [] -> OK ([], s)
  | t1 :: tl ->
    (match transl_exit nexits t1 s with
     | Error msg0 -> Error msg0
     | OK (a, s') ->
       (match transl_jumptable nexits tl s' with
        | Error msg0 -> Error msg0
        | OK (a0, s'0) -> OK ((a :: a0), s'0)))

(** val transl_exitexpr : mapping -> exitexpr -> node list -> node mon **)

let rec transl_exitexpr map a nexits =
  match a with
  | XEexit n -> transl_exit nexits n
  | XEjumptable (a0, tbl) ->
    (fun s ->
      match alloc_reg map a0 s with
      | Error msg0 -> Error msg0
      | OK (a1, s') ->
        (match transl_jumptable nexits tbl s' with
         | Error msg0 -> Error msg0
         | OK (a2, s'0) ->
           (match add_instr (Ijumptable (a1, a2)) s'0 with
            | Error msg0 -> Error msg0
            | OK (a3, s'1) -> transl_expr map a0 a1 a3 s'1)))
  | XEcondition (a0, b, c) ->
    (fun s ->
      match transl_exitexpr map c nexits s with
      | Error msg0 -> Error msg0
      | OK (a1, s') ->
        (match transl_exitexpr map b nexits s' with
         | Error msg0 -> Error msg0
         | OK (a2, s'0) -> transl_condexpr map a0 a2 a1 s'0))
  | XElet (a0, b) ->
    (fun s ->
      match new_reg s with
      | Error msg0 -> Error msg0
      | OK (a1, s') ->
        (match transl_exitexpr (add_letvar map a1) b nexits s' with
         | Error msg0 -> Error msg0
         | OK (a2, s'0) -> transl_expr map a0 a1 a2 s'0))

(** val more_likely : condexpr -> stmt -> stmt -> bool **)

let more_likely = RTLgenaux.more_likely

type labelmap = node PTree.t

(** val transl_stmt :
    mapping -> stmt -> node -> node list -> labelmap -> node -> reg option ->
    node mon **)

let rec transl_stmt map s nd nexits ngoto nret rret =
  match s with
  | Sskip -> (fun s0 -> OK (nd, s0))
  | Sassign (v, b) ->
    (fun s0 ->
      match find_var map v s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') -> transl_expr map b a nd s')
  | Sstore (chunk, addr, al, b) ->
    (fun s0 ->
      match alloc_regs map al s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') ->
        (match alloc_reg map b s' with
         | Error msg0 -> Error msg0
         | OK (a0, s'0) ->
           (match add_instr (Istore (chunk, addr, a, a0, nd)) s'0 with
            | Error msg0 -> Error msg0
            | OK (a1, s'1) ->
              (match transl_expr map b a0 a1 s'1 with
               | Error msg0 -> Error msg0
               | OK (a2, s'2) -> transl_exprlist map al a a2 s'2))))
  | Scall (optid, sig0, s0, cl) ->
    (fun s1 ->
      match s0 with
      | Coq_inl b ->
        (match alloc_reg map b s1 with
         | Error msg0 -> Error msg0
         | OK (a, s') ->
           (match alloc_regs map cl s' with
            | Error msg0 -> Error msg0
            | OK (a0, s'0) ->
              (match alloc_optreg map optid s'0 with
               | Error msg0 -> Error msg0
               | OK (a1, s'1) ->
                 (match add_instr (Icall (sig0, (Coq_inl a), a0, a1, nd)) s'1 with
                  | Error msg0 -> Error msg0
                  | OK (a2, s'2) ->
                    (match transl_exprlist map cl a0 a2 s'2 with
                     | Error msg0 -> Error msg0
                     | OK (a3, s'3) -> transl_expr map b a a3 s'3)))))
      | Coq_inr id ->
        (match alloc_regs map cl s1 with
         | Error msg0 -> Error msg0
         | OK (a, s') ->
           (match alloc_optreg map optid s' with
            | Error msg0 -> Error msg0
            | OK (a0, s'0) ->
              (match add_instr (Icall (sig0, (Coq_inr id), a, a0, nd)) s'0 with
               | Error msg0 -> Error msg0
               | OK (a1, s'1) -> transl_exprlist map cl a a1 s'1))))
  | Stailcall (sig0, s0, cl) ->
    (fun s1 ->
      match s0 with
      | Coq_inl b ->
        (match alloc_reg map b s1 with
         | Error msg0 -> Error msg0
         | OK (a, s') ->
           (match alloc_regs map cl s' with
            | Error msg0 -> Error msg0
            | OK (a0, s'0) ->
              (match add_instr (Itailcall (sig0, (Coq_inl a), a0)) s'0 with
               | Error msg0 -> Error msg0
               | OK (a1, s'1) ->
                 (match transl_exprlist map cl a0 a1 s'1 with
                  | Error msg0 -> Error msg0
                  | OK (a2, s'2) -> transl_expr map b a a2 s'2))))
      | Coq_inr id ->
        (match alloc_regs map cl s1 with
         | Error msg0 -> Error msg0
         | OK (a, s') ->
           (match add_instr (Itailcall (sig0, (Coq_inr id), a)) s' with
            | Error msg0 -> Error msg0
            | OK (a0, s'0) -> transl_exprlist map cl a a0 s'0)))
  | Sbuiltin (optid, ef, al) ->
    (fun s0 ->
      match alloc_regs map al s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') ->
        (match alloc_optreg map optid s' with
         | Error msg0 -> Error msg0
         | OK (a0, s'0) ->
           (match add_instr (Ibuiltin (ef, a, a0, nd)) s'0 with
            | Error msg0 -> Error msg0
            | OK (a1, s'1) -> transl_exprlist map al a a1 s'1)))
  | Sseq (s1, s2) ->
    (fun s0 ->
      match transl_stmt map s2 nd nexits ngoto nret rret s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') -> transl_stmt map s1 a nexits ngoto nret rret s')
  | Sifthenelse (c, strue, sfalse) ->
    (fun s0 ->
      if more_likely c strue sfalse
      then (match transl_stmt map sfalse nd nexits ngoto nret rret s0 with
            | Error msg0 -> Error msg0
            | OK (a, s') ->
              (match transl_stmt map strue nd nexits ngoto nret rret s' with
               | Error msg0 -> Error msg0
               | OK (a0, s'0) -> transl_condexpr map c a0 a s'0))
      else (match transl_stmt map strue nd nexits ngoto nret rret s0 with
            | Error msg0 -> Error msg0
            | OK (a, s') ->
              (match transl_stmt map sfalse nd nexits ngoto nret rret s' with
               | Error msg0 -> Error msg0
               | OK (a0, s'0) -> transl_condexpr map c a a0 s'0)))
  | Sloop sbody ->
    (fun s0 ->
      match reserve_instr s0 with
      | Error msg0 -> Error msg0
      | OK (a, s') ->
        (match transl_stmt map sbody a nexits ngoto nret rret s' with
         | Error msg0 -> Error msg0
         | OK (a0, s'0) ->
           (match update_instr a (Inop a0) s'0 with
            | Error msg0 -> Error msg0
            | OK (a1, s'1) -> add_instr (Inop a0) s'1)))
  | Sblock sbody -> transl_stmt map sbody nd (nd :: nexits) ngoto nret rret
  | Sexit n -> transl_exit nexits n
  | Sswitch a -> transl_exitexpr map a nexits
  | Sreturn opt_a ->
    (match opt_a with
     | Some a ->
       (match rret with
        | Some r -> transl_expr map a r nret
        | None ->
          (fun s0 -> Error
            (msg
              ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('o'::('n'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::[]))))))))))))))))))))))))))))))))))
     | None -> (fun s0 -> OK (nret, s0)))
  | Slabel (lbl, s') ->
    (fun s0 ->
      match transl_stmt map s' nd nexits ngoto nret rret s0 with
      | Error msg0 -> Error msg0
      | OK (a, s'0) ->
        (match PTree.get lbl ngoto with
         | Some n ->
           (match handle_error (update_instr n (Inop a)) (fun s1 -> Error
                    ((MSG
                    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('y'::('-'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::[])))))))))))))))))))))))) :: ((CTX
                    lbl) :: []))) s'0 with
            | Error msg0 -> Error msg0
            | OK (a0, s'1) -> OK (a, s'1))
         | None ->
           Error
             (msg
               ('R'::('T'::('L'::('g'::('e'::('n'::(':'::(' '::('u'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('l'::('a'::('b'::('e'::('l'::[]))))))))))))))))))))))))
  | Sgoto lbl ->
    (fun s0 ->
      match PTree.get lbl ngoto with
      | Some n -> OK (n, s0)
      | None ->
        Error ((MSG
          ('U'::('n'::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('d'::('e'::('f'::('i'::('n'::('e'::('d'::(' '::('l'::('a'::('b'::('e'::('l'::(' '::[]))))))))))))))))))))))))) :: ((CTX
          lbl) :: [])))

(** val alloc_label : label -> (labelmap * state) -> labelmap * state **)

let alloc_label lbl = function
| (map, s) ->
  let n = s.st_nextnode in
  ((PTree.set lbl n map), { st_nextreg = s.st_nextreg; st_nextnode =
  (Pos.succ s.st_nextnode); st_code = s.st_code })

(** val reserve_labels : stmt -> (labelmap * state) -> labelmap * state **)

let rec reserve_labels s ms =
  match s with
  | Sseq (s1, s2) -> reserve_labels s1 (reserve_labels s2 ms)
  | Sifthenelse (c, s1, s2) -> reserve_labels s1 (reserve_labels s2 ms)
  | Sloop s1 -> reserve_labels s1 ms
  | Sblock s1 -> reserve_labels s1 ms
  | Slabel (lbl, s1) -> alloc_label lbl (reserve_labels s1 ms)
  | _ -> ms

(** val ret_reg : signature -> reg -> reg option **)

let ret_reg sig0 rd =
  match sig0.sig_res with
  | Some ty -> Some rd
  | None -> None

(** val transl_fun :
    CminorSel.coq_function -> labelmap -> (node * reg list) mon **)

let transl_fun f ngoto s =
  match add_vars init_mapping f.CminorSel.fn_params s with
  | Error msg0 -> Error msg0
  | OK (a, s') ->
    (match add_vars (snd a) f.fn_vars s' with
     | Error msg0 -> Error msg0
     | OK (a0, s'0) ->
       (match new_reg s'0 with
        | Error msg0 -> Error msg0
        | OK (a1, s'1) ->
          let orret = ret_reg f.CminorSel.fn_sig a1 in
          (match add_instr (Ireturn orret) s'1 with
           | Error msg0 -> Error msg0
           | OK (a2, s'2) ->
             (match transl_stmt (snd a0) f.fn_body a2 [] ngoto a2 orret s'2 with
              | Error msg0 -> Error msg0
              | OK (a3, s'3) -> OK ((a3, (fst a)), s'3)))))

(** val transl_function :
    CminorSel.coq_function -> coq_function Errors.res **)

let transl_function f =
  let (ngoto, s0) = reserve_labels f.fn_body (PTree.empty, init_state) in
  (match transl_fun f ngoto s0 with
   | Error msg0 -> Errors.Error msg0
   | OK (p, s) ->
     let (nentry, rparams) = p in
     Errors.OK { fn_sig = f.CminorSel.fn_sig; fn_params = rparams;
     fn_stacksize = f.fn_stackspace; fn_code = s.st_code; fn_entrypoint =
     nentry })

(** val transl_fundef :
    CminorSel.coq_function AST.fundef -> coq_function AST.fundef Errors.res **)

let transl_fundef =
  transf_partial_fundef transl_function

(** val transl_program : CminorSel.program -> program Errors.res **)

let transl_program p =
  transform_partial_program transl_fundef p

