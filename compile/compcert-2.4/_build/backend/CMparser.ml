exception Error

type token = 
  | WHILE
  | VOLATILE
  | VOID
  | VAR
  | TILDEL
  | TILDE
  | TAILCALL
  | SWITCHL
  | SWITCH
  | STRINGLIT of (string)
  | STARL
  | STARF
  | STAR
  | STACK
  | SLASHU
  | SLASHLU
  | SLASHL
  | SLASHF
  | SLASH
  | SINGLE
  | SEMICOLON
  | RPAREN
  | RETURN
  | READONLY
  | RBRACKET
  | RBRACERBRACE
  | RBRACE
  | PLUSL
  | PLUSF
  | PLUS
  | PERCENTU
  | PERCENTLU
  | PERCENTL
  | PERCENT
  | MINUSL
  | MINUSGREATER
  | MINUSF
  | MINUS
  | MATCH
  | LPAREN
  | LOOP
  | LONGUOFFLOAT
  | LONGOFINTU
  | LONGOFINT
  | LONGOFFLOAT
  | LONGLIT of (int64)
  | LONG
  | LESSU
  | LESSLU
  | LESSLESSL
  | LESSLESS
  | LESSL
  | LESSF
  | LESSEQUALU
  | LESSEQUALLU
  | LESSEQUALL
  | LESSEQUALF
  | LESSEQUAL
  | LESS
  | LBRACKET
  | LBRACELBRACE
  | LBRACE
  | INTUOFFLOAT
  | INTOFLONG
  | INTOFFLOAT
  | INTLIT of (int32)
  | INT8U
  | INT8S
  | INT8
  | INT64
  | INT32
  | INT16U
  | INT16S
  | INT16
  | INT
  | IF
  | IDENT of (string)
  | GREATERU
  | GREATERLU
  | GREATERL
  | GREATERGREATERU
  | GREATERGREATERLU
  | GREATERGREATERL
  | GREATERGREATER
  | GREATERF
  | GREATEREQUALU
  | GREATEREQUALLU
  | GREATEREQUALL
  | GREATEREQUALF
  | GREATEREQUAL
  | GREATER
  | GOTO
  | FLOATOFLONGU
  | FLOATOFLONG
  | FLOATOFINTU
  | FLOATOFINT
  | FLOATLIT of (float)
  | FLOAT64
  | FLOAT32
  | FLOAT
  | EXTERN
  | EXIT
  | EQUALEQUALU
  | EQUALEQUALLU
  | EQUALEQUALL
  | EQUALEQUALF
  | EQUALEQUAL
  | EQUAL
  | EOF
  | ELSE
  | DEFAULT
  | COMMA
  | COLON
  | CASE
  | CARETL
  | CARET
  | BUILTIN
  | BARL
  | BAR
  | BANGEQUALU
  | BANGEQUALLU
  | BANGEQUALL
  | BANGEQUALF
  | BANGEQUAL
  | BANG
  | AMPERSANDL
  | AMPERSAND
  | ABSF

and _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  mutable _menhir_token: token;
  mutable _menhir_startp: Lexing.position;
  mutable _menhir_endp: Lexing.position;
  mutable _menhir_shifted: int
}

and _menhir_state = 
  | MenhirState403
  | MenhirState401
  | MenhirState399
  | MenhirState388
  | MenhirState383
  | MenhirState378
  | MenhirState375
  | MenhirState368
  | MenhirState365
  | MenhirState354
  | MenhirState351
  | MenhirState349
  | MenhirState348
  | MenhirState346
  | MenhirState344
  | MenhirState343
  | MenhirState342
  | MenhirState339
  | MenhirState336
  | MenhirState331
  | MenhirState327
  | MenhirState316
  | MenhirState313
  | MenhirState308
  | MenhirState297
  | MenhirState294
  | MenhirState290
  | MenhirState287
  | MenhirState285
  | MenhirState284
  | MenhirState258
  | MenhirState256
  | MenhirState249
  | MenhirState247
  | MenhirState245
  | MenhirState243
  | MenhirState241
  | MenhirState239
  | MenhirState237
  | MenhirState235
  | MenhirState233
  | MenhirState231
  | MenhirState229
  | MenhirState227
  | MenhirState225
  | MenhirState223
  | MenhirState221
  | MenhirState219
  | MenhirState217
  | MenhirState215
  | MenhirState213
  | MenhirState211
  | MenhirState209
  | MenhirState207
  | MenhirState205
  | MenhirState203
  | MenhirState201
  | MenhirState199
  | MenhirState197
  | MenhirState195
  | MenhirState193
  | MenhirState191
  | MenhirState189
  | MenhirState187
  | MenhirState185
  | MenhirState183
  | MenhirState181
  | MenhirState179
  | MenhirState177
  | MenhirState175
  | MenhirState173
  | MenhirState171
  | MenhirState169
  | MenhirState167
  | MenhirState165
  | MenhirState163
  | MenhirState161
  | MenhirState159
  | MenhirState157
  | MenhirState155
  | MenhirState153
  | MenhirState151
  | MenhirState149
  | MenhirState147
  | MenhirState145
  | MenhirState143
  | MenhirState141
  | MenhirState139
  | MenhirState137
  | MenhirState135
  | MenhirState133
  | MenhirState131
  | MenhirState128
  | MenhirState124
  | MenhirState122
  | MenhirState120
  | MenhirState118
  | MenhirState115
  | MenhirState114
  | MenhirState100
  | MenhirState98
  | MenhirState95
  | MenhirState94
  | MenhirState93
  | MenhirState92
  | MenhirState89
  | MenhirState88
  | MenhirState85
  | MenhirState84
  | MenhirState82
  | MenhirState81
  | MenhirState80
  | MenhirState78
  | MenhirState77
  | MenhirState76
  | MenhirState75
  | MenhirState74
  | MenhirState73
  | MenhirState72
  | MenhirState71
  | MenhirState69
  | MenhirState68
  | MenhirState67
  | MenhirState65
  | MenhirState57
  | MenhirState50
  | MenhirState46
  | MenhirState40
  | MenhirState13
  | MenhirState2
  | MenhirState0

  
open Datatypes
open Camlcoq
open BinNums
open Integers
open AST
open Cminor

(** Parsing external functions *)

type ef_token =
  | EFT_tok of string
  | EFT_int of int32
  | EFT_string of string
  | EFT_chunk of memory_chunk

let mkef sg toks =
  match toks with
  | [EFT_tok "extern"; EFT_string s] ->
      EF_external(intern_string s, sg)
  | [EFT_tok "builtin"; EFT_string s] ->
      EF_builtin(intern_string s, sg)
  | [EFT_tok "volatile"; EFT_tok "load"; EFT_chunk c] ->
      EF_vload c
  | [EFT_tok "volatile"; EFT_tok "store"; EFT_chunk c] ->
      EF_vstore c
  | [EFT_tok "volatile"; EFT_tok "load"; EFT_chunk c; 
     EFT_tok "global"; EFT_string s; EFT_int n] ->
      EF_vload_global(c, intern_string s, coqint_of_camlint n)
  | [EFT_tok "volatile"; EFT_tok "store"; EFT_chunk c; 
     EFT_tok "global"; EFT_string s; EFT_int n] ->
      EF_vstore_global(c, intern_string s, coqint_of_camlint n)
  | [EFT_tok "malloc"] ->
      EF_malloc
  | [EFT_tok "free"] ->
      EF_free
  | [EFT_tok "memcpy"; EFT_tok "size"; EFT_int sz; EFT_tok "align"; EFT_int al] ->
      EF_memcpy(Z.of_sint32 sz, Z.of_sint32 al)
  | [EFT_tok "annot"; EFT_string txt] ->
      EF_annot(intern_string txt,
               List.map (fun t -> AA_arg t) sg.sig_args)
  | [EFT_tok "annot_val"; EFT_string txt] ->
      if sg.sig_args = [] then raise Parsing.Parse_error;
      EF_annot_val(intern_string txt, List.hd sg.sig_args)
  | [EFT_tok "inline_asm"; EFT_string txt] ->
      EF_inline_asm(intern_string txt)
  | _ ->
      raise Parsing.Parse_error

(** Naming function calls in expressions *)

type rexpr =
  | Rvar of ident
  | Rconst of constant
  | Runop of unary_operation * rexpr
  | Rbinop of binary_operation * rexpr * rexpr
  | Rload of memory_chunk * rexpr
  | Rcall of signature * rexpr * rexpr list
  | Rbuiltin of signature * ef_token list * rexpr list

let temp_counter = ref 0

let temporaries = ref []

let mktemp () =
  incr temp_counter;
  let n = Printf.sprintf "__t%d" !temp_counter in
  let id = intern_string n in
  temporaries := id :: !temporaries;
  id

let convert_accu = ref []

let rec convert_rexpr = function
  | Rvar id -> Evar id
  | Rconst c -> Econst c
  | Runop(op, e1) -> Eunop(op, convert_rexpr e1)
  | Rbinop(op, e1, e2) ->
      let c1 = convert_rexpr e1 in
      let c2 = convert_rexpr e2 in
      Ebinop(op, c1, c2)
  | Rload(chunk, e1) -> Eload(chunk, convert_rexpr e1)
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      let t = mktemp() in
      convert_accu := Scall(Some t, sg, c1, cl) :: !convert_accu;
      Evar t
  | Rbuiltin(sg, pef, el) ->
      let ef = mkef sg pef in
      let cl = convert_rexpr_list el in
      let t = mktemp() in
      convert_accu := Sbuiltin(Some t, ef, cl) :: !convert_accu;
      Evar t

and convert_rexpr_list = function
  | [] -> []
  | e1 :: el ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      c1 :: cl

let rec prepend_seq stmts last =
  match stmts with
  | [] -> last
  | s1 :: sl -> prepend_seq sl (Sseq(s1, last))

let mkeval e =
  convert_accu := [];
  match e with
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Scall(None, sg, c1, cl))
  | Rbuiltin(sg, pef, el) -> 
      let ef = mkef sg pef in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Sbuiltin(None, ef, cl))
  | _ ->
      ignore (convert_rexpr e);
      prepend_seq !convert_accu Sskip

let mkassign id e =
  convert_accu := [];
  match e with
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Scall(Some id, sg, c1, cl))
  | Rbuiltin(sg, pef, el) ->
      let ef = mkef sg pef in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Sbuiltin(Some id, ef, cl))
  | _ ->
      let c = convert_rexpr e in
      prepend_seq !convert_accu (Sassign(id, c))

let mkstore chunk e1 e2 =
  convert_accu := [];
  let c1 = convert_rexpr e1 in
  let c2 = convert_rexpr e2 in
  prepend_seq !convert_accu (Sstore(chunk, c1, c2))

let mkifthenelse e s1 s2 =
  convert_accu := [];
  let c = convert_rexpr e in
  prepend_seq !convert_accu (Sifthenelse(c, s1, s2))

let mkreturn_some e =
  convert_accu := [];
  let c = convert_rexpr e in
  prepend_seq !convert_accu (Sreturn (Some c))

let mktailcall sg e1 el =
  convert_accu := [];
  let c1 = convert_rexpr e1 in
  let cl = convert_rexpr_list el in
  prepend_seq !convert_accu (Stailcall(sg, c1, cl))

let mkwhile expr body =
  Sblock (Sloop (mkifthenelse expr body (Sexit O)))

(** Other constructors *)

let intconst n =
  Rconst(Ointconst(coqint_of_camlint n))

let longconst n =
  Rconst(Olongconst(coqint_of_camlint64 n))

let exitnum n = Nat.of_int32 n

let mkswitch islong convert expr (cases, dfl) =
  convert_accu := [];
  let c = convert_rexpr expr in
  let rec mktable = function
  | [] -> []
  | (key, exit) :: rem ->
      (convert key, exitnum exit) :: mktable rem in
  prepend_seq !convert_accu (Sswitch(islong, c, mktable cases, exitnum dfl))

(***
   match (a) { case 0: s0; case 1: s1; case 2: s2; }  --->

   block {
   block {
   block {
   block {
     switch(a) { case 0: exit 0; case 1: exit 1; default: exit 2; }
   }; s0; exit 2;
   }; s1; exit 1;
   }; s2;
   }

   Note that matches are assumed to be exhaustive
***)

let mkmatch_aux expr cases =
  let ncases = List.length cases in
  let rec mktable n = function
    | [] -> assert false
    | [key, action] -> []
    | (key, action) :: rem ->
        (coqint_of_camlint key, Nat.of_int n)
        :: mktable (n + 1) rem in
  let sw =
    Sswitch(false, expr, mktable 0 cases, Nat.of_int (ncases - 1)) in
  let rec mkblocks body n = function
    | [] -> assert false
    | [key, action] ->
        Sblock(Sseq(body, action))
    | (key, action) :: rem ->
        mkblocks
          (Sblock(Sseq(body, Sseq(action, Sexit (Nat.of_int n)))))
          (n - 1)
          rem in
  mkblocks (Sblock sw) (ncases - 1) cases

let mkmatch expr cases =
  convert_accu := [];
  let c = convert_rexpr expr in
  let s =
    match cases with
    | [] -> Sskip (* ??? *)
    | [key, action] -> action
    | _ -> mkmatch_aux c cases in
  prepend_seq !convert_accu s

let _eRR =
  Error

let rec _menhir_goto_init_data_list_1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.init_data list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | FLOAT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | FLOAT32 ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | FLOAT64 ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | FLOATLIT _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
        | INT ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | INT16 ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | INT32 ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | INT64 ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | INT8 ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | INTLIT _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
        | LBRACKET ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | LONGLIT _v ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (AST.init_data list) =                                                 ( _1 ) in
        _menhir_goto_init_data_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_stmt_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Cminor.stmt) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState349 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( _2 ) in
            _menhir_goto_stmts _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState375 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _1), _, _2) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( Sseq(_1, _2) ) in
        _menhir_goto_stmt_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState344 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACERBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( Sblock(_2) ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState342 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CASE ->
            _menhir_run340 _menhir_env (Obj.magic _menhir_stack) MenhirState383
        | RBRACE ->
            _menhir_reduce133 _menhir_env (Obj.magic _menhir_stack) MenhirState383
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState383)
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((((_menhir_stack, _1), _, _3), _, _6), _8), _9), _, _10) = _menhir_stack in
            let _v : (AST.ident * (Cminor.fundef, unit) AST.globdef) =       ( let tmp = !temporaries in
        temporaries := [];
        temp_counter := 0;
        (intern_string _1,
        Gfun(Internal { fn_sig = _6;
                        fn_params = List.rev _3;
                        fn_vars = List.rev (tmp @ _9);
                        fn_stackspace = _8;
                        fn_body = _10 })) ) in
            _menhir_goto_proc _menhir_env _menhir_stack _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_match_cases : _menhir_env -> 'ttv_tail -> _menhir_state -> ((int32 * Cminor.stmt) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState383 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _2), _, _4), _, _5) = _menhir_stack in
        let _v : ((int32 * Cminor.stmt) list) =                                                 ( (_2, _4) :: _5 ) in
        _menhir_goto_match_cases _menhir_env _menhir_stack _menhir_s _v
    | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, _3), _, _6) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mkmatch _3 _6 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_switch_cases : _menhir_env -> 'ttv_tail -> _menhir_state -> ((int32 * int32) list * int32) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState327 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _2), _5), _, _7) = _menhir_stack in
        let _v : ((int32 * int32) list * int32) =            ( let (cases, dfl) = _7 in ((_2, _5) :: cases, dfl) ) in
        _menhir_goto_switch_cases _menhir_env _menhir_stack _menhir_s _v
    | MenhirState316 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, _3), _, _6) = _menhir_stack in
            let _v : (Cminor.stmt) =                                          ( mkswitch false Z.of_uint32 _3 _6 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_switchl_cases : _menhir_env -> 'ttv_tail -> _menhir_state -> ((int64 * int32) list * int32) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState308 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _2), _5), _, _7) = _menhir_stack in
        let _v : ((int64 * int32) list * int32) =            ( let (cases, dfl) = _7 in ((_2, _5) :: cases, dfl) ) in
        _menhir_goto_switchl_cases _menhir_env _menhir_stack _menhir_s _v
    | MenhirState297 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, _3), _, _6) = _menhir_stack in
            let _v : (Cminor.stmt) =                                          ( mkswitch true Z.of_uint64 _3 _6 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_init_data : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.init_data) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _3 = _v in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (AST.init_data list) =                                                  ( _3 :: _1 ) in
        _menhir_goto_init_data_list_1 _menhir_env _menhir_stack _menhir_s _v
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = _v in
        let _v : (AST.init_data list) =                                                  ( [_1] ) in
        _menhir_goto_init_data_list_1 _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_expr_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (rexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | FLOAT ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState128
                | INT ->
                    _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState128
                | LONG ->
                    _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState128
                | SINGLE ->
                    _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState128
                | VOID ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState128
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | FLOAT ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState256
                | INT ->
                    _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState256
                | LONG ->
                    _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState256
                | SINGLE ->
                    _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState256
                | VOID ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState256
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState256)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState287 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | FLOAT ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState290
                | INT ->
                    _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState290
                | LONG ->
                    _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState290
                | SINGLE ->
                    _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState290
                | VOID ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState290
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState290)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce11 : _menhir_env -> 'ttv_tail * _menhir_state * (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
    let _v : (rexpr) =                                                 ( Rvar(intern_string _1) ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce177 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Cminor.stmt) =                                                 ( Sskip ) in
    _menhir_goto_stmt_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_stmts : _menhir_env -> 'ttv_tail -> _menhir_state -> (Cminor.stmt) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( Slabel (intern_string _1,_3) ) in
        _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
    | MenhirState348 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | EXIT ->
                _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | GOTO ->
                _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | IDENT _v ->
                _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
            | IF ->
                _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LBRACE ->
                _menhir_run349 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LBRACELBRACE ->
                _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LOOP ->
                _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | MATCH ->
                _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | RETURN ->
                _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
            | SWITCH ->
                _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | SWITCHL ->
                _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | TAILCALL ->
                _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | WHILE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState378
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState378)
        | ABSF | AMPERSAND | BANG | BUILTIN | CASE | EXIT | FLOAT | FLOAT32 | FLOAT64 | FLOATLIT _ | FLOATOFINT | FLOATOFINTU | FLOATOFLONG | FLOATOFLONGU | GOTO | IDENT _ | IF | INT | INT16S | INT16U | INT32 | INT64 | INT8S | INT8U | INTLIT _ | INTOFFLOAT | INTOFLONG | INTUOFFLOAT | LBRACELBRACE | LONGLIT _ | LONGOFFLOAT | LONGOFINT | LONGOFINTU | LONGUOFFLOAT | LOOP | LPAREN | MATCH | MINUS | MINUSF | MINUSL | RBRACE | RBRACERBRACE | RETURN | STRINGLIT _ | SWITCH | SWITCHL | TAILCALL | TILDE | TILDEL | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, _3), _, _5) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mkifthenelse _3 _5 Sskip ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState378 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, _3), _, _5), _, _7) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( mkifthenelse _3 _5 _7 ) in
        _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
    | MenhirState343 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( Sloop(_2) ) in
        _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
    | MenhirState284 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, _3), _, _5) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( mkwhile _3 _5 ) in
        _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce133 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((int32 * Cminor.stmt) list) =                                                 ( [] ) in
    _menhir_goto_match_cases _menhir_env _menhir_stack _menhir_s _v

and _menhir_run340 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | EXIT ->
                _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | GOTO ->
                _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | IDENT _v ->
                _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | IF ->
                _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LBRACELBRACE ->
                _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LOOP ->
                _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | MATCH ->
                _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | RETURN ->
                _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState342 _v
            | SWITCH ->
                _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | SWITCHL ->
                _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | TAILCALL ->
                _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | WHILE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | CASE | RBRACE ->
                _menhir_reduce177 _menhir_env (Obj.magic _menhir_stack) MenhirState342
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState342)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run317 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | EXIT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | INTLIT _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | SEMICOLON ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _ = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _4) = _menhir_stack in
                    let _v : ((int32 * int32) list * int32) =            ( ([], _4) ) in
                    _menhir_goto_switch_cases _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run322 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EXIT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | INTLIT _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = (_menhir_stack, _v) in
                    let _tok = _menhir_discard _menhir_env in
                    (match _tok with
                    | SEMICOLON ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _tok = _menhir_discard _menhir_env in
                        (match _tok with
                        | CASE ->
                            _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState327
                        | DEFAULT ->
                            _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState327
                        | _ ->
                            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                            _menhir_env._menhir_shifted <- (-1);
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState327)
                    | _ ->
                        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                        _menhir_env._menhir_shifted <- (-1);
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run298 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | EXIT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | INTLIT _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | SEMICOLON ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _ = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _4) = _menhir_stack in
                    let _v : ((int64 * int32) list * int32) =            ( ([], _4) ) in
                    _menhir_goto_switchl_cases _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run303 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LONGLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EXIT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | INTLIT _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = (_menhir_stack, _v) in
                    let _tok = _menhir_discard _menhir_env in
                    (match _tok with
                    | SEMICOLON ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _tok = _menhir_discard _menhir_env in
                        (match _tok with
                        | CASE ->
                            _menhir_run303 _menhir_env (Obj.magic _menhir_stack) MenhirState308
                        | DEFAULT ->
                            _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState308
                        | _ ->
                            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                            _menhir_env._menhir_shifted <- (-1);
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState308)
                    | _ ->
                        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                        _menhir_env._menhir_shifted <- (-1);
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | IDENT _v ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run285 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState285
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState285

and _menhir_run293 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | IDENT _v ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _v
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState294
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState294)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run312 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | IDENT _v ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState313
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState313)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run331 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | SEMICOLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState331 in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( Sreturn None ) in
        _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState331 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState331
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState331

and _menhir_run335 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | IDENT _v ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _v
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState336 _v
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState336
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState336)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run343 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | EXIT ->
        _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState343 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | GOTO ->
        _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | IDENT _v ->
        _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState343 _v
    | IF ->
        _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState343 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LBRACE ->
        _menhir_run349 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LBRACELBRACE ->
        _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState343 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LOOP ->
        _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | MATCH ->
        _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | RETURN ->
        _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState343 _v
    | SWITCH ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | SWITCHL ->
        _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | TAILCALL ->
        _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | WHILE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState343
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState343

and _menhir_run344 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | EXIT ->
        _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | GOTO ->
        _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | IDENT _v ->
        _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
    | IF ->
        _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LBRACELBRACE ->
        _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LOOP ->
        _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | MATCH ->
        _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | RETURN ->
        _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
    | SWITCH ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | SWITCHL ->
        _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | TAILCALL ->
        _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | WHILE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | RBRACERBRACE ->
        _menhir_reduce177 _menhir_env (Obj.magic _menhir_stack) MenhirState344
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState344

and _menhir_run349 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | EXIT ->
        _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState349 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | GOTO ->
        _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | IDENT _v ->
        _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState349 _v
    | IF ->
        _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState349 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LBRACELBRACE ->
        _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState349 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LOOP ->
        _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | MATCH ->
        _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | RETURN ->
        _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState349 _v
    | SWITCH ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | SWITCHL ->
        _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | TAILCALL ->
        _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | WHILE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | RBRACE ->
        _menhir_reduce177 _menhir_env (Obj.magic _menhir_stack) MenhirState349
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState349

and _menhir_run345 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | IDENT _v ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _v
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState346 _v
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState346
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState346)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run350 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | EXIT ->
            _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | GOTO ->
            _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | IDENT _v ->
            _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _v
        | IF ->
            _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LBRACE ->
            _menhir_run349 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LBRACELBRACE ->
            _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LOOP ->
            _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | MATCH ->
            _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | RETURN ->
            _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState354 _v
        | SWITCH ->
            _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | SWITCHL ->
            _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | TAILCALL ->
            _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | WHILE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState354
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState354)
    | EQUAL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState351 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | IDENT _v ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState351 _v
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState351 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState351 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState351 _v
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState351
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState351)
    | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | LPAREN | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
        _menhir_reduce11 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run355 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _2) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( Sgoto(intern_string _2) ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run358 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _2) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( Sexit (exitnum _2) ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | SEMICOLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( Sexit O ) in
        _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_expr_list_1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (rexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState287 | MenhirState114 | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = _v in
        let _v : (rexpr list) =                                                 ( _1 ) in
        _menhir_goto_expr_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _3 = _v in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (rexpr list) =                                                 ( _1 :: _3 ) in
        _menhir_goto_expr_list_1 _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run122 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState122
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122

and _menhir_run131 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131

and _menhir_run133 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState133
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133

and _menhir_run135 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135

and _menhir_run137 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState137
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137

and _menhir_run139 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139

and _menhir_run141 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState141
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141

and _menhir_run143 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143

and _menhir_reduce100 : _menhir_env -> ('ttv_tail * _menhir_state * (AST.memory_chunk)) * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
    let _v : (rexpr) =                                                 ( Rload(_1, _3) ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run145 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState145
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState145

and _menhir_run155 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155

and _menhir_run157 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState157

and _menhir_run147 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147

and _menhir_run149 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149

and _menhir_run151 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151

and _menhir_run153 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState153
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState153

and _menhir_run159 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159

and _menhir_run161 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161

and _menhir_run163 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState163

and _menhir_run124 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | RPAREN ->
        _menhir_reduce103 _menhir_env (Obj.magic _menhir_stack) MenhirState124
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState124

and _menhir_run165 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165

and _menhir_run179 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179

and _menhir_run167 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState167
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167

and _menhir_run169 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState169

and _menhir_run181 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState181 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState181
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState181

and _menhir_run183 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183

and _menhir_run185 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185

and _menhir_run187 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState187
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187

and _menhir_run189 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState189
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState189

and _menhir_run191 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState191
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191

and _menhir_run193 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState193
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193

and _menhir_run195 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState195
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState195

and _menhir_run197 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState197
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197

and _menhir_run199 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState199
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState199

and _menhir_run201 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState201

and _menhir_run171 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171

and _menhir_run173 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState173
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState173

and _menhir_run175 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState175
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState175

and _menhir_run177 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState177

and _menhir_run203 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState203
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState203

and _menhir_run205 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState205

and _menhir_run207 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState207
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState207

and _menhir_run209 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState209
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState209

and _menhir_run211 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState211
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211

and _menhir_run213 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState213

and _menhir_run215 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState215
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215

and _menhir_run217 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState217

and _menhir_run219 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState219
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219

and _menhir_run221 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState221
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState221

and _menhir_run223 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState223
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223

and _menhir_run225 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225

and _menhir_run229 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState229
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229

and _menhir_run245 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState245
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState245

and _menhir_run247 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState247
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState247

and _menhir_run249 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState249
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState249

and _menhir_run231 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState231
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState231

and _menhir_run233 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState233
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233

and _menhir_run235 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState235
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState235

and _menhir_run237 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState237
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState237

and _menhir_run239 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState239

and _menhir_run241 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState241
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState241

and _menhir_run243 : _menhir_env -> 'ttv_tail * _menhir_state * (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState243
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState243

and _menhir_goto_init_data_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.init_data list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _2), _3), _4), _, _6) = _menhir_stack in
        let _v : (AST.ident * (Cminor.fundef, unit) AST.globdef) =        ( (intern_string _2,
          Gvar{gvar_info = (); gvar_init = List.rev _6;
               gvar_readonly = _3; gvar_volatile = _4; } ) ) in
        _menhir_goto_global_declaration _menhir_env _menhir_stack _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int64) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (AST.init_data) =                                                  ( Init_int64 (coqint_of_camlint64 _1) ) in
    _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _2) = _menhir_stack in
            let _v : (AST.init_data) =                                                  ( Init_space (Z.of_sint32 _2) ) in
            _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int32) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | STRINGLIT _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _ = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _1), _3) = _menhir_stack in
                let _v : (AST.init_data) =                                                  ( Init_addrof (intern_string _3, coqint_of_camlint _1) ) in
                _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | COMMA | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_int32 (coqint_of_camlint _1) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_int8 (coqint_of_camlint _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LONGLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_int64 (coqint_of_camlint64 _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_int32 (coqint_of_camlint _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run28 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_int16 (coqint_of_camlint _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run30 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_int32 (coqint_of_camlint _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run32 : _menhir_env -> 'ttv_tail -> _menhir_state -> (float) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (AST.init_data) =                                                  ( Init_float64 (coqfloat_of_camlfloat _1) ) in
    _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FLOATLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_float64 (coqfloat_of_camlfloat _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FLOATLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_float32 (coqfloat_of_camlfloat _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FLOATLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (AST.init_data) =                                                  ( Init_float64 (coqfloat_of_camlfloat _2) ) in
        _menhir_goto_init_data _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_var_declarations : _menhir_env -> 'ttv_tail -> (Camlcoq.P.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | EXIT ->
        _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | GOTO ->
        _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | IDENT _v ->
        _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
    | IF ->
        _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LBRACELBRACE ->
        _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LOOP ->
        _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | MATCH ->
        _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | RETURN ->
        _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
    | SWITCH ->
        _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | SWITCHL ->
        _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | TAILCALL ->
        _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | VAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState65 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | IDENT _v ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState388)
    | WHILE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | RBRACE ->
        _menhir_reduce177 _menhir_env (Obj.magic _menhir_stack) MenhirState65
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65

and _menhir_run391 : _menhir_env -> 'ttv_tail * _menhir_state * (AST.ident list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _3 = _v in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (AST.ident list) =                                                 ( intern_string _3 :: _1 ) in
        _menhir_goto_parameter_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce103 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (rexpr list) =                                                 ( [] ) in
    _menhir_goto_expr_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run68 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68

and _menhir_run69 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (rexpr) =                                                 ( Rconst(Oaddrsymbol(intern_string _1, Int.zero)) ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71

and _menhir_run72 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73

and _menhir_run74 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState74
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74

and _menhir_run75 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75

and _menhir_run76 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76

and _menhir_run77 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77

and _menhir_run78 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78

and _menhir_run79 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int64) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (rexpr) =                                                 ( longconst _1 ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run80 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState80
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81

and _menhir_run82 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState82
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int32) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (rexpr) =                                                 ( intconst _1 ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run84 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | LBRACKET ->
        _menhir_reduce136 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | LBRACKET ->
        _menhir_reduce135 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85

and _menhir_run88 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | LBRACKET ->
        _menhir_reduce138 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88

and _menhir_run89 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState89
    | LBRACKET ->
        _menhir_reduce137 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89

and _menhir_run91 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce11 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run92 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92

and _menhir_run93 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93

and _menhir_run94 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94

and _menhir_run95 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95

and _menhir_run96 : _menhir_env -> 'ttv_tail -> _menhir_state -> (float) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (rexpr) =                                                 ( Rconst(Ofloatconst (coqfloat_of_camlfloat _1)) ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run98 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | LBRACKET ->
        _menhir_reduce142 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98

and _menhir_run100 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | BUILTIN ->
        _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | EXTERN ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | FLOAT32 ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | IDENT _v ->
        _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT16S ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT16U ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT8S ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INT8U ->
        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | INTLIT _v ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | STRINGLIT _v ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | VOLATILE ->
        _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | LPAREN ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100

and _menhir_run115 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115

and _menhir_run116 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | INTLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _2 = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (rexpr) =                                                 ( Rconst(Oaddrstack(coqint_of_camlint _2)) ) in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run118 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | ABSF ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | AMPERSAND ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | BANG ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | BUILTIN ->
        _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOAT32 ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOATLIT _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | FLOATOFINT ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOATOFINTU ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOATOFLONG ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FLOATOFLONGU ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | IDENT _v ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INT16S ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INT16U ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INT8S ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INT8U ->
        _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INTLIT _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | INTOFFLOAT ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INTOFLONG ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | INTUOFFLOAT ->
        _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LONGLIT _v ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | LONGOFFLOAT ->
        _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LONGOFINT ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LONGOFINTU ->
        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LONGUOFFLOAT ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LPAREN ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | MINUS ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | MINUSF ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | MINUSL ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | STRINGLIT _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | TILDE ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | TILDEL ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118

and _menhir_goto_proc : _menhir_env -> 'ttv_tail -> (AST.ident * (Cminor.fundef, unit) AST.globdef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (AST.ident * (Cminor.fundef, unit) AST.globdef) =       ( _1 ) in
    _menhir_goto_global_declaration _menhir_env _menhir_stack _v

and _menhir_goto_stmt : _menhir_env -> 'ttv_tail -> _menhir_state -> (Cminor.stmt) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState284 | MenhirState343 | MenhirState348 | MenhirState378 | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (Cminor.stmt) =                                                 ( _1 ) in
        _menhir_goto_stmts _menhir_env _menhir_stack _menhir_s _v
    | MenhirState65 | MenhirState342 | MenhirState344 | MenhirState375 | MenhirState349 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ABSF ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | AMPERSAND ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | BANG ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | BUILTIN ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | EXIT ->
            _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOAT ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOAT32 ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOAT64 ->
            _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOATLIT _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
        | FLOATOFINT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOATOFINTU ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOATOFLONG ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | FLOATOFLONGU ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | GOTO ->
            _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | IDENT _v ->
            _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
        | IF ->
            _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT ->
            _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT16S ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT16U ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT32 ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT64 ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT8S ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INT8U ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INTLIT _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
        | INTOFFLOAT ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INTOFLONG ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | INTUOFFLOAT ->
            _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LBRACELBRACE ->
            _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LONGLIT _v ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
        | LONGOFFLOAT ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LONGOFINT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LONGOFINTU ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LONGUOFFLOAT ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LOOP ->
            _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | MATCH ->
            _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | MINUS ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | MINUSF ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | MINUSL ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | RETURN ->
            _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | STRINGLIT _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
        | SWITCH ->
            _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | SWITCHL ->
            _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | TAILCALL ->
            _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | TILDE ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | TILDEL ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | WHILE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | CASE | RBRACE | RBRACERBRACE ->
            _menhir_reduce177 _menhir_env (Obj.magic _menhir_stack) MenhirState375
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState375)
    | _ ->
        _menhir_fail ()

and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (rexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            _menhir_reduce100 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omull, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState287 | MenhirState114 | MenhirState227 | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | IDENT _v ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
            let _v : (rexpr list) =                                                 ( _1 :: [] ) in
            _menhir_goto_expr_list_1 _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omulf, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omul, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Odivu, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Odivlu, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Odivl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Odivf, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Odiv, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState145 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oaddl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omodu, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omodlu, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omodl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Omod, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oaddf, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oadd, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Osubl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Osubf, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Osub, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Clt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oshll, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState169 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oshl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oshru, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oshrlu, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oshrl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oshr, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmplu Clt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpl Clt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpf Clt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Cle, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmplu Cle, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState189 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpl Cle, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState191 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpf Cle, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmp Cle, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState195 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmp Clt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Cgt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmplu Cgt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpl Cgt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpf Cgt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState205 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Cge, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState207 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmplu Cge, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpl Cge, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpf Cge, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState213 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmp Cge, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmp Cgt, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Ceq, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmplu Ceq, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState221 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpl Ceq, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpf Ceq, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmp Ceq, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | BARL | CARET | CARETL | COMMA | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oxorl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState231 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Cne, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmplu Cne, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpl Cne, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState237 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpf Cne, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLU | LESSU | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmp Cne, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState241 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BAR | BARL | CARET | CARETL | COMMA | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oandl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState243 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BAR | BARL | CARET | CARETL | COMMA | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oand, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | BARL | CARET | CARETL | COMMA | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oxor, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | BARL | COMMA | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oorl, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState249 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | BAR | BARL | COMMA | RBRACKET | RPAREN | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Oor, _1, _3) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Oabsf, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Rbinop(Ocmpu Ceq, _2, intconst 0l) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Osingleoffloat, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ofloatofint, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ofloatofintu, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ofloatoflong, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ofloatoflongu, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ocast16signed, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ocast16unsigned, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ocast8signed, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ocast8unsigned, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ointoffloat, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ointoflong, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Ointuoffloat, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Olongoffloat, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Olongofint, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Olongofintu, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Olonguoffloat, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( _2 ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Onegint, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Onegf, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Onegl, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Onotint, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (rexpr) =                                                 ( Runop(Onotl, _2) ) in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | EXIT ->
                _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | GOTO ->
                _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | IDENT _v ->
                _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
            | IF ->
                _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LBRACE ->
                _menhir_run349 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LBRACELBRACE ->
                _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LOOP ->
                _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | MATCH ->
                _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | RETURN ->
                _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
            | SWITCH ->
                _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | SWITCHL ->
                _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | TAILCALL ->
                _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | WHILE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState284
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState284)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState285 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | IDENT _v ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _v
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState287 _v
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | RPAREN ->
                _menhir_reduce103 _menhir_env (Obj.magic _menhir_stack) MenhirState287
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState287)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | LBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | CASE ->
                    _menhir_run303 _menhir_env (Obj.magic _menhir_stack) MenhirState297
                | DEFAULT ->
                    _menhir_run298 _menhir_env (Obj.magic _menhir_stack) MenhirState297
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState297)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | LBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | CASE ->
                    _menhir_run322 _menhir_env (Obj.magic _menhir_stack) MenhirState316
                | DEFAULT ->
                    _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState316
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState316)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mkreturn_some _2 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState336 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | LBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | CASE ->
                    _menhir_run340 _menhir_env (Obj.magic _menhir_stack) MenhirState339
                | RBRACE ->
                    _menhir_reduce133 _menhir_env (Obj.magic _menhir_stack) MenhirState339
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState339)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState346 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | EXIT ->
                _menhir_run358 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | GOTO ->
                _menhir_run355 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | IDENT _v ->
                _menhir_run350 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v
            | IF ->
                _menhir_run345 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LBRACE ->
                _menhir_run349 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LBRACELBRACE ->
                _menhir_run344 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LOOP ->
                _menhir_run343 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | MATCH ->
                _menhir_run335 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | RETURN ->
                _menhir_run331 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState348 _v
            | SWITCH ->
                _menhir_run312 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | SWITCHL ->
                _menhir_run293 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | TAILCALL ->
                _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | WHILE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState348
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState348)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState351 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mkassign (intern_string _1) _3 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState365 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EQUAL ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | ABSF ->
                    _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | AMPERSAND ->
                    _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | BANG ->
                    _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | BUILTIN ->
                    _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOAT ->
                    _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOAT32 ->
                    _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOAT64 ->
                    _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOATLIT _v ->
                    _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
                | FLOATOFINT ->
                    _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOATOFINTU ->
                    _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOATOFLONG ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | FLOATOFLONGU ->
                    _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | IDENT _v ->
                    _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
                | INT ->
                    _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INT16S ->
                    _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INT16U ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INT32 ->
                    _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INT64 ->
                    _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INT8S ->
                    _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INT8U ->
                    _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INTLIT _v ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
                | INTOFFLOAT ->
                    _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INTOFLONG ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | INTUOFFLOAT ->
                    _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | LONGLIT _v ->
                    _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
                | LONGOFFLOAT ->
                    _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | LONGOFINT ->
                    _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | LONGOFINTU ->
                    _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | LONGUOFFLOAT ->
                    _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | LPAREN ->
                    _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | MINUS ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | MINUSF ->
                    _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | MINUSL ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | STRINGLIT _v ->
                    _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState368 _v
                | TILDE ->
                    _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | TILDEL ->
                    _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState368
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState368)
            | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | LPAREN | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
                _menhir_reduce100 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState368 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _1), _, _3), _, _6) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mkstore _1 _3 _6 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState65 | MenhirState284 | MenhirState342 | MenhirState343 | MenhirState344 | MenhirState348 | MenhirState378 | MenhirState349 | MenhirState375 | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AMPERSAND ->
            _menhir_run243 _menhir_env (Obj.magic _menhir_stack)
        | AMPERSANDL ->
            _menhir_run241 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUAL ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALF ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALL ->
            _menhir_run235 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALLU ->
            _menhir_run233 _menhir_env (Obj.magic _menhir_stack)
        | BANGEQUALU ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack)
        | BAR ->
            _menhir_run249 _menhir_env (Obj.magic _menhir_stack)
        | BARL ->
            _menhir_run247 _menhir_env (Obj.magic _menhir_stack)
        | CARET ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack)
        | CARETL ->
            _menhir_run229 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUAL ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALF ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALL ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALLU ->
            _menhir_run219 _menhir_env (Obj.magic _menhir_stack)
        | EQUALEQUALU ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack)
        | GREATER ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUAL ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALF ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALL ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALLU ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
        | GREATEREQUALU ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack)
        | GREATERF ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATER ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERL ->
            _menhir_run175 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERLU ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | GREATERGREATERU ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack)
        | GREATERL ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
        | GREATERLU ->
            _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
        | GREATERU ->
            _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
        | LESS ->
            _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUAL ->
            _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALF ->
            _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALL ->
            _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALLU ->
            _menhir_run187 _menhir_env (Obj.magic _menhir_stack)
        | LESSEQUALU ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack)
        | LESSF ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack)
        | LESSL ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESS ->
            _menhir_run169 _menhir_env (Obj.magic _menhir_stack)
        | LESSLESSL ->
            _menhir_run167 _menhir_env (Obj.magic _menhir_stack)
        | LESSLU ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | LESSU ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | LPAREN ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack)
        | MINUS ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | MINUSF ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | MINUSL ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | PERCENT ->
            _menhir_run153 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTL ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTLU ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack)
        | PERCENTU ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | PLUSF ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | PLUSL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mkeval _1 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | SLASH ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack)
        | SLASHF ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack)
        | SLASHL ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack)
        | SLASHLU ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack)
        | SLASHU ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack)
        | STAR ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack)
        | STARF ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack)
        | STARL ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce101 : _menhir_env -> (('ttv_tail * _menhir_state * (rexpr)) * _menhir_state * (rexpr list)) * _menhir_state * (AST.signature) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, _1), _, _3), _, _6) = _menhir_stack in
    let _v : (rexpr) =                                                 ( Rcall(_6, _1, _3) ) in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_stack_declaration : _menhir_env -> 'ttv_tail -> (Camlcoq.Z.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Camlcoq.P.t list) =                                                 ( [] ) in
    _menhir_goto_var_declarations _menhir_env _menhir_stack _v

and _menhir_goto_is_volatile : _menhir_env -> 'ttv_tail -> (bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | FLOAT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | FLOAT32 ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | FLOAT64 ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | FLOATLIT _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
        | INT ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | INT16 ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | INT32 ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | INT64 ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | INT8 ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | INTLIT _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
        | LBRACKET ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState13
        | LONGLIT _v ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState13 in
            let _v : (AST.init_data list) =                                                 ( [] ) in
            _menhir_goto_init_data_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_goto_parameter_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.ident list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState388 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run391 _menhir_env (Obj.magic _menhir_stack)
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
            let _v : (AST.ident list) =                                                 ( _2 ) in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _2 = _v in
            let (_menhir_stack, _1) = _menhir_stack in
            let _v : (Camlcoq.P.t list) =                                                 ( _2 @ _1 ) in
            _menhir_goto_var_declarations _menhir_env _menhir_stack _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run391 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
            let _v : (AST.ident list) =                                                 ( _1 ) in
            _menhir_goto_parameters _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_eftoks : _menhir_env -> 'ttv_tail -> _menhir_state -> (ef_token list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | IDENT _v ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | RPAREN ->
                _menhir_reduce103 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState258 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _1), _, _2) = _menhir_stack in
        let _v : (ef_token list) =                                                 ( _1 :: _2 ) in
        _menhir_goto_eftoks _menhir_env _menhir_stack _menhir_s _v
    | MenhirState399 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FLOAT ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState401
            | INT ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState401
            | LONG ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState401
            | SINGLE ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState401
            | VOID ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState401
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState401)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce136 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint8unsigned ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce135 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint8signed ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce138 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint16unsigned ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce137 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint16signed ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce142 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mfloat32 ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_memory_chunk : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.memory_chunk) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState399 | MenhirState258 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (ef_token) =                                                 ( EFT_chunk _1 ) in
        _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v
    | MenhirState368 | MenhirState365 | MenhirState351 | MenhirState346 | MenhirState336 | MenhirState331 | MenhirState313 | MenhirState294 | MenhirState287 | MenhirState285 | MenhirState67 | MenhirState68 | MenhirState69 | MenhirState71 | MenhirState72 | MenhirState73 | MenhirState74 | MenhirState75 | MenhirState76 | MenhirState77 | MenhirState78 | MenhirState80 | MenhirState81 | MenhirState82 | MenhirState84 | MenhirState85 | MenhirState88 | MenhirState89 | MenhirState92 | MenhirState93 | MenhirState94 | MenhirState95 | MenhirState98 | MenhirState114 | MenhirState115 | MenhirState249 | MenhirState247 | MenhirState245 | MenhirState243 | MenhirState241 | MenhirState239 | MenhirState237 | MenhirState235 | MenhirState233 | MenhirState231 | MenhirState229 | MenhirState227 | MenhirState225 | MenhirState223 | MenhirState221 | MenhirState219 | MenhirState217 | MenhirState215 | MenhirState213 | MenhirState211 | MenhirState209 | MenhirState207 | MenhirState205 | MenhirState203 | MenhirState201 | MenhirState199 | MenhirState197 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState189 | MenhirState187 | MenhirState185 | MenhirState183 | MenhirState181 | MenhirState179 | MenhirState177 | MenhirState175 | MenhirState173 | MenhirState171 | MenhirState169 | MenhirState167 | MenhirState165 | MenhirState163 | MenhirState161 | MenhirState159 | MenhirState157 | MenhirState155 | MenhirState153 | MenhirState151 | MenhirState149 | MenhirState147 | MenhirState145 | MenhirState143 | MenhirState141 | MenhirState139 | MenhirState137 | MenhirState135 | MenhirState133 | MenhirState131 | MenhirState124 | MenhirState122 | MenhirState120 | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | IDENT _v ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState65 | MenhirState284 | MenhirState342 | MenhirState343 | MenhirState344 | MenhirState348 | MenhirState378 | MenhirState349 | MenhirState375 | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | ABSF ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | AMPERSAND ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | BANG ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | BUILTIN ->
                _menhir_run100 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOAT32 ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOATLIT _v ->
                _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState365 _v
            | FLOATOFINT ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOATOFINTU ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOATOFLONG ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | FLOATOFLONGU ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | IDENT _v ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState365 _v
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INT16S ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INT16U ->
                _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INT8S ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INT8U ->
                _menhir_run84 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INTLIT _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState365 _v
            | INTOFFLOAT ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INTOFLONG ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | INTUOFFLOAT ->
                _menhir_run80 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | LONGLIT _v ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState365 _v
            | LONGOFFLOAT ->
                _menhir_run78 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | LONGOFINT ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | LONGOFINTU ->
                _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | LONGUOFFLOAT ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | LPAREN ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | MINUS ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | MINUSF ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | MINUSL ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | STRINGLIT _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState365 _v
            | TILDE ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | TILDEL ->
                _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState365
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState365)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_eftok : _menhir_env -> 'ttv_tail -> _menhir_state -> (ef_token) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BUILTIN ->
        _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | EXTERN ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | FLOAT ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | FLOAT32 ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | FLOAT64 ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | IDENT _v ->
        _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState258 _v
    | INT ->
        _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INT16S ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INT16U ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INT32 ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INT64 ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INT8S ->
        _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INT8U ->
        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | INTLIT _v ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState258 _v
    | STRINGLIT _v ->
        _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState258 _v
    | VOLATILE ->
        _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | COLON | LPAREN ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState258
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState258

and _menhir_goto_signature : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.signature) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
        let _v : (AST.signature) =                ( let s = _3 in {s with sig_args = _1 :: s.sig_args} ) in
        _menhir_goto_signature _menhir_env _menhir_stack _menhir_s _v
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | STACK ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | INTLIT _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = (_menhir_stack, _v) in
                    let _tok = _menhir_discard _menhir_env in
                    (match _tok with
                    | SEMICOLON ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _ = _menhir_discard _menhir_env in
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (_menhir_stack, _2) = _menhir_stack in
                        let _v : (Camlcoq.Z.t) =                                                 ( Z.of_sint32 _2 ) in
                        _menhir_goto_stack_declaration _menhir_env _menhir_stack _v
                    | _ ->
                        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                        _menhir_env._menhir_shifted <- (-1);
                        let _menhir_stack = Obj.magic _menhir_stack in
                        raise _eRR)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | ABSF | AMPERSAND | BANG | BUILTIN | EXIT | FLOAT | FLOAT32 | FLOAT64 | FLOATLIT _ | FLOATOFINT | FLOATOFINTU | FLOATOFLONG | FLOATOFLONGU | GOTO | IDENT _ | IF | INT | INT16S | INT16U | INT32 | INT64 | INT8S | INT8U | INTLIT _ | INTOFFLOAT | INTOFLONG | INTUOFFLOAT | LBRACELBRACE | LONGLIT _ | LONGOFFLOAT | LONGOFINT | LONGOFINTU | LONGUOFFLOAT | LOOP | LPAREN | MATCH | MINUS | MINUSF | MINUSL | RBRACE | RETURN | STRINGLIT _ | SWITCH | SWITCHL | TAILCALL | TILDE | TILDEL | VAR | WHILE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _v : (Camlcoq.Z.t) =                                                 ( Z0 ) in
                _menhir_goto_stack_declaration _menhir_env _menhir_stack _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce101 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, _2), _, _4), _, _7) = _menhir_stack in
        let _v : (rexpr) =                                                           ( Rbuiltin(_7, _2, _4) ) in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState290 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMICOLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _, _2), _, _4), _, _7) = _menhir_stack in
            let _v : (Cminor.stmt) =                                                 ( mktailcall _7 _2 _4 ) in
            _menhir_goto_stmt _menhir_env _menhir_stack _menhir_s _v
        | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | LPAREN | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL ->
            _menhir_reduce101 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState401 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _2), _, _4), _, _6) = _menhir_stack in
        let _v : (AST.ident * (Cminor.fundef, unit) AST.globdef) =       ( (intern_string _2, Gfun(External(mkef _6 _4))) ) in
        _menhir_goto_proc _menhir_env _menhir_stack _v
    | MenhirState403 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _2), _, _4) = _menhir_stack in
        let _v : (AST.ident * (Cminor.fundef, unit) AST.globdef) =       ( (intern_string _2, Gfun(External(EF_external(intern_string _2,_4)))) ) in
        _menhir_goto_proc _menhir_env _menhir_stack _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_type_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | MINUSGREATER ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | FLOAT ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | INT ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | LONG ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | SINGLE ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | VOID ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState57
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
    | AMPERSAND | AMPERSANDL | BANGEQUAL | BANGEQUALF | BANGEQUALL | BANGEQUALLU | BANGEQUALU | BAR | BARL | CARET | CARETL | COMMA | EOF | EQUALEQUAL | EQUALEQUALF | EQUALEQUALL | EQUALEQUALLU | EQUALEQUALU | EXTERN | GREATER | GREATEREQUAL | GREATEREQUALF | GREATEREQUALL | GREATEREQUALLU | GREATEREQUALU | GREATERF | GREATERGREATER | GREATERGREATERL | GREATERGREATERLU | GREATERGREATERU | GREATERL | GREATERLU | GREATERU | LBRACE | LESS | LESSEQUAL | LESSEQUALF | LESSEQUALL | LESSEQUALLU | LESSEQUALU | LESSF | LESSL | LESSLESS | LESSLESSL | LESSLU | LESSU | LPAREN | MINUS | MINUSF | MINUSL | PERCENT | PERCENTL | PERCENTLU | PERCENTU | PLUS | PLUSF | PLUSL | RBRACKET | RPAREN | SEMICOLON | SLASH | SLASHF | SLASHL | SLASHLU | SLASHU | STAR | STARF | STARL | STRINGLIT _ | VAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
        let _v : (AST.signature) =                ( {sig_args = []; sig_res = Some _1; sig_cc = cc_default} ) in
        _menhir_goto_signature _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_is_readonly : _menhir_env -> 'ttv_tail -> (bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | VOLATILE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _ = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (bool) =                        ( true ) in
        _menhir_goto_is_volatile _menhir_env _menhir_stack _v
    | LBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (bool) =                        ( false ) in
        _menhir_goto_is_volatile _menhir_env _menhir_stack _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_goto_global_declaration : _menhir_env -> 'ttv_tail -> (AST.ident * (Cminor.fundef, unit) AST.globdef) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _2 = _v in
    let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
    let _v : ((AST.ident * (Cminor.fundef, unit) AST.globdef) list) =                                                 ( _2 :: _1 ) in
    _menhir_goto_global_declarations _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_parameters : _menhir_env -> 'ttv_tail -> _menhir_state -> (AST.ident list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FLOAT ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | INT ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | LONG ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | SINGLE ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | VOID ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState50
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run47 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (AST.ident list) =                                                 ( intern_string _1 :: [] ) in
    _menhir_goto_parameter_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (ef_token list) =                                                 ( [] ) in
    _menhir_goto_eftoks _menhir_env _menhir_stack _menhir_s _v

and _menhir_run101 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (ef_token) =                                                 ( EFT_tok "volatile" ) in
    _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v

and _menhir_run102 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (ef_token) =                                                 ( EFT_string _1 ) in
    _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v

and _menhir_run103 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int32) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (ef_token) =                                                 ( EFT_int _1 ) in
    _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v

and _menhir_run104 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce136 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run105 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce135 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run86 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint64 ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_run87 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint32 ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_run106 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce138 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run107 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce137 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run90 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mint32 ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_run108 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (ef_token) =                                                 ( EFT_tok _1 ) in
    _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v

and _menhir_run97 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mfloat64 ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_run109 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce142 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run99 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.memory_chunk) =                                                 ( Mfloat64 ) in
    _menhir_goto_memory_chunk _menhir_env _menhir_stack _menhir_s _v

and _menhir_run110 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (ef_token) =                                                 ( EFT_tok "extern" ) in
    _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v

and _menhir_run111 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (ef_token) =                                                 ( EFT_tok "builtin" ) in
    _menhir_goto_eftok _menhir_env _menhir_stack _menhir_s _v

and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.signature) =                ( {sig_args = []; sig_res = None; sig_cc = cc_default} ) in
    _menhir_goto_signature _menhir_env _menhir_stack _menhir_s _v

and _menhir_run52 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.typ) =                                                 ( Tsingle ) in
    _menhir_goto_type_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run53 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.typ) =                                                 ( Tlong ) in
    _menhir_goto_type_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run54 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.typ) =                                                 ( Tint ) in
    _menhir_goto_type_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run55 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (AST.typ) =                                                 ( Tfloat ) in
    _menhir_goto_type_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_run4 : _menhir_env -> 'ttv_tail -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | STRINGLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | LBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | INTLIT _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | RBRACKET ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _ = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _2), _4) = _menhir_stack in
                    let _v : (AST.ident * (Cminor.fundef, unit) AST.globdef) =       ( (intern_string _2,
         Gvar{gvar_info = (); gvar_init = [Init_space(Z.of_sint32 _4)];
              gvar_readonly = false; gvar_volatile = false}) ) in
                    _menhir_goto_global_declaration _menhir_env _menhir_stack _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let _menhir_stack = Obj.magic _menhir_stack in
                    raise _eRR)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | READONLY ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _v : (bool) =                        ( true ) in
            _menhir_goto_is_readonly _menhir_env _menhir_stack _v
        | LBRACE | VOLATILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _v : (bool) =                        ( false ) in
            _menhir_goto_is_readonly _menhir_env _menhir_stack _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run45 : _menhir_env -> 'ttv_tail -> (string) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | IDENT _v ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState46 in
            let _v : (AST.ident list) =                                                 ( [] ) in
            _menhir_goto_parameters _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run397 : _menhir_env -> 'ttv_tail -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | STRINGLIT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FLOAT ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | INT ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | LONG ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | SINGLE ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | VOID ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState403)
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | BUILTIN ->
                _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | EXTERN ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | FLOAT ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | FLOAT32 ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | FLOAT64 ->
                _menhir_run97 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | IDENT _v ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
            | INT ->
                _menhir_run90 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INT16S ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INT16U ->
                _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INT32 ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INT64 ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INT8S ->
                _menhir_run105 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INT8U ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | INTLIT _v ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
            | STRINGLIT _v ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
            | VOLATILE ->
                _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | COLON ->
                _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState399
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState399)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_goto_prog : _menhir_env -> 'ttv_tail -> _menhir_state -> (Cminor.program) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    Obj.magic _1

and _menhir_goto_global_declarations : _menhir_env -> 'ttv_tail -> _menhir_state -> ((AST.ident * (Cminor.fundef, unit) AST.globdef) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _2), _, _3) = _menhir_stack in
            let _v : (Cminor.program) =       ( { prog_defs = List.rev _3;
          prog_main = intern_string _2; } ) in
            _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v
        | EXTERN ->
            _menhir_run397 _menhir_env (Obj.magic _menhir_stack)
        | STRINGLIT _v ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) _v
        | VAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
            let _v : (Cminor.program) =       ( { prog_defs = List.rev _1;
          prog_main = intern_string "main" } ) in
            _menhir_goto_prog _menhir_env _menhir_stack _menhir_s _v
        | EXTERN ->
            _menhir_run397 _menhir_env (Obj.magic _menhir_stack)
        | STRINGLIT _v ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) _v
        | VAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState403 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState401 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState399 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState388 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState383 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState378 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState375 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState368 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState365 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState354 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState351 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState349 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState348 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState346 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState344 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState343 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState342 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState336 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState331 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState327 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState316 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState308 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState297 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState290 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState287 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState285 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState284 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState258 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState249 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState247 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState243 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState241 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState237 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState231 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState221 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState213 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState207 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState205 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState195 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState191 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState189 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState181 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState169 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState145 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce110 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((AST.ident * (Cminor.fundef, unit) AST.globdef) list) =                                                 ( [] ) in
    _menhir_goto_global_declarations _menhir_env _menhir_stack _menhir_s _v

and _menhir_discard : _menhir_env -> token =
  fun _menhir_env ->
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = _menhir_env._menhir_lexer lexbuf in
    _menhir_env._menhir_token <- _tok;
    _menhir_env._menhir_startp <- lexbuf.Lexing.lex_start_p;
    _menhir_env._menhir_endp <- lexbuf.Lexing.lex_curr_p;
    let shifted = Pervasives.(+) _menhir_env._menhir_shifted 1 in
    if Pervasives.(>=) shifted 0 then
      _menhir_env._menhir_shifted <- shifted;
    _tok

and prog : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Cminor.program) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_startp = lexbuf.Lexing.lex_start_p;
      _menhir_endp = lexbuf.Lexing.lex_curr_p;
      _menhir_shifted = max_int;
      } in
    Obj.magic (let _menhir_stack = () in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQUAL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | STRINGLIT _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _ = _menhir_discard _menhir_env in
            _menhir_reduce110 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | EOF | EXTERN | STRINGLIT _ | VAR ->
        _menhir_reduce110 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)



