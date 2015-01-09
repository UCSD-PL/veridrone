open AST
open BinNums
open Cminor
open CminorSel
open Datatypes
open Errors
open Integers
open Op
open SelectOp

type helper_functions = { i64_dtos : ident; i64_dtou : ident;
                          i64_stod : ident; i64_utod : ident;
                          i64_stof : ident; i64_utof : ident;
                          i64_neg : ident; i64_add : ident; i64_sub : 
                          ident; i64_mul : ident; i64_sdiv : ident;
                          i64_udiv : ident; i64_smod : ident;
                          i64_umod : ident; i64_shl : ident; i64_shr : 
                          ident; i64_sar : ident }

(** val i64_dtos : helper_functions -> ident **)

let i64_dtos x = x.i64_dtos

(** val i64_dtou : helper_functions -> ident **)

let i64_dtou x = x.i64_dtou

(** val i64_stod : helper_functions -> ident **)

let i64_stod x = x.i64_stod

(** val i64_utod : helper_functions -> ident **)

let i64_utod x = x.i64_utod

(** val i64_stof : helper_functions -> ident **)

let i64_stof x = x.i64_stof

(** val i64_utof : helper_functions -> ident **)

let i64_utof x = x.i64_utof

(** val i64_neg : helper_functions -> ident **)

let i64_neg x = x.i64_neg

(** val i64_add : helper_functions -> ident **)

let i64_add x = x.i64_add

(** val i64_sub : helper_functions -> ident **)

let i64_sub x = x.i64_sub

(** val i64_mul : helper_functions -> ident **)

let i64_mul x = x.i64_mul

(** val i64_sdiv : helper_functions -> ident **)

let i64_sdiv x = x.i64_sdiv

(** val i64_udiv : helper_functions -> ident **)

let i64_udiv x = x.i64_udiv

(** val i64_smod : helper_functions -> ident **)

let i64_smod x = x.i64_smod

(** val i64_umod : helper_functions -> ident **)

let i64_umod x = x.i64_umod

(** val i64_shl : helper_functions -> ident **)

let i64_shl x = x.i64_shl

(** val i64_shr : helper_functions -> ident **)

let i64_shr x = x.i64_shr

(** val i64_sar : helper_functions -> ident **)

let i64_sar x = x.i64_sar

(** val sig_l_l : signature **)

let sig_l_l =
  { sig_args = (Tlong :: []); sig_res = (Some Tlong); sig_cc = cc_default }

(** val sig_l_f : signature **)

let sig_l_f =
  { sig_args = (Tlong :: []); sig_res = (Some Tfloat); sig_cc = cc_default }

(** val sig_l_s : signature **)

let sig_l_s =
  { sig_args = (Tlong :: []); sig_res = (Some Tsingle); sig_cc = cc_default }

(** val sig_f_l : signature **)

let sig_f_l =
  { sig_args = (Tfloat :: []); sig_res = (Some Tlong); sig_cc = cc_default }

(** val sig_ll_l : signature **)

let sig_ll_l =
  { sig_args = (Tlong :: (Tlong :: [])); sig_res = (Some Tlong); sig_cc =
    cc_default }

(** val sig_li_l : signature **)

let sig_li_l =
  { sig_args = (Tlong :: (Tint :: [])); sig_res = (Some Tlong); sig_cc =
    cc_default }

(** val sig_ii_l : signature **)

let sig_ii_l =
  { sig_args = (Tint :: (Tint :: [])); sig_res = (Some Tlong); sig_cc =
    cc_default }

(** val makelong : expr -> expr -> expr **)

let makelong h l =
  Eop (Omakelong, (Econs (h, (Econs (l, Enil)))))

type splitlong_cases =
| Coq_splitlong_case1 of expr * expr
| Coq_splitlong_default of expr

(** val splitlong_match : expr -> splitlong_cases **)

let splitlong_match = function
| Eop (o, e0) ->
  (match o with
   | Omakelong ->
     (match e0 with
      | Enil -> Coq_splitlong_default (Eop (Omakelong, Enil))
      | Econs (h, e1) ->
        (match e1 with
         | Enil -> Coq_splitlong_default (Eop (Omakelong, (Econs (h, Enil))))
         | Econs (l, e2) ->
           (match e2 with
            | Enil -> Coq_splitlong_case1 (h, l)
            | Econs (e3, e4) ->
              Coq_splitlong_default (Eop (Omakelong, (Econs (h, (Econs (l,
                (Econs (e3, e4)))))))))))
   | x -> Coq_splitlong_default (Eop (x, e0)))
| x -> Coq_splitlong_default x

(** val splitlong : expr -> (expr -> expr -> expr) -> expr **)

let splitlong e f =
  match splitlong_match e with
  | Coq_splitlong_case1 (h, l) -> f h l
  | Coq_splitlong_default e0 ->
    Elet (e0,
      (f (Eop (Ohighlong, (Econs ((Eletvar O), Enil)))) (Eop (Olowlong,
        (Econs ((Eletvar O), Enil))))))

type splitlong2_cases =
| Coq_splitlong2_case1 of expr * expr * expr * expr
| Coq_splitlong2_case2 of expr * expr * expr
| Coq_splitlong2_case3 of expr * expr * expr
| Coq_splitlong2_default of expr * expr

(** val splitlong2_match : expr -> expr -> splitlong2_cases **)

let splitlong2_match e1 e2 =
  match e1 with
  | Eop (o, e) ->
    (match o with
     | Omakelong ->
       (match e with
        | Enil ->
          let e3 = Eop (Omakelong, Enil) in
          (match e2 with
           | Eop (o0, e0) ->
             (match o0 with
              | Omakelong ->
                (match e0 with
                 | Enil ->
                   Coq_splitlong2_default (e3, (Eop (Omakelong, Enil)))
                 | Econs (h2, e4) ->
                   (match e4 with
                    | Enil ->
                      Coq_splitlong2_default (e3, (Eop (Omakelong, (Econs
                        (h2, Enil)))))
                    | Econs (l2, e5) ->
                      (match e5 with
                       | Enil -> Coq_splitlong2_case3 (e3, h2, l2)
                       | Econs (e6, e7) ->
                         Coq_splitlong2_default (e3, (Eop (Omakelong, (Econs
                           (h2, (Econs (l2, (Econs (e6, e7))))))))))))
              | x -> Coq_splitlong2_default (e3, (Eop (x, e0))))
           | x -> Coq_splitlong2_default (e3, x))
        | Econs (h1, e0) ->
          (match e0 with
           | Enil ->
             let e3 = Eop (Omakelong, (Econs (h1, Enil))) in
             (match e2 with
              | Eop (o0, e4) ->
                (match o0 with
                 | Omakelong ->
                   (match e4 with
                    | Enil ->
                      Coq_splitlong2_default (e3, (Eop (Omakelong, Enil)))
                    | Econs (h2, e5) ->
                      (match e5 with
                       | Enil ->
                         Coq_splitlong2_default (e3, (Eop (Omakelong, (Econs
                           (h2, Enil)))))
                       | Econs (l2, e6) ->
                         (match e6 with
                          | Enil -> Coq_splitlong2_case3 (e3, h2, l2)
                          | Econs (e7, e8) ->
                            Coq_splitlong2_default (e3, (Eop (Omakelong,
                              (Econs (h2, (Econs (l2, (Econs (e7, e8))))))))))))
                 | x -> Coq_splitlong2_default (e3, (Eop (x, e4))))
              | x -> Coq_splitlong2_default (e3, x))
           | Econs (l1, e3) ->
             (match e3 with
              | Enil ->
                (match e2 with
                 | Eop (o0, e4) ->
                   (match o0 with
                    | Omakelong ->
                      (match e4 with
                       | Enil ->
                         Coq_splitlong2_case2 (h1, l1, (Eop (Omakelong,
                           Enil)))
                       | Econs (h2, e5) ->
                         (match e5 with
                          | Enil ->
                            Coq_splitlong2_case2 (h1, l1, (Eop (Omakelong,
                              (Econs (h2, Enil)))))
                          | Econs (l2, e6) ->
                            (match e6 with
                             | Enil -> Coq_splitlong2_case1 (h1, l1, h2, l2)
                             | Econs (e7, e8) ->
                               Coq_splitlong2_case2 (h1, l1, (Eop (Omakelong,
                                 (Econs (h2, (Econs (l2, (Econs (e7,
                                 e8))))))))))))
                    | x -> Coq_splitlong2_case2 (h1, l1, (Eop (x, e4))))
                 | x -> Coq_splitlong2_case2 (h1, l1, x))
              | Econs (e4, e5) ->
                let e6 = Eop (Omakelong, (Econs (h1, (Econs (l1, (Econs (e4,
                  e5)))))))
                in
                (match e2 with
                 | Eop (o0, e7) ->
                   (match o0 with
                    | Omakelong ->
                      (match e7 with
                       | Enil ->
                         Coq_splitlong2_default (e6, (Eop (Omakelong, Enil)))
                       | Econs (h2, e8) ->
                         (match e8 with
                          | Enil ->
                            Coq_splitlong2_default (e6, (Eop (Omakelong,
                              (Econs (h2, Enil)))))
                          | Econs (l2, e9) ->
                            (match e9 with
                             | Enil -> Coq_splitlong2_case3 (e6, h2, l2)
                             | Econs (e10, e11) ->
                               Coq_splitlong2_default (e6, (Eop (Omakelong,
                                 (Econs (h2, (Econs (l2, (Econs (e10,
                                 e11))))))))))))
                    | x -> Coq_splitlong2_default (e6, (Eop (x, e7))))
                 | x -> Coq_splitlong2_default (e6, x)))))
     | x ->
       let e3 = Eop (x, e) in
       (match e2 with
        | Eop (o0, e0) ->
          (match o0 with
           | Omakelong ->
             (match e0 with
              | Enil -> Coq_splitlong2_default (e3, (Eop (Omakelong, Enil)))
              | Econs (h2, e4) ->
                (match e4 with
                 | Enil ->
                   Coq_splitlong2_default (e3, (Eop (Omakelong, (Econs (h2,
                     Enil)))))
                 | Econs (l2, e5) ->
                   (match e5 with
                    | Enil -> Coq_splitlong2_case3 (e3, h2, l2)
                    | Econs (e6, e7) ->
                      Coq_splitlong2_default (e3, (Eop (Omakelong, (Econs
                        (h2, (Econs (l2, (Econs (e6, e7))))))))))))
           | x0 -> Coq_splitlong2_default (e3, (Eop (x0, e0))))
        | x0 -> Coq_splitlong2_default (e3, x0)))
  | x ->
    (match e2 with
     | Eop (o, e) ->
       (match o with
        | Omakelong ->
          (match e with
           | Enil -> Coq_splitlong2_default (x, (Eop (Omakelong, Enil)))
           | Econs (h2, e0) ->
             (match e0 with
              | Enil ->
                Coq_splitlong2_default (x, (Eop (Omakelong, (Econs (h2,
                  Enil)))))
              | Econs (l2, e3) ->
                (match e3 with
                 | Enil -> Coq_splitlong2_case3 (x, h2, l2)
                 | Econs (e4, e5) ->
                   Coq_splitlong2_default (x, (Eop (Omakelong, (Econs (h2,
                     (Econs (l2, (Econs (e4, e5))))))))))))
        | x0 -> Coq_splitlong2_default (x, (Eop (x0, e))))
     | x0 -> Coq_splitlong2_default (x, x0))

(** val splitlong2 :
    expr -> expr -> (expr -> expr -> expr -> expr -> expr) -> expr **)

let splitlong2 e1 e2 f =
  match splitlong2_match e1 e2 with
  | Coq_splitlong2_case1 (h1, l1, h2, l2) -> f h1 l1 h2 l2
  | Coq_splitlong2_case2 (h1, l1, t2) ->
    Elet (t2,
      (f (lift h1) (lift l1) (Eop (Ohighlong, (Econs ((Eletvar O), Enil))))
        (Eop (Olowlong, (Econs ((Eletvar O), Enil))))))
  | Coq_splitlong2_case3 (t1, h2, l2) ->
    Elet (t1,
      (f (Eop (Ohighlong, (Econs ((Eletvar O), Enil)))) (Eop (Olowlong,
        (Econs ((Eletvar O), Enil)))) (lift h2) (lift l2)))
  | Coq_splitlong2_default (e3, e4) ->
    Elet (e3, (Elet ((lift e4),
      (f (Eop (Ohighlong, (Econs ((Eletvar (S O)), Enil)))) (Eop (Olowlong,
        (Econs ((Eletvar (S O)), Enil)))) (Eop (Ohighlong, (Econs ((Eletvar
        O), Enil)))) (Eop (Olowlong, (Econs ((Eletvar O), Enil))))))))

type lowlong_cases =
| Coq_lowlong_case1 of expr * expr
| Coq_lowlong_default of expr

(** val lowlong_match : expr -> lowlong_cases **)

let lowlong_match = function
| Eop (o, e0) ->
  (match o with
   | Omakelong ->
     (match e0 with
      | Enil -> Coq_lowlong_default (Eop (Omakelong, Enil))
      | Econs (e1, e2) ->
        (match e2 with
         | Enil -> Coq_lowlong_default (Eop (Omakelong, (Econs (e1, Enil))))
         | Econs (e3, e4) ->
           (match e4 with
            | Enil -> Coq_lowlong_case1 (e1, e3)
            | Econs (e5, e6) ->
              Coq_lowlong_default (Eop (Omakelong, (Econs (e1, (Econs (e3,
                (Econs (e5, e6)))))))))))
   | x -> Coq_lowlong_default (Eop (x, e0)))
| x -> Coq_lowlong_default x

(** val lowlong : expr -> expr **)

let lowlong e =
  match lowlong_match e with
  | Coq_lowlong_case1 (e1, e2) -> e2
  | Coq_lowlong_default e0 -> Eop (Olowlong, (Econs (e0, Enil)))

type highlong_cases =
| Coq_highlong_case1 of expr * expr
| Coq_highlong_default of expr

(** val highlong_match : expr -> highlong_cases **)

let highlong_match = function
| Eop (o, e0) ->
  (match o with
   | Omakelong ->
     (match e0 with
      | Enil -> Coq_highlong_default (Eop (Omakelong, Enil))
      | Econs (e1, e2) ->
        (match e2 with
         | Enil -> Coq_highlong_default (Eop (Omakelong, (Econs (e1, Enil))))
         | Econs (e3, e4) ->
           (match e4 with
            | Enil -> Coq_highlong_case1 (e1, e3)
            | Econs (e5, e6) ->
              Coq_highlong_default (Eop (Omakelong, (Econs (e1, (Econs (e3,
                (Econs (e5, e6)))))))))))
   | x -> Coq_highlong_default (Eop (x, e0)))
| x -> Coq_highlong_default x

(** val highlong : expr -> expr **)

let highlong e =
  match highlong_match e with
  | Coq_highlong_case1 (e1, e2) -> e1
  | Coq_highlong_default e0 -> Eop (Ohighlong, (Econs (e0, Enil)))

(** val longconst : Int64.int -> expr **)

let longconst n =
  makelong (Eop ((Ointconst (Int64.hiword n)), Enil)) (Eop ((Ointconst
    (Int64.loword n)), Enil))

type is_longconst_cases =
| Coq_is_longconst_case1 of Int.int * Int.int
| Coq_is_longconst_default of expr

(** val is_longconst_match : expr -> is_longconst_cases **)

let is_longconst_match = function
| Eop (o, e0) ->
  (match o with
   | Omakelong ->
     (match e0 with
      | Enil -> Coq_is_longconst_default (Eop (Omakelong, Enil))
      | Econs (e1, e2) ->
        (match e1 with
         | Eop (o0, e3) ->
           (match o0 with
            | Ointconst h ->
              (match e3 with
               | Enil ->
                 (match e2 with
                  | Enil ->
                    Coq_is_longconst_default (Eop (Omakelong, (Econs ((Eop
                      ((Ointconst h), Enil)), Enil))))
                  | Econs (e4, e5) ->
                    (match e4 with
                     | Eop (o1, e6) ->
                       (match o1 with
                        | Ointconst l ->
                          (match e6 with
                           | Enil ->
                             (match e5 with
                              | Enil -> Coq_is_longconst_case1 (h, l)
                              | Econs (e7, e8) ->
                                Coq_is_longconst_default (Eop (Omakelong,
                                  (Econs ((Eop ((Ointconst h), Enil)), (Econs
                                  ((Eop ((Ointconst l), Enil)), (Econs (e7,
                                  e8)))))))))
                           | Econs (e7, e8) ->
                             Coq_is_longconst_default (Eop (Omakelong, (Econs
                               ((Eop ((Ointconst h), Enil)), (Econs ((Eop
                               ((Ointconst l), (Econs (e7, e8)))), e5)))))))
                        | Omakelong ->
                          Coq_is_longconst_default (Eop (Omakelong, (Econs
                            ((Eop ((Ointconst h), Enil)), (Econs ((Eop
                            (Omakelong, e6)), e5))))))
                        | x ->
                          Coq_is_longconst_default (Eop (Omakelong, (Econs
                            ((Eop ((Ointconst h), Enil)), (Econs ((Eop (x,
                            e6)), e5)))))))
                     | x ->
                       Coq_is_longconst_default (Eop (Omakelong, (Econs ((Eop
                         ((Ointconst h), Enil)), (Econs (x, e5))))))))
               | Econs (e4, e5) ->
                 Coq_is_longconst_default (Eop (Omakelong, (Econs ((Eop
                   ((Ointconst h), (Econs (e4, e5)))), e2)))))
            | Omakelong ->
              Coq_is_longconst_default (Eop (Omakelong, (Econs ((Eop
                (Omakelong, e3)), e2))))
            | x ->
              Coq_is_longconst_default (Eop (Omakelong, (Econs ((Eop (x,
                e3)), e2)))))
         | x -> Coq_is_longconst_default (Eop (Omakelong, (Econs (x, e2))))))
   | x -> Coq_is_longconst_default (Eop (x, e0)))
| x -> Coq_is_longconst_default x

(** val is_longconst : expr -> Int64.int option **)

let is_longconst e =
  match is_longconst_match e with
  | Coq_is_longconst_case1 (h, l) -> Some (Int64.ofwords h l)
  | Coq_is_longconst_default e0 -> None

(** val is_longconst_zero : expr -> bool **)

let is_longconst_zero e =
  match is_longconst e with
  | Some n -> Int64.eq n Int64.zero
  | None -> false

(** val intoflong : expr -> expr **)

let intoflong e =
  lowlong e

(** val longofint : expr -> expr **)

let longofint e =
  Elet (e,
    (makelong
      (shrimm (Eletvar O)
        (Int.repr (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))))
      (Eletvar O)))

(** val longofintu : expr -> expr **)

let longofintu e =
  makelong (Eop ((Ointconst Int.zero), Enil)) e

(** val negl : helper_functions -> expr -> expr **)

let negl hf e =
  match is_longconst e with
  | Some n -> longconst (Int64.neg n)
  | None -> Ebuiltin ((EF_builtin (hf.i64_neg, sig_l_l)), (Econs (e, Enil)))

(** val notl : expr -> expr **)

let notl e =
  splitlong e (fun h l -> makelong (notint h) (notint l))

(** val longoffloat : helper_functions -> expr -> expr **)

let longoffloat hf arg =
  Eexternal (hf.i64_dtos, sig_f_l, (Econs (arg, Enil)))

(** val longuoffloat : helper_functions -> expr -> expr **)

let longuoffloat hf arg =
  Eexternal (hf.i64_dtou, sig_f_l, (Econs (arg, Enil)))

(** val floatoflong : helper_functions -> expr -> expr **)

let floatoflong hf arg =
  Eexternal (hf.i64_stod, sig_l_f, (Econs (arg, Enil)))

(** val floatoflongu : helper_functions -> expr -> expr **)

let floatoflongu hf arg =
  Eexternal (hf.i64_utod, sig_l_f, (Econs (arg, Enil)))

(** val longofsingle : helper_functions -> expr -> expr **)

let longofsingle hf arg =
  longoffloat hf (floatofsingle arg)

(** val longuofsingle : helper_functions -> expr -> expr **)

let longuofsingle hf arg =
  longuoffloat hf (floatofsingle arg)

(** val singleoflong : helper_functions -> expr -> expr **)

let singleoflong hf arg =
  Eexternal (hf.i64_stof, sig_l_s, (Econs (arg, Enil)))

(** val singleoflongu : helper_functions -> expr -> expr **)

let singleoflongu hf arg =
  Eexternal (hf.i64_utof, sig_l_s, (Econs (arg, Enil)))

(** val andl : expr -> expr -> expr **)

let andl e1 e2 =
  splitlong2 e1 e2 (fun h1 l1 h2 l2 ->
    makelong (coq_and h1 h2) (coq_and l1 l2))

(** val orl : expr -> expr -> expr **)

let orl e1 e2 =
  splitlong2 e1 e2 (fun h1 l1 h2 l2 ->
    makelong (coq_or h1 h2) (coq_or l1 l2))

(** val xorl : expr -> expr -> expr **)

let xorl e1 e2 =
  splitlong2 e1 e2 (fun h1 l1 h2 l2 -> makelong (xor h1 h2) (xor l1 l2))

(** val shllimm : helper_functions -> expr -> Int.int -> expr **)

let shllimm hf e1 n =
  if Int.eq n Int.zero
  then e1
  else if Int.ltu n Int.iwordsize
       then splitlong e1 (fun h l ->
              makelong
                (coq_or (shlimm h n) (shruimm l (Int.sub Int.iwordsize n)))
                (shlimm l n))
       else if Int.ltu n Int64.iwordsize'
            then makelong (shlimm (lowlong e1) (Int.sub n Int.iwordsize))
                   (Eop ((Ointconst Int.zero), Enil))
            else Eexternal (hf.i64_shl, sig_li_l, (Econs (e1, (Econs ((Eop
                   ((Ointconst n), Enil)), Enil)))))

(** val shrluimm : helper_functions -> expr -> Int.int -> expr **)

let shrluimm hf e1 n =
  if Int.eq n Int.zero
  then e1
  else if Int.ltu n Int.iwordsize
       then splitlong e1 (fun h l ->
              makelong (shruimm h n)
                (coq_or (shruimm l n) (shlimm h (Int.sub Int.iwordsize n))))
       else if Int.ltu n Int64.iwordsize'
            then makelong (Eop ((Ointconst Int.zero), Enil))
                   (shruimm (highlong e1) (Int.sub n Int.iwordsize))
            else Eexternal (hf.i64_shr, sig_li_l, (Econs (e1, (Econs ((Eop
                   ((Ointconst n), Enil)), Enil)))))

(** val shrlimm : helper_functions -> expr -> Int.int -> expr **)

let shrlimm hf e1 n =
  if Int.eq n Int.zero
  then e1
  else if Int.ltu n Int.iwordsize
       then splitlong e1 (fun h l ->
              makelong (shrimm h n)
                (coq_or (shruimm l n) (shlimm h (Int.sub Int.iwordsize n))))
       else if Int.ltu n Int64.iwordsize'
            then Elet ((highlong e1),
                   (makelong
                     (shrimm (Eletvar O)
                       (Int.repr (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI
                         Coq_xH)))))))
                     (shrimm (Eletvar O) (Int.sub n Int.iwordsize))))
            else Eexternal (hf.i64_sar, sig_li_l, (Econs (e1, (Econs ((Eop
                   ((Ointconst n), Enil)), Enil)))))

(** val is_intconst : expr -> Int.int option **)

let is_intconst = function
| Eop (o, e0) ->
  (match o with
   | Ointconst n ->
     (match e0 with
      | Enil -> Some n
      | Econs (e1, e2) -> None)
   | _ -> None)
| _ -> None

(** val shll : helper_functions -> expr -> expr -> expr **)

let shll hf e1 e2 =
  match is_intconst e2 with
  | Some n -> shllimm hf e1 n
  | None ->
    Eexternal (hf.i64_shl, sig_li_l, (Econs (e1, (Econs (e2, Enil)))))

(** val shrlu : helper_functions -> expr -> expr -> expr **)

let shrlu hf e1 e2 =
  match is_intconst e2 with
  | Some n -> shrluimm hf e1 n
  | None ->
    Eexternal (hf.i64_shr, sig_li_l, (Econs (e1, (Econs (e2, Enil)))))

(** val shrl : helper_functions -> expr -> expr -> expr **)

let shrl hf e1 e2 =
  match is_intconst e2 with
  | Some n -> shrlimm hf e1 n
  | None ->
    Eexternal (hf.i64_sar, sig_li_l, (Econs (e1, (Econs (e2, Enil)))))

(** val addl : helper_functions -> expr -> expr -> expr **)

let addl hf e1 e2 =
  let default = Ebuiltin ((EF_builtin (hf.i64_add, sig_ll_l)), (Econs (e1,
    (Econs (e2, Enil)))))
  in
  (match is_longconst e1 with
   | Some n1 ->
     (match is_longconst e2 with
      | Some n2 -> longconst (Int64.add n1 n2)
      | None -> if Int64.eq n1 Int64.zero then e2 else default)
   | None ->
     (match is_longconst e2 with
      | Some n2 -> if Int64.eq n2 Int64.zero then e1 else default
      | None -> default))

(** val subl : helper_functions -> expr -> expr -> expr **)

let subl hf e1 e2 =
  let default = Ebuiltin ((EF_builtin (hf.i64_sub, sig_ll_l)), (Econs (e1,
    (Econs (e2, Enil)))))
  in
  (match is_longconst e1 with
   | Some n1 ->
     (match is_longconst e2 with
      | Some n2 -> longconst (Int64.sub n1 n2)
      | None -> if Int64.eq n1 Int64.zero then negl hf e2 else default)
   | None ->
     (match is_longconst e2 with
      | Some n2 -> if Int64.eq n2 Int64.zero then e1 else default
      | None -> default))

(** val mull_base : helper_functions -> expr -> expr -> expr **)

let mull_base hf e1 e2 =
  splitlong2 e1 e2 (fun h1 l1 h2 l2 -> Elet ((Ebuiltin ((EF_builtin
    (hf.i64_mul, sig_ii_l)), (Econs (l1, (Econs (l2, Enil)))))),
    (makelong
      (add
        (add (Eop (Ohighlong, (Econs ((Eletvar O), Enil))))
          (mul (lift l1) (lift h2))) (mul (lift h1) (lift l2))) (Eop
      (Olowlong, (Econs ((Eletvar O), Enil)))))))

(** val mullimm : helper_functions -> expr -> Int64.int -> expr **)

let mullimm hf e n =
  if Int64.eq n Int64.zero
  then longconst Int64.zero
  else if Int64.eq n Int64.one
       then e
       else (match Int64.is_power2 n with
             | Some l -> shllimm hf e (Int.repr (Int64.unsigned l))
             | None -> mull_base hf e (longconst n))

(** val mull : helper_functions -> expr -> expr -> expr **)

let mull hf e1 e2 =
  match is_longconst e1 with
  | Some n1 ->
    (match is_longconst e2 with
     | Some n2 -> longconst (Int64.mul n1 n2)
     | None -> mullimm hf e2 n1)
  | None ->
    (match is_longconst e2 with
     | Some n2 -> mullimm hf e1 n2
     | None -> mull_base hf e1 e2)

(** val binop_long :
    ident -> (Int64.int -> Int64.int -> Int64.int) -> expr -> expr -> expr **)

let binop_long id sem e1 e2 =
  match is_longconst e1 with
  | Some n1 ->
    (match is_longconst e2 with
     | Some n2 -> longconst (sem n1 n2)
     | None -> Eexternal (id, sig_ll_l, (Econs (e1, (Econs (e2, Enil))))))
  | None -> Eexternal (id, sig_ll_l, (Econs (e1, (Econs (e2, Enil)))))

(** val divl : helper_functions -> expr -> expr -> expr **)

let divl hf =
  binop_long hf.i64_sdiv Int64.divs

(** val modl : helper_functions -> expr -> expr -> expr **)

let modl hf =
  binop_long hf.i64_smod Int64.mods

(** val divlu : helper_functions -> expr -> expr -> expr **)

let divlu hf e1 e2 =
  let default = Eexternal (hf.i64_udiv, sig_ll_l, (Econs (e1, (Econs (e2,
    Enil)))))
  in
  (match is_longconst e1 with
   | Some n1 ->
     (match is_longconst e2 with
      | Some n2 -> longconst (Int64.divu n1 n2)
      | None -> default)
   | None ->
     (match is_longconst e2 with
      | Some n2 ->
        (match Int64.is_power2 n2 with
         | Some l -> shrluimm hf e1 (Int.repr (Int64.unsigned l))
         | None -> default)
      | None -> default))

(** val modlu : helper_functions -> expr -> expr -> expr **)

let modlu hf e1 e2 =
  let default = Eexternal (hf.i64_umod, sig_ll_l, (Econs (e1, (Econs (e2,
    Enil)))))
  in
  (match is_longconst e1 with
   | Some n1 ->
     (match is_longconst e2 with
      | Some n2 -> longconst (Int64.modu n1 n2)
      | None -> default)
   | None ->
     (match is_longconst e2 with
      | Some n2 ->
        (match Int64.is_power2 n2 with
         | Some l -> andl e1 (longconst (Int64.sub n2 Int64.one))
         | None -> default)
      | None -> default))

(** val cmpl_eq_zero : expr -> expr **)

let cmpl_eq_zero e =
  splitlong e (fun h l ->
    comp Ceq (coq_or h l) (Eop ((Ointconst Int.zero), Enil)))

(** val cmpl_ne_zero : expr -> expr **)

let cmpl_ne_zero e =
  splitlong e (fun h l ->
    comp Cne (coq_or h l) (Eop ((Ointconst Int.zero), Enil)))

(** val cmplu_gen : comparison -> comparison -> expr -> expr -> expr **)

let cmplu_gen ch cl e1 e2 =
  splitlong2 e1 e2 (fun h1 l1 h2 l2 -> Econdition ((CEcond ((Ccomp Ceq),
    (Econs (h1, (Econs (h2, Enil)))))), (Eop ((Ocmp (Ccompu cl)), (Econs (l1,
    (Econs (l2, Enil)))))), (Eop ((Ocmp (Ccompu ch)), (Econs (h1, (Econs (h2,
    Enil))))))))

(** val cmplu : comparison -> expr -> expr -> expr **)

let cmplu c e1 e2 =
  match c with
  | Ceq -> cmpl_eq_zero (xorl e1 e2)
  | Cne -> cmpl_ne_zero (xorl e1 e2)
  | Cle -> cmplu_gen Clt Cle e1 e2
  | Cge -> cmplu_gen Cgt Cge e1 e2
  | x -> cmplu_gen x x e1 e2

(** val cmpl_gen : comparison -> comparison -> expr -> expr -> expr **)

let cmpl_gen ch cl e1 e2 =
  splitlong2 e1 e2 (fun h1 l1 h2 l2 -> Econdition ((CEcond ((Ccomp Ceq),
    (Econs (h1, (Econs (h2, Enil)))))), (Eop ((Ocmp (Ccompu cl)), (Econs (l1,
    (Econs (l2, Enil)))))), (Eop ((Ocmp (Ccomp ch)), (Econs (h1, (Econs (h2,
    Enil))))))))

(** val cmpl : comparison -> expr -> expr -> expr **)

let cmpl c e1 e2 =
  match c with
  | Ceq -> cmpl_eq_zero (xorl e1 e2)
  | Cne -> cmpl_ne_zero (xorl e1 e2)
  | Clt ->
    if is_longconst_zero e2
    then comp Clt (highlong e1) (Eop ((Ointconst Int.zero), Enil))
    else cmpl_gen Clt Clt e1 e2
  | Cle -> cmpl_gen Clt Cle e1 e2
  | Cgt -> cmpl_gen Cgt Cgt e1 e2
  | Cge ->
    if is_longconst_zero e2
    then comp Cge (highlong e1) (Eop ((Ointconst Int.zero), Enil))
    else cmpl_gen Cgt Cge e1 e2

(** val get_helper : genv -> char list -> signature -> ident res **)

let get_helper = fun ge s sg ->
     Errors.OK (Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s))

(** val get_builtin : char list -> signature -> ident res **)

let get_builtin = fun s sg ->
     Errors.OK (Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s))

(** val get_helpers : genv -> helper_functions res **)

let get_helpers ge =
  match get_helper ge
          ('_'::('_'::('i'::('6'::('4'::('_'::('d'::('t'::('o'::('s'::[]))))))))))
          sig_f_l with
  | OK x ->
    (match get_helper ge
             ('_'::('_'::('i'::('6'::('4'::('_'::('d'::('t'::('o'::('u'::[]))))))))))
             sig_f_l with
     | OK x0 ->
       (match get_helper ge
                ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('t'::('o'::('d'::[]))))))))))
                sig_l_f with
        | OK x1 ->
          (match get_helper ge
                   ('_'::('_'::('i'::('6'::('4'::('_'::('u'::('t'::('o'::('d'::[]))))))))))
                   sig_l_f with
           | OK x2 ->
             (match get_helper ge
                      ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('t'::('o'::('f'::[]))))))))))
                      sig_l_s with
              | OK x3 ->
                (match get_helper ge
                         ('_'::('_'::('i'::('6'::('4'::('_'::('u'::('t'::('o'::('f'::[]))))))))))
                         sig_l_s with
                 | OK x4 ->
                   (match get_builtin
                            ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('n'::('e'::('g'::('l'::[]))))))))))))))
                            sig_l_l with
                    | OK x5 ->
                      (match get_builtin
                               ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('a'::('d'::('d'::('l'::[]))))))))))))))
                               sig_ll_l with
                       | OK x6 ->
                         (match get_builtin
                                  ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('s'::('u'::('b'::('l'::[]))))))))))))))
                                  sig_ll_l with
                          | OK x7 ->
                            (match get_builtin
                                     ('_'::('_'::('b'::('u'::('i'::('l'::('t'::('i'::('n'::('_'::('m'::('u'::('l'::('l'::[]))))))))))))))
                                     sig_ll_l with
                             | OK x8 ->
                               (match get_helper ge
                                        ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('d'::('i'::('v'::[]))))))))))
                                        sig_ll_l with
                                | OK x9 ->
                                  (match get_helper ge
                                           ('_'::('_'::('i'::('6'::('4'::('_'::('u'::('d'::('i'::('v'::[]))))))))))
                                           sig_ll_l with
                                   | OK x10 ->
                                     (match get_helper ge
                                              ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('m'::('o'::('d'::[]))))))))))
                                              sig_ll_l with
                                      | OK x11 ->
                                        (match get_helper ge
                                                 ('_'::('_'::('i'::('6'::('4'::('_'::('u'::('m'::('o'::('d'::[]))))))))))
                                                 sig_ll_l with
                                         | OK x12 ->
                                           (match get_helper ge
                                                    ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('h'::('l'::[])))))))))
                                                    sig_li_l with
                                            | OK x13 ->
                                              (match get_helper ge
                                                       ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('h'::('r'::[])))))))))
                                                       sig_li_l with
                                               | OK x14 ->
                                                 (match get_helper ge
                                                          ('_'::('_'::('i'::('6'::('4'::('_'::('s'::('a'::('r'::[])))))))))
                                                          sig_li_l with
                                                  | OK x15 ->
                                                    OK { i64_dtos = x;
                                                      i64_dtou = x0;
                                                      i64_stod = x1;
                                                      i64_utod = x2;
                                                      i64_stof = x3;
                                                      i64_utof = x4;
                                                      i64_neg = x5; i64_add =
                                                      x6; i64_sub = x7;
                                                      i64_mul = x8;
                                                      i64_sdiv = x9;
                                                      i64_udiv = x10;
                                                      i64_smod = x11;
                                                      i64_umod = x12;
                                                      i64_shl = x13;
                                                      i64_shr = x14;
                                                      i64_sar = x15 }
                                                  | Error msg -> Error msg)
                                               | Error msg -> Error msg)
                                            | Error msg -> Error msg)
                                         | Error msg -> Error msg)
                                      | Error msg -> Error msg)
                                   | Error msg -> Error msg)
                                | Error msg -> Error msg)
                             | Error msg -> Error msg)
                          | Error msg -> Error msg)
                       | Error msg -> Error msg)
                    | Error msg -> Error msg)
                 | Error msg -> Error msg)
              | Error msg -> Error msg)
           | Error msg -> Error msg)
        | Error msg -> Error msg)
     | Error msg -> Error msg)
  | Error msg -> Error msg

