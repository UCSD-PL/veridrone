open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors
open Marshal
open Tactics

(*open Plugin_utils*)

open Pretty.PrintClight
open Pretty.AST

(* first, we need to convert Term.constr into
   (Pretty.Clight.fundef, Pretty.Ctypes.coq_type) Pretty.AST.program 
   
    this is weird voodoo code I got from 
    https://github.com/gmalecha/mirror-core/blob/master/src/reify_lambda_shell.ml4#L277
    I don't fully understand it...*)

(****************************************************************************
   first things first, though, we need some term utilities
   (direct copy-paste from
   https://github.com/gmalecha/coq-plugin-utils/blob/master/src/term_match.ml)
  ****************************************************************************)

type ('a,'b,'c) pattern =
| Glob of Term.constr Lazy.t
| EGlob of Term.constr
| App of ('a,'b,'c) pattern * ('a,'b,'c) pattern
| Lam of 'b * ('a,'b,'c) pattern * ('a,'b,'c) pattern
| As of ('a,'b,'c) pattern * 'a
| Ref of 'b
| Choice of (('a,'b,'c) pattern) list
| Impl of ('a,'b,'c) pattern * ('a,'b,'c) pattern
| Pi of ('a,'b,'c) pattern * ('a,'b,'c) pattern
| Ignore
| Filter of ('c -> Term.constr -> bool) * ('a,'b,'c) pattern

exception Match_failure

let rec apps f ls =
  match ls with
    [] -> f
  | l :: ls ->
    apps (App (f,l)) ls

let get x =
  As (Ignore, x)


(** NOTE: This function does not clear writes by failed choices **)
let rec match_pattern p e ctx s =
  match p with
  | Ignore -> s
  | Glob name ->
    begin
      if Term.eq_constr (Lazy.force name) e
      then
	s
      else
	raise Match_failure
    end
  | EGlob name ->
    begin
      if Term.eq_constr name e
      then
	s
      else
	raise Match_failure
    end
  | Filter (f, p) ->
    if f ctx e then match_pattern p e ctx s else raise Match_failure
  | Choice pl ->
    begin
      let rec try_each pl =
	match pl with
	  [] -> raise Match_failure
	| p :: pl ->
	  try
	    match_pattern p e ctx s
	  with
	    Match_failure -> try_each pl
      in try_each pl
    end
  | App _ ->
    begin
      match Term.kind_of_term e with
      | Term.App (f, args) ->
	  match_app f args (Array.length args - 1) p ctx s
      | _ -> raise Match_failure
    end
  | Lam (nm, pty, pbody) ->
    begin
      match Term.kind_of_term e with
      | Term.Lambda (n, t, c) ->
	let _ = match_pattern pty t ctx s in
	match_pattern pbody c ctx s
      | _ -> raise Match_failure
    end
  | As (ptrn, nm) ->
    begin
      let res = match_pattern ptrn e ctx s in
      let _ = Hashtbl.add res nm e in
      res
    end
  | Impl (l,r) ->
    begin
      match Term.kind_of_term e with
	Term.Prod (_, lhs, rhs) ->
	  if Term.noccurn 1 rhs then
	    let _ = match_pattern l lhs ctx s in
	    match_pattern r rhs ctx s
	  else
	    raise Match_failure
      | _ -> raise Match_failure
    end
  | Pi (l,r) ->
    begin
      match Term.kind_of_term e with
	Term.Prod (_, lhs, rhs) ->
	  let _ = match_pattern l lhs ctx s in
	  match_pattern r rhs ctx s
      | _ -> raise Match_failure
    end
  | Ref n ->
    assert false
and match_app f args i p ctx s =
  if i < 0
  then match_pattern p f ctx s
  else
    match p with
      App (fp , arg_p) ->
	let s = match_app f args (i - 1) fp ctx s in
	match_pattern arg_p args.(i) ctx s
    | _ ->
      match_pattern p (Term.mkApp (f, Array.sub args 0 (i + 1))) ctx s

let matches gl ls e =
  let x = Hashtbl.create 5 in
  let rec recur ls =
    match ls with
    | [] -> raise Match_failure
    | (p,f) :: ls ->
      try
	f gl (match_pattern p e gl x)
      with
	Match_failure ->
	  let _ = Hashtbl.clear x in
	  recur ls
  in
  recur ls

let matches_app gl ls e args from =
  let x = Hashtbl.create 5 in
  let rec recur ls =
    match ls with
    | [] -> raise Match_failure
    | (p,f) :: ls ->
      try
	f gl (match_app e args from p gl x)
      with
	Match_failure ->
	  let _ = Hashtbl.clear x in
	  recur ls
  in
  recur ls

let dbg msg =
  Format.printf "%s\n" msg


(****************************************************************************
   end of copy-paste
 ****************************************************************************)


(****************************************************************************
   Begin copy-paste from
https://raw.githubusercontent.com/gmalecha/coq-plugin-utils/master/src/coqstd.ml
 ****************************************************************************)

module StdT (C : sig val contrib_name : string end) =
struct
  type coq_term = Term.constr
  type coq_type = Term.constr

  let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    let re = Coqlib.find_reference C.contrib_name path tm in
    Libnames.constr_of_global re

  let rec app_full trm acc =
    match Term.kind_of_term trm with
      Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)

  let bad_arg msg trm =
    let _ = Format.eprintf "\n%s: %a\n" msg pp_constr trm in
    raise (Invalid_argument msg)


  let datatypes_pkg = ["Coq";"Init";"Datatypes"]
  let bignums_pkg = ["Coq";"Numbers";"BinNums"]
  let specif_pkg = ["Coq";"Init";"Specif"]

  module Unit =
  struct
    let tt = lazy (resolve_symbol datatypes_pkg "tt")
    let unit = lazy (resolve_symbol datatypes_pkg "unit")
  end

  module Positive =
  struct

    let pos_type = lazy (resolve_symbol bignums_pkg "positive")

    let to_positive =
      let xH = lazy (resolve_symbol bignums_pkg "xH") in
      let xO = lazy (resolve_symbol bignums_pkg "xO") in
      let xI = lazy (resolve_symbol bignums_pkg "xI") in
      let rec to_positive n =
	if n = 1 then
	  Lazy.force xH
	else
	  if n mod 2 = 0 then
	    Term.mkApp (Lazy.force xO, [| to_positive (n / 2) |])
	  else
  	    Term.mkApp (Lazy.force xI, [| to_positive (n / 2) |])
      in
      fun n ->
	if n <= 0
	then raise (Invalid_argument ("to_positive: " ^ string_of_int n))
	else to_positive n

  end

  module BinNum =
  struct
    let n_type = lazy (resolve_symbol bignums_pkg "N")

    let to_N =
      let o = lazy (resolve_symbol bignums_pkg "N0") in
      let pos = lazy (resolve_symbol bignums_pkg "Npos") in
      fun n ->
	if n = 0
	then Lazy.force o
	else
	  if n < 0
	  then raise (Invalid_argument (Printf.sprintf "to_N: %d" n))
	  else Term.mkApp (Lazy.force pos, [| Positive.to_positive n |])
  end

  module Nat =
  struct
    let nat_type = lazy (resolve_symbol datatypes_pkg "nat")
    let c_S = lazy (resolve_symbol datatypes_pkg "S")
    let c_O = lazy (resolve_symbol datatypes_pkg "O")

    let to_nat =
      let rec to_nat n =
	if n = 0 then
	  Lazy.force c_O
	else
	  Term.mkApp (Lazy.force c_S, [| to_nat (n - 1) |])
      in
      fun n ->
	if n < 0
	then raise (Invalid_argument ("to_nat: " ^ string_of_int n))
	else to_nat n

    let rec of_nat (trm : Term.constr) : int =
      let (h,args) = app_full trm [] in
      if Term.eq_constr h (Lazy.force c_O) then
	0
      else if Term.eq_constr h (Lazy.force c_S) then
	match args with
	  n :: _ -> 1 + of_nat n
	| _ -> bad_arg "of_nat" trm
      else
	bad_arg "of_nat" trm
  end

  module Option =
  struct
    let c_None = lazy (resolve_symbol datatypes_pkg "None")
    let c_Some = lazy (resolve_symbol datatypes_pkg "Some")

    let option_type = lazy (resolve_symbol datatypes_pkg "option")
    let option_of (t : coq_type) =
      Term.mkApp (Lazy.force option_type, [| t |])

    let to_option typ (x : Term.constr option) =
      match x with
	None -> Term.mkApp (Lazy.force c_None, [| typ |])
      | Some x -> Term.mkApp (Lazy.force c_Some, [| typ ; x |])
  end

  module List =
  struct
    let list_type =
      lazy (resolve_symbol datatypes_pkg "list")
    let list_of typ =
      Term.mkApp (Lazy.force list_type, [| typ |])

    let c_nil = lazy (resolve_symbol datatypes_pkg "nil")
    let c_cons = lazy (resolve_symbol datatypes_pkg "cons")

    let to_list typ =
      let the_nil = Term.mkApp (Lazy.force c_nil, [| typ |]) in
      let rec to_list (ls : Term.constr list) : Term.constr =
	match ls with
	  [] -> the_nil
	| l :: ls ->
	  Term.mkApp (Lazy.force c_cons, [| typ ; l ; to_list ls |])
      in to_list

  end

  module PosMap =
  struct
    type 'a pmap =
    | PM_Empty
    | PM_Branch of 'a pmap * 'a option * 'a pmap

    let posmap_mod = ["Coq";"FSets";"FMapPositive";"PositiveMap"]

    let c_leaf = lazy (resolve_symbol posmap_mod "Leaf")
    let c_node = lazy (resolve_symbol posmap_mod "Node")

    let rec pmap_add k v m =
      if k = 1 then
	match m with
	  PM_Empty -> PM_Branch (PM_Empty, Some v, PM_Empty)
	| PM_Branch(l,_,r) -> PM_Branch (l, Some v, r)
      else
	if k mod 2 = 0 then
	  match m with
	    PM_Empty -> PM_Branch (pmap_add (k / 2) v PM_Empty, None, PM_Empty)
	  | PM_Branch (l,d,r) -> PM_Branch (pmap_add (k / 2) v l, d, r)
	else
	  match m with
	    PM_Empty -> PM_Branch (PM_Empty, None, pmap_add (k / 2) v PM_Empty)
	  | PM_Branch (l,d,r) -> PM_Branch (l, d, pmap_add (k / 2) v r)

    let to_posmap (mkEmpty : 'b)
	(mkBranch : 'b -> 'c option -> 'b -> 'b)
	(get : 'a -> 'c option) =
      let rec to_pm i ls acc =
	match ls with
	  [] -> acc
	| l :: ls ->
	  to_pm (1 + i) ls
	    (match get l with
	      None ->  acc
	    | Some d -> pmap_add i d acc)
      in
      let rec convert pm =
	match pm with
	  PM_Empty -> mkEmpty
	| PM_Branch (l,d,r) ->
	  mkBranch (convert l) d (convert r)
      in
      fun ls ->
	let pm = to_pm 1 ls PM_Empty in
	convert pm
  end

  (** Depdendent pairs **)
  module SigT =
  struct
    let sigT_type : Term.constr Lazy.t =
      lazy (resolve_symbol specif_pkg "sigT")

    let c_existT : Term.constr Lazy.t =
      lazy (resolve_symbol specif_pkg "existT")

    let sigT a b : Term.constr =
      Term.mkApp (Lazy.force sigT_type, [| a ; b |])

    let existT a b f s : Term.constr =
      Term.mkApp (Lazy.force c_existT, [| a ; b ; f ; s |])
  end

  (** Non-dependent pairs **)
  module Pair =
  struct
    let prod_type : Term.constr Lazy.t =
      lazy (resolve_symbol datatypes_pkg "prod")

    let prod a b : Term.constr =
      Term.mkApp (Lazy.force prod_type, [| a ; b |])

    let c_pair : Term.constr Lazy.t =
      lazy (resolve_symbol datatypes_pkg "pair")

    let pair a b f s : Term.constr =
      Term.mkApp (Lazy.force c_pair, [| a ; b ; f ; s |])
  end

end

(****************************************************************************
   end of copy-paste
 ****************************************************************************)

(* specializing Std to our use: *)

module Std = StdT
       (struct
        let contrib_name = "HelloWorld"
       end)



(* these let us easily access the constructors we want to match against (in correct form) *)

(* we don't need a pattern_mod, I think *)

let pattern_mod = []

let ptrn_program = Std.resolve_symbol pattern_mod "AST.mkprogram"
(*
let ptrn_const = Std.resolve_symbol pattern_mod "RConst"
let ptrn_ignore = Std.resolve_symbol pattern_mod "RIgnore"
let ptrn_get = Std.resolve_symbol pattern_mod "RGet"
let ptrn_app = Std.resolve_symbol pattern_mod "RApp"
let ptrn_pi = Std.resolve_symbol pattern_mod "RPi"
let ptrn_lam = Std.resolve_symbol pattern_mod "RLam"
let ptrn_impl = Std.resolve_symbol pattern_mod "RImpl"
let ptrn_has_type = Std.resolve_symbol pattern_mod "RHasType"
*)
(*
let action_function = Std.resolve_symbol pattern_mod "function"
let action_id = Std.resolve_symbol pattern_mod "id"
let action_associate = Std.resolve_symbol pattern_mod "associate"
let action_store = Std.resolve_symbol pattern_mod "store"
*)

let into_program =
    let rec into_program (ptrn : Term.constr) : (Pretty.Clight.fundef, Pretty.Ctypes.coq_type) Pretty.AST.program =
        (matches ()
        [ (apps (EGlob ptrn_program) [get 0; get 1],
           fun _ s ->
               let progdefs = Hashtbl.find s 0 in
               let mainid   = Hashtbl.find s 1 in
               (* into_defs_list prog_defs *)
               Pretty.AST.mkprogram ([]
                         (Pretty.Camlcoq.P.of_int mainid)))
        ]
        ptrn)
     in
    into_program

let clight_dump_tactic s p = fun gl ->
    let fd = openfile s [O_CREAT; O_TRUNC; O_RDWR] 0o777 in
    let oc = out_channel_of_descr fd in
    let foc = Format.formatter_of_out_channel oc in
    (*to_channel oc p [No_sharing; Closures];*)
    print_program foc p;
    close_out oc;
    Tacticals.tclIDTAC gl

TACTIC EXTEND ClightDegen
       | ["clight_dump" string(s) constr(p)] -> [clight_dump_tactic s p] END;;
