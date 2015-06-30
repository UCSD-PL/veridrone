open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors

module type TM =
sig
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

  val apps : ('a,'b,'c) pattern -> ('a,'b,'c) pattern list -> ('a,'b,'c) pattern

  val get : 'a -> ('a,'b,'c) pattern

  val match_pattern : ('a,'b,'c) pattern -> Term.constr -> 'c -> ('a,Term.constr) Hashtbl.t -> ('a,Term.constr) Hashtbl.t

  val matches : 'a -> (('b,'d,'a) pattern * ('a -> ('b, Term.constr) Hashtbl.t -> 'c)) list -> Term.constr -> 'c

  val matches_app : 'a -> (('b,'d,'a) pattern * ('a -> ('b, Term.constr) Hashtbl.t -> 'c)) list -> Term.constr -> Term.constr array -> int -> 'c
end

module Term_match : TM =
struct
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
end

module Z3Tactic =
struct

  let contrib_name = "z3-check"

  let debug = ref false

  let with_debugging f g =
    let copy = !debug in
    let _ = debug := true in
    try
      let result = f g in
      let _ = debug := copy in
      result
    with
      f ->
	let _ = debug := copy in
	raise f

  let debug f = if !debug then f () else ()

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    let re = Coqlib.find_reference contrib_name path tm in
    Libnames.constr_of_global re

  let r_pkg = ["Coq";"Reals";"Rdefinitions"]
  let logic_pkg = ["Coq";"Init";"Logic"]

  let c_R = resolve_symbol r_pkg "R"
  let c_0 = resolve_symbol r_pkg "R0"
  let c_1 = resolve_symbol r_pkg "R1"
  let c_Rplus = resolve_symbol r_pkg "Rplus"
  let c_Rminus = resolve_symbol r_pkg "Rminus"
  let c_Rdiv = resolve_symbol r_pkg "Rdiv"
  let c_Rmult = resolve_symbol r_pkg "Rmult"
  let c_Ropp = resolve_symbol r_pkg "Ropp"
  let c_Rinv = resolve_symbol r_pkg "Rinv"

  let c_Rlt = resolve_symbol r_pkg "Rlt"
  let c_Rle = resolve_symbol r_pkg "Rle"
  let c_Rgt = resolve_symbol r_pkg "Rgt"
  let c_Rge = resolve_symbol r_pkg "Rge"

  let c_and = resolve_symbol logic_pkg "and"
  let c_or = resolve_symbol logic_pkg "or"
  let c_True = resolve_symbol logic_pkg "True"
  let c_False = resolve_symbol logic_pkg "False"
  let c_Not = resolve_symbol logic_pkg "not"
  let c_eq = resolve_symbol logic_pkg "eq"
  let c_Prop = Term.mkProp

  module Cmap = Map.Make
    (struct
      type t = Term.constr
      let compare = Term.constr_ord
     end)

  type r_type = Prop | R

  type r_expr =
      RConst of float
    | Rplus of r_expr * r_expr
    | Rminus of r_expr * r_expr
    | Rmult of r_expr * r_expr
    | Rdiv of r_expr * r_expr
    | Ropp of r_expr
    | Rinv of r_expr
    | Ropaque of int

  type r_prop =
    | Rtrue
    | Rfalse
    | Rlt of r_expr * r_expr
    | Rle of r_expr * r_expr
    | Rgt of r_expr * r_expr
    | Rge of r_expr * r_expr
    | Req of r_expr * r_expr
    | Rand of r_prop * r_prop
    | Ror of r_prop * r_prop
    | Rimpl of r_prop * r_prop
    | Rnot of r_prop
    | Popaque of int

  let rec print_r_expr out e =
    match e with
      RConst f -> Format.fprintf out "%f" f
    | Rplus (l,r) -> Format.fprintf out "(+ %a %a)" print_r_expr l print_r_expr r
    | Rminus (l,r) -> Format.fprintf out "(- %a %a)" print_r_expr l print_r_expr r
    | Rmult (l,r) -> Format.fprintf out "(* %a %a)" print_r_expr l print_r_expr r
    | Rdiv (l,r) -> Format.fprintf out "(/ %a %a)" print_r_expr l print_r_expr r
    | Ropp l -> Format.fprintf out "(- 0 %a)" print_r_expr l
    | Rinv l -> Format.fprintf out "(/ 1 %a)" print_r_expr l
    | Ropaque l -> Format.fprintf out "x%d" l

  let rec print_r_prop out e =
    match e with
      Rtrue -> Format.fprintf out "true"
    | Rfalse -> Format.fprintf out "false"
    | Rnot l -> Format.fprintf out "(not %a)" print_r_prop l
    | Popaque x -> Format.fprintf out "x%d" x
    | Rand (l,r) -> Format.fprintf out "(and %a %a)" print_r_prop l print_r_prop r
    | Ror (l,r) -> Format.fprintf out "(or %a %a)" print_r_prop l print_r_prop r
    | Rimpl (l,r) -> Format.fprintf out "(=> %a %a)" print_r_prop l print_r_prop r
    | Rle (l,r) -> Format.fprintf out "(<= %a %a)" print_r_expr l print_r_expr r
    | Rlt (l,r) -> Format.fprintf out "(< %a %a)" print_r_expr l print_r_expr r
    | Rge (l,r) -> Format.fprintf out "(>= %a %a)" print_r_expr l print_r_expr r
    | Rgt (l,r) -> Format.fprintf out "(> %a %a)" print_r_expr l print_r_expr r
    | Req (l,r) -> Format.fprintf out "(= %a %a)" print_r_expr l print_r_expr r

  let conclusion_name = "__CONCLUSION__"

  let print_identifier out id =
    Format.fprintf out "%s" (Names.string_of_id id)

  let print_r_assert out (nm,e) =
    Format.fprintf out "(assert (! %a :named %a))" print_r_prop e print_identifier nm

  let print_type out t =
    match t with
      Prop -> Format.fprintf out "Bool"
    | R -> Format.fprintf out "Real"

  let pr_list sep pr =
    let rec pr_list out ls =
      match ls with
	[] -> ()
      | [l] -> Format.fprintf out "%a" pr l
      | l :: ls -> Format.fprintf out "%a%s%a" pr l sep pr_list ls
    in
    pr_list

  let pr_decls out =
    Cmap.iter (fun _ (k,v) -> Format.fprintf out "(declare-const x%d %a)" k print_type v)

  let pr_smt2 (sep : string) out (tbl, stmts) =
    Format.fprintf out "%a%a"
		   pr_decls tbl
		   (pr_list sep print_r_assert) stmts

  let ptrn_success = Str.regexp "^unsat (\\([^)]*\\))"
  let ptrn_failure = Str.regexp "^sat ([^)]*) (model\\(.+\\)) ?$"
  let ptrn_split = Str.regexp " "

  let ptrn_def = Str.regexp "(define-fun x\\([0-9]+\\) () Real[ \n\r\t]+(?\\(-? [0-9]*.[0-9]*\\))?)"

  type z3_result =
      Sat of (int * float) list
    | Unsat of Names.identifier list


  let rec extract_model start result =
    debug (fun _ -> Printf.eprintf "extract model: %s\n" (String.sub result start (String.length result - start))) ;
    try
      let _ = Str.search_forward ptrn_def result start in
      let num = int_of_string (Str.matched_group 1 result) in
      let value = Str.matched_group 2 result in
      let value =
	try
	  let _ = String.index value '-' in
	  "-" ^ String.sub value 2 (String.length value - 2)
	with
	  Not_found -> value
      in
      let value = float_of_string value in
      (num, value) :: extract_model (Str.match_end ()) result
    with
      Not_found -> []

  let parse_Z3_result result =
    let _ =
      debug (fun _ ->
	     Pp.msg_debug (Pp.str ("Z3 output\n" ^ result)))
    in
    let result = Str.global_replace (Str.regexp (Str.quote "\n")) " " result in
    let result = Str.global_replace (Str.regexp (Str.quote "\r")) "" result in
    if Str.string_partial_match ptrn_success result 0 then
      let lst = Str.matched_group 1 result in
      Unsat (List.map Names.id_of_string (Str.split ptrn_split lst))
    else
      if Str.string_match ptrn_failure result 0 then
	let result = Str.matched_group 1 result in
	Sat (extract_model 0 result)
      else
	let _ = Format.eprintf "Bad Z3 output:\n%s" result in
	assert false

  let runZ3 tbl stmts =
    let (in_channel,out_channel) = Unix.open_process "z3 -in -smt2" in
    let _ =
      begin
	let fmt = Format.formatter_of_out_channel out_channel in
	Format.fprintf fmt "(set-option :produce-unsat-cores true)\n" ;
	Format.fprintf fmt "(set-option :produce-models true)\n" ;
	Format.fprintf fmt "%a" (pr_smt2 "") (tbl, stmts) ;
	Format.fprintf fmt "(check-sat)\n(get-unsat-core)\n(get-model)" ;
	Format.pp_print_flush fmt () ;
	flush out_channel ;
	close_out out_channel
      end
    in
    let buffer_size = 2048 in
    let buffer = Buffer.create buffer_size in
    let string = String.create buffer_size in
    let chars_read = ref 1 in
    while !chars_read <> 0 do
      chars_read := input in_channel string 0 buffer_size;
      Buffer.add_substring buffer string 0 !chars_read
    done;
    ignore (Unix.close_process (in_channel, out_channel));
    let result = Buffer.contents buffer in
    parse_Z3_result result

  let parse_uop recur constr op =
    (Term_match.apps (Term_match.EGlob constr)
		     [Term_match.get 0],
     fun tbl bindings ->
     let (res,tbl) = recur tbl (Hashtbl.find bindings 0) in
     (op res, tbl))

  let parse_bop recur constr op =
    (Term_match.apps (Term_match.EGlob constr)
		     [Term_match.get 0;Term_match.get 1],
     fun tbl bindings ->
     let (l,tbl) = recur tbl (Hashtbl.find bindings 0) in
     let (r,tbl) = recur tbl (Hashtbl.find bindings 1) in
     (op l r, tbl))

  let rec parse_expr tbl =
    Term_match.matches tbl
      [ (Term_match.EGlob c_0, fun tbl _ -> (RConst 0., tbl))
      ; (Term_match.EGlob c_1, fun tbl _ -> (RConst 1., tbl))
      ; parse_bop parse_expr c_Rplus (fun a b -> Rplus (a,b))
      ; parse_bop parse_expr c_Rminus (fun a b -> Rminus (a,b))
      ; parse_bop parse_expr c_Rmult (fun a b -> Rmult (a,b))
      ; parse_bop parse_expr c_Rdiv (fun a b -> Rdiv (a,b))
      ; parse_uop parse_expr c_Ropp (fun a -> Ropp a)
      ; parse_uop parse_expr c_Rinv (fun a -> Rinv a)
      ; (Term_match.get 0,
	 fun tbl binders ->
	 let trm = Hashtbl.find binders 0 in
	 try
	   (Ropaque (fst (Cmap.find trm tbl)), tbl)
	 with
	   Not_found ->
	   let nxt = Cmap.cardinal tbl in
	   (Ropaque nxt, Cmap.add trm (nxt,R) tbl))
      ]

  let rec parse_prop tbl =
    Term_match.matches tbl
      [ parse_bop parse_expr c_Rlt (fun a b -> Rlt (a,b))
      ; parse_bop parse_expr c_Rle (fun a b -> Rle (a,b))
      ; parse_bop parse_expr c_Rgt (fun a b -> Rgt (a,b))
      ; parse_bop parse_expr c_Rge (fun a b -> Rge (a,b))
      ; (Term_match.apps (Term_match.EGlob c_eq)
			 [Term_match.EGlob c_R;
			  Term_match.get 0;
			  Term_match.get 1],
	 fun tbl bindings ->
	 let (l,tbl) = parse_expr tbl (Hashtbl.find bindings 0) in
	 let (r,tbl) = parse_expr tbl (Hashtbl.find bindings 1) in
	 (Req (l, r), tbl))
      ; parse_bop parse_prop c_and (fun a b -> Rand (a,b))
      ; parse_bop parse_prop c_or  (fun a b -> Ror (a,b))
      ; (Term_match.apps (Term_match.EGlob c_Not)
	   [Term_match.get 0], fun tbl bindings ->
	     let (l,tbl) = parse_prop tbl (Hashtbl.find bindings 0) in
	     (Rnot l, tbl))
      ; (Term_match.EGlob c_True, fun tbl _ -> (Rtrue, tbl))
      ; (Term_match.EGlob c_False, fun tbl _ -> (Rfalse, tbl))
      ; (Term_match.get 0,
	 fun tbl binders ->
	 let trm = Hashtbl.find binders 0 in
	 try
	   (Popaque (fst (Cmap.find trm tbl)), tbl)
	 with
	   Not_found ->
	   begin
	     let nxt = Cmap.cardinal tbl in
	     (Popaque nxt, Cmap.add trm (nxt,Prop) tbl)
	   end)
      ]

  let pp_list (pp : 'a -> Pp.std_ppcmds) (pp_sep : unit -> Pp.std_ppcmds) =
    let rec pp_list (ls : 'a list) : Pp.std_ppcmds =
      match ls with
	[] -> Pp.spc ()
      | [x] -> pp x
      | x :: xs -> Pp.(++) (pp x)  (Pp.(++) (pp_sep ()) (pp_list xs))
    in
    pp_list

  let pr_unsat_core ls =
    pp_list Ppconstr.pr_id Pp.spc ls

  let pr_model tbl =
    let rec find x =
      match Cmap.fold (fun k (v,_) acc -> if v = x then Some k else acc) tbl None with
	None -> assert false
      | Some x -> x
    in
    let pp_assign (x,v) =
      let vv : float = v in
      Pp.(   (Printer.pr_constr (find x))
	  ++ (str (Printf.sprintf " = %f" vv)))
    in
    begin
    fun x ->
      match x with
      | [] -> assert false
      | _ -> 
	pp_list pp_assign Pp.fnl x
    end

  let maybe_parse check tbl (name, decl, trm) =
    if check trm then
      try
	let (p,tbl) = parse_prop tbl trm in
	Some (tbl, (name, p))
      with
	Term_match.Match_failure -> None
    else
      None

  let z3Tactic quick gl =
    let goal = Tacmach.pf_concl gl in
    let hyps = Tacmach.pf_hyps gl in

    let is_prop p =
      Term.eq_constr (Tacmach.pf_type_of gl p) Term.mkProp
    in

    let tbl = Cmap.empty in
    match maybe_parse (fun _ -> true) tbl
		      (Names.id_of_string conclusion_name, None, goal)
    with
      None ->
      Tacticals.tclFAIL 0 (Pp.str "z3 plugin failed to parse goal") gl
    | Some (tbl, (name, concl)) ->
       let acc = (tbl, [(name, Rnot concl)]) in
       let (tbl,hyps) =
	 List.fold_left (fun (tbl,acc) t ->
			 match maybe_parse is_prop tbl t with
			   None -> (tbl, acc)
			 | Some (tbl, hyp) -> (tbl, hyp::acc)) acc hyps
       in
       let _ =
	 debug (fun _ ->
		let _ = Format.fprintf Format.str_formatter "%a" (pr_smt2 "\n") (tbl,hyps) in
		let msg = Format.flush_str_formatter () in
		let _ = Format.eprintf "%a" (pr_smt2 "\n") (tbl, hyps) in
		Pp.msg_debug (Pp.str msg))
       in
       match runZ3 tbl hyps with
         Sat model ->
	 let msg =
	   Pp.(   (str "z3 failed to solve the goal.")
               ++ (fnl ())
	       ++ (pr_model tbl model))
	 in
	 Tacticals.tclFAIL 0 msg gl
       | Unsat core ->
	  let msg =
	    Pp.(++) (Pp.str "z3 solved the goal using only")
		    (Pp.(++) (Pp.spc ()) (pr_unsat_core core))
	  in
	  Tacticals.tclIDTAC_MESSAGE msg gl

end

TACTIC EXTEND z3_tac
  | ["z3" "solve"]     ->     [Z3Tactic.z3Tactic false]
END;;

TACTIC EXTEND z3_tac_dbg
  | ["z3" "solve_dbg"] ->     [Z3Tactic.with_debugging (Z3Tactic.z3Tactic false)]
END;;


TACTIC EXTEND z3_tac_quick
  | ["z3" "quick" "solve"] -> [Z3Tactic.z3Tactic true]
END;;
