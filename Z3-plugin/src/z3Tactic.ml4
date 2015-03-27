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

  let read_process command =
    let buffer_size = 2048 in
    let buffer = Buffer.create buffer_size in
    let string = String.create buffer_size in
    let in_channel = Unix.open_process_in command in
    let chars_read = ref 1 in
    while !chars_read <> 0 do
      chars_read := input in_channel string 0 buffer_size;
      Buffer.add_substring buffer string 0 !chars_read
    done;
    ignore (Unix.close_process_in in_channel);
    Buffer.contents buffer


  let contrib_name = "z3-check"

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
      RConst f -> Printf.fprintf out "%f" f
    | Rplus (l,r) -> Printf.fprintf out "(+ %a %a)" print_r_expr l print_r_expr r
    | Rminus (l,r) -> Printf.fprintf out "(- %a %a)" print_r_expr l print_r_expr r
    | Rmult (l,r) -> Printf.fprintf out "(* %a %a)" print_r_expr l print_r_expr r
    | Rdiv (l,r) -> Printf.fprintf out "(/ %a %a)" print_r_expr l print_r_expr r
    | Ropp l -> Printf.fprintf out "(- 0 %a)" print_r_expr l
    | Rinv l -> Printf.fprintf out "(/ 1 %a)" print_r_expr l
    | Ropaque l -> Printf.fprintf out "x%d" l

  let rec print_r_prop out e =
    match e with
      Rtrue -> Printf.fprintf out "true"
    | Rfalse -> Printf.fprintf out "false"
    | Rnot l -> Printf.fprintf out "(not %a)" print_r_prop l
    | Popaque x -> Printf.fprintf out "x%d" x
    | Rand (l,r) -> Printf.fprintf out "(and %a %a)" print_r_prop l print_r_prop r
    | Ror (l,r) -> Printf.fprintf out "(or %a %a)" print_r_prop l print_r_prop r
    | Rimpl (l,r) -> Printf.fprintf out "(=> %a %a)" print_r_prop l print_r_prop r
    | Rle (l,r) -> Printf.fprintf out "(<= %a %a)" print_r_expr l print_r_expr r
    | Rlt (l,r) -> Printf.fprintf out "(< %a %a)" print_r_expr l print_r_expr r
    | Rge (l,r) -> Printf.fprintf out "(>= %a %a)" print_r_expr l print_r_expr r
    | Rgt (l,r) -> Printf.fprintf out "(> %a %a)" print_r_expr l print_r_expr r
    | Req (l,r) -> Printf.fprintf out "(= %a %a)" print_r_expr l print_r_expr r

  let conclusion_name = "__CONCLUSION__"

  let print_identifier out id =
    Printf.fprintf out "%s" (Names.string_of_id id)

  let print_r_assert out (nm,e) =
    Printf.fprintf out "(assert (! %a :named %a))" print_r_prop e print_identifier nm

  let print_type out t =
    match t with
      Prop -> Printf.fprintf out "Bool"
    | R -> Printf.fprintf out "Real"

  let pr_list pr out ls =
    List.iter (Printf.fprintf out "%a" pr) ls

  let pr_decls (out : out_channel) =
    Cmap.iter (fun _ (k,v) -> Printf.fprintf out "(declare-const x%d %a)" k print_type v)

  let write_problem (out : out_channel) tbl stmts =
    Printf.fprintf out "%a" pr_decls tbl ;
    Printf.fprintf out "%a" (pr_list print_r_assert) stmts

  let ptrn_success = Str.regexp "^unsat\n(\([^)]+\))"
  let ptrn_failure = Str.regexp "^sat"
  let ptrn_split = Str.regexp " "

  let parse_Z3_result result =
    if Str.string_partial_match ptrn_success result 0 then
      let lst = Str.matched_group 1 result in
      Some (List.map Names.id_of_string (Str.split ptrn_split lst))
    else
      if Str.string_match ptrn_failure result 0 then
	None
      else
	let _ = Printf.eprintf "Bad Z3 output:\n%s" result in
	assert false

  let runZ3 tbl stmts =
    let file = Filename.temp_file "z3-" ".smt2" in
    let out = open_out file in
    let _ =
      begin
	fprintf out "(set-option :produce-unsat-cores true)\n" ;
	write_problem out tbl stmts ;
	fprintf out "(check-sat)\n(get-unsat-core)" ;
	close_out out
      end
    in
    let command = Printf.sprintf "z3 -smt2 -- %s" file  in
    parse_Z3_result (read_process command)

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

  let maybe_parse tbl (name, decl, trm) =
    try
      let (p,tbl) = parse_prop tbl trm in
      Some (tbl, (name, p))
    with
      Term_match.Match_failure -> None

  let rec pr_unsat_core ls =
    match ls with
      [] -> Pp.spc ()
    | [x] -> Ppconstr.pr_id x
    | x :: xs -> Pp.(++) (Ppconstr.pr_id x)
			 (Pp.(++) (Pp.spc ()) (pr_unsat_core xs))

  let z3Tactic quick gl =
    let goal = Tacmach.pf_concl gl in
    let hyps = Tacmach.pf_hyps gl in

    let tbl = Cmap.empty in
    match maybe_parse tbl (Names.id_of_string conclusion_name, None, goal) with
      None ->
      Tacticals.tclFAIL 0 (Pp.str "z3 plugin failed to parse goal") gl
    | Some (tbl, (name, concl)) ->
       let acc = (tbl, [(name, Rnot concl)]) in
       let (tbl,hyps) =
	 List.fold_left (fun (tbl,acc) t ->
			 match maybe_parse tbl t with
			   None -> (tbl, acc)
			 | Some (tbl, hyp) -> (tbl, hyp::acc)) acc hyps
       in
       match runZ3 tbl hyps with
         None ->
	 Tacticals.tclFAIL 0 (Pp.str "z3 failed to solve the goal") gl
       | Some core ->
	  let msg =
	    Pp.(++) (Pp.str "z3 solved the goal using only")
		    (Pp.(++) (Pp.spc ()) (pr_unsat_core core))
	  in
	  Tacticals.tclIDTAC_MESSAGE msg gl

end

TACTIC EXTEND z3_tac
  | ["z3Tactic"] ->     [Z3Tactic.z3Tactic false]
END;;

TACTIC EXTEND z3_tac_quick
  | ["z3" "quick" "solve"] -> [Z3Tactic.z3Tactic true]
END;;
