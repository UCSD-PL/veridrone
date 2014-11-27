open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors


let output = ref ""
let store str = output := str 
let pp_print () = !output
let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
(*
let get_env_named_context = function {Environ.env_globals = n; env_named_context = _ ; env_named_vals = _ ; env_rel_context = _ ;
    env_rel_val = _; env_nb_rel = _ ; env_stratification = _ ; env_conv_oracle = _ ; retroknowledge = _ ; indirect_pterms  = _   }  -> n
*)
let mapOperator op opposite= (match op with 
		| "Rle" -> if opposite = true then ">" else "<=" 
   	        | "Rlt"  -> if opposite = true then ">=" else "<"
                | "Rgt" -> if opposite = true then "<=" else ">"
		| "Rge"  ->  if opposite = true then "<" else ">="
		| "Rmult" -> "*"
		| "Rplus" -> "+"
		| "Rminus" -> "-"
		| "eq" -> if opposite = true then "<>" else "="
		| "neq" -> if opposite = true then "=" else "<>"
		| x -> x )
type validity = Valid | Invalid | Maybe




let validityCheck op = (match op with
                | "Rle" -> Valid
                | "Rlt"  -> Valid
                | "Rgt" -> Valid
                | "Rge"  -> Valid
                | "Rmult" -> Valid
                | "Rplus" -> Valid
                | "Rminus" -> Valid
                | "eq"  -> Maybe
                | _ -> Invalid )



let createHashtable n = Hashtbl.create n

let hashtbl =   Hashtbl.create 100

let noOfVar = ref 0

let declStmt var = "(declare-const " :: (var :: ( " Real)"  ::  []) )




let mapVariable var = 
    try
	([],[Hashtbl.find hashtbl var]) 
    with Not_found ->
	noOfVar := !noOfVar + 1;
	let mappedVar = "x" ^ (string_of_int !noOfVar) in
        Hashtbl.add hashtbl var mappedVar;
	(declStmt mappedVar,[mappedVar])
	
                
let exploit (c : Term.constr) = fun gl -> 
  (* the type of [c] is [ty] *)
  let ty = Tacmach.pf_type_of gl c in      
  let goal = Tacmach.pf_concl gl in
      
   let _ = Format.printf "real %a " pp_constr goal in
(*let mappr ty = Term.map_constr pp_constr ty in *)

								                 
					           

  let rec getZ3Statements t cnt isReal mapOpposite =  (match Term.kind_of_term t with
  | Term.Const const ->  (match isReal with 
                         | true ->                                
			 		let formatStr = Format.asprintf "%a" pp_constr t in
			 		let _ = Format.printf "CONST  %s " formatStr in
			 		(match formatStr with
			 		| "0%R" -> ([],["0"])
                         		| "1%R" -> ([],["1"])
					|  _ ->  ([],[mapOperator formatStr mapOpposite])
					)

			 		(* [(mapOperator (Names.string_of_con const))]*)
		 	| false -> 
					([],[])	)
  | Term.App (fst,snd) -> let str = Format.asprintf "%a" pp_constr fst in 
			  (match validityCheck str with
			  | Invalid   -> (match isReal with  
					  | true ->	
					  	let formatTy = Format.asprintf "%a" pp_constr t in
					   	let _ = Format.printf "Invalid  %s " formatTy in
					   	mapVariable formatTy
					  	(* [formatTy]*)
					  | false ->
						 ([],[])
					   )
			  | Maybe     ->  
					   (match Term.kind_of_term snd.(0) with
					   | Term.Const const ->
							        let formatStr = Format.asprintf "%a" pp_constr snd.(0) in
								let _ = Format.printf "CONST(MAYBE)  %s" formatStr in
								(match formatStr with
								| "R" ->   		  
									let declList = ref [] in
									let listStr = ref ["("] in
									let op = mapOperator str mapOpposite in
							        	let (declStmt,stmt) = ([],[op]) in
									listStr := List.append !listStr stmt;
									declList := List.append !declList declStmt;	
									for i =1 to ((Array.length snd)-1) do
										let val_i = snd.(i) in
										let (declStmt, stmt) = (getZ3Statements val_i (cnt+1) true mapOpposite) in
										listStr := List.append !listStr stmt;
										declList := List.append !declList declStmt
										done;
										listStr := List.append !listStr [")"];
										(!declList,!listStr) 						
								| _  -> ([],[]))    	 
                                           | _ -> ([],[]) )                       
			  | Valid     ->  
					   let _ = Format.printf "valid app %s " str in
					   let listStr = ref ["("] in
					   let declList = ref [] in
					   let (declStmt,stmt) =  getZ3Statements fst (cnt+1) true mapOpposite   in 
					   listStr := List.append !listStr stmt; 
					   declList := List.append !declList declStmt;   
					   let len = Array.length snd in
					   let _ = Format.printf "length %d " len in 	
			  		   for i = 0 to ((Array.length snd)-1) do 
	              			   let 	val_i = snd.(i) in
					   let (declStmt,stmt) = (getZ3Statements val_i (cnt+1) true mapOpposite) in
			                   listStr := List.append !listStr stmt; 
					   declList := List.append !declList declStmt	
			  	           done;
			  	          listStr := List.append !listStr [")"] ; 
					   (!declList,!listStr) )       
  | Term.Var var-> 	(match isReal with 
			| true ->	
					let _ = Format.printf "First is Var %d" cnt in
				        mapVariable (Names.string_of_id var)   	
				     (*	([],[(Names.string_of_id var)]) *)
			| false -> 
					([],[]))

  | _ ->  let _ = Format.printf "UNKNOWN REPRESENTATION" in
	  ([],[])) 
   in

     let rec getZ3StatementsForGoal ty = (match Term.kind_of_term ty with
        | Term.Prod (n,b,t) ->           let z3Stmts = getZ3Statements b 0 false false in
					 
                                         (match z3Stmts with
                                         | ([],[]) -> ([],[])
                                         | (declStmts,stmts) -> let assertStmt = List.append (List.append ["(assert "] stmts) [")"] in
								let nextZ3Stmts = getZ3StatementsForGoal t in
                                                                (match nextZ3Stmts with
                                                                | ([],[]) -> ([],[])
                                                                | (nextDeclStmts,nextStmts) ->
                                                                        let allDeclStmts = (List.append declStmts nextDeclStmts) in
                                                                        let allStmts = (List.append assertStmt nextStmts) in                                                                                                (allDeclStmts,allStmts)        
                    						)
					 )
                    
        | _ ->   let (declStmt,stmts) = (getZ3Statements ty 0 false true)  in 
		 let assertStmt = List.append (List.append ["(assert "] stmts) [")"] in
		 (declStmt,assertStmt) ) in		
 
  let process_output_to_list2 = fun command -> 
  let chan = Unix.open_process_in command in
  let res = ref ([] : string list) in
  let rec process_otl_aux () =  
  let e = input_line chan in
    res := e::!res;
    process_otl_aux() in
  try process_otl_aux ()
  with End_of_file ->
    let stat = Unix.close_process_in chan in (List.rev !res,stat) in

  let read_process_lines command =
  let lines = ref [] in
  let in_channel = Unix.open_process_in command in
  begin
    try
      while true do
        lines := input_line in_channel :: !lines
      done;
    with End_of_file ->
      ignore (Unix.close_process_in in_channel)
  end;
  List.rev !lines in 
 
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
  Buffer.contents buffer in

   let (declList,stmtList) =  getZ3StatementsForGoal goal in
   let  _ =(
   match (declList ,stmtList) with 
   | (_,[]) ->   Format.printf "NOT REAL ARITHMETIC"
   | _ ->   
           let allStmts = List.append (List.append declList stmtList) ["(check-sat) "; "(get-model)"] in
           let finalStr = String.concat " " allStmts  in	   
	   let _ = Format.printf "Z3 STATEMENTS :\n%s\n" finalStr in
	   let file = "z3.txt" in
	   let oc = open_out file in
	   let _ = fprintf oc "%s\n" finalStr in
	   let _ = close_out oc in 
	   let command = String.concat "" ["z3 -smt2 " ; file ]  in
         (*  let command = String.concat "" ["cat "; "z3.txt" ; ] in *)
(*	   let out = system command in*)
	   
  	   let str = read_process command in
	   let _ = store str in
	 (*  let out = String.concat "" str in     *)
	   let _ = Format.printf "COMMAND %s " command in
	    Format.printf "OUT IS DONE  %s " str
	   (*
	   (match l with
           | fst :: _ -> Format.printf "OUT IS DONE %s" fst
	   | [] -> Format.printf "FAIL" )*)
	  (* let out = system "z3 -smt2 file"  in *)
         (*  let _ = execvp "z3" [| "z3" ; "-smt2" ; file|] in	   *)
   ) in 


 
 (* let _ = Format.printf "environment : %a " pp_constr env in *)
  let _ = Format.printf "type of hypothesis :\n%a\n" pp_constr ty in
   
  let _ = Format.printf "c is :\n%a\n" pp_constr c in 

  (* ty can be written as [forall (x1:t1) ... (xn:tn), t] 
     here, [ctx] is [(xn, tn); ...; (x1,t1))] *)
  let ctx, t = Term.decompose_prod_assum ty in
  let _ =  Format.printf "ctx is :\n%a\n" pp_constr t in    

  (* the type of the conclusion of the goal is [concl] *)
  let concl = Tacmach.pf_concl gl in 
   let _ = Format.printf "concl is :\n%a\n" pp_constr concl in 
  
  (* We want to build the proof term pf
     
     [fun (x1:t1) ... (xn:tn) (m: t -> concl) => m (c x1 .... xn)]
     
     We start to build the body of the proof term [pf_body] *)
  let pf_body = Term.mkApp (Term.mkRel 1, [| Term.mkApp (c, Termops.extended_rel_vect 1 ctx) |]) in
  let _ = Format.printf "pf body is :%a" pp_constr pf_body in 

  (* We now need to extend the context to accomodate for the extra
     parameter [m] of type [t -> concl]. 
     
     Note here that the type [t] may depend on the context
     [ctx]. There is no need to lift [t], because it is used in the
     exact same context as before; and there should not be de Bruijn
     indices in [concl].  *)
  
  let ctx = (Names.Anonymous,None, Term.mkArrow t concl ) :: ctx in 
  let pf_term = Term.it_mkLambda_or_LetIn pf_body ctx in
    
  (* Sanity check: we pretty print the term that we are going to apply*)
  let _ = Format.printf "Proof term produced by the exploit tactic:\n%a\n" pp_constr pf_term in 
  let _ = eprintf "wahhahh" in
(* let _ =  Printf.fprintf stderr "waahaa %a" pp_constr concl in *) 
   (* Unfortunately, Tactics.apply does not generate the sub-goals in
      the exact order we used. So we use a variant of Tactics.refine  *)
   Tacticals.tclIDTAC gl 
    
TACTIC EXTEND exploit
  | ["exploit" constr(c)] ->     [exploit c]      END;;

VERNAC COMMAND EXTEND PrintTimingProfile
["Print" "Timing" "Profile"] ->
[ Pp.msgnl (Pp.str (pp_print ())) ]
END;;


(* Looking carefully at the things we had to do to make the above
   tactics work, we imagine that we should be able to use the following
   tactic instead. 
   
   However, it fails with the following error message.

   Error: Application of lemmas whose beta-iota normal form contains
   metavariables deep inside the term is not supported; try "refine" instead.


let exploit2 c = fun gl -> 
  let ty = Tacmach.pf_type_of gl c in 
  let ctx, t = Term.decompose_prod_assum ty in 
  let concl = Tacmach.pf_concl gl in 
  let mvars = (List.map (fun _ -> Evarutil.mk_new_meta ()) ctx) in 
  let pf_body = Term.mkApp (Term.mkRel 1, [| Term.applist (c, mvars) |]) in 
  let term = Term.mkProd (Names.Anonymous, Term.mkArrow t concl, pf_body) in 
  Tactics.refine (Term.mkApp (term, [|Evarutil.mk_new_meta ()|])) gl
*)
