let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)


let mapOperator op = (match op with 
		| "Rle" -> "<="
   	        | "Rlt"  -> "<"
                | "Rgt" -> ">"
		| "Rge"  -> ">="
		| "Rmult" -> "*"
		| "Rplus" -> "+"
		| "Rminus" -> "-"
		| "eq" -> "="
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

type program = Statements of string list |  Declarations of string list

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

(*let mappr ty = Term.map_constr pp_constr ty in *)


  let rec getZ3Statements t cnt isReal =  (match Term.kind_of_term t with
  | Term.Const const ->  (match isReal with 
                         | true ->                                
			 		let formatStr = Format.asprintf "%a" pp_constr t in
			 		let _ = Format.printf "CONST  %s " formatStr in
			 		(match formatStr with
			 		| "0%R" -> ([],["0"])
                         		| "1%R" -> ([],["1"])
					|  _ ->   ([],[mapOperator formatStr]))
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
									let op = mapOperator str in
							        	let (declStmt,stmt) = ([],[op]) in
									listStr := List.append !listStr stmt;
									declList := List.append !declList declStmt;	
									for i =1 to ((Array.length snd)-1) do
										let val_i = snd.(i) in
										let (declStmt, stmt) = (getZ3Statements val_i (cnt+1) true) in
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
					   let (declStmt,stmt) =  getZ3Statements fst (cnt+1) true   in 
					   listStr := List.append !listStr stmt; 
					   declList := List.append !declList declStmt;   
					   let len = Array.length snd in
					   let _ = Format.printf "length %d " len in 	
			  		   for i = 0 to ((Array.length snd)-1) do 
	              			   let 	val_i = snd.(i) in
					   let (declStmt,stmt) = (getZ3Statements val_i (cnt+1) true) in
			                   listStr := List.append !listStr stmt; 
					   declList := List.append !declList declStmt	
			  	           done;
			  	          listStr := List.append !listStr [")"] ; 
					   (!declList,!listStr) )       
  | Term.Var var-> 	(match isReal with 
			| true ->	
					let _ = Format.printf "First is Var %d" cnt in
					([],[(Names.string_of_id var)]) 
			| false -> 
					([],[]))

  | _ ->  let _ = Format.printf "UNKNOWN REPRESENTATION" in
	  ([],[])) 
   in
   let (declList,stmtList) =  getZ3Statements ty 0 false in
   let  _ =(
   match (declList ,stmtList) with 
   | (_,[]) ->   Format.printf "NOT REAL ARITHMETIC"
   | _ ->  let assertStmt = List.append (List.append ["(assert "] stmtList) [")"] in 
           let allStmts = List.append declList assertStmt in
           let finalStr = String.concat " " allStmts  in
            Format.printf "Z3 STATEMENTS :\n%s\n" finalStr 
   ) in 
   (*below stuff is not required for our plugin - you may not read this*)
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
  
   (* Unfortunately, Tactics.apply does not generate the sub-goals in
      the exact order we used. So we use a variant of Tactics.refine  *)
    Tactics.apply_term pf_term (List.map (fun _ -> Evarutil.mk_new_meta ()) ctx) gl
    
TACTIC EXTEND exploit
  | ["exploit" constr(c)] ->     [exploit c]      END;;


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
