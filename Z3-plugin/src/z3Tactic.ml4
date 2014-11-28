open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors


let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
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

                
let z3Tactic  = fun gl -> 
  (* the type of [c] is [ty] *)
  let goal = Tacmach.pf_concl gl in     


  let output = ref "" in
  let store str = output := str in
  let pp_print () = !output in
 
  let reverseHashTbl = Hashtbl.create 100 in

    
  let hashtbl =   Hashtbl.create 100 in
  let noOfVar = ref 0 in
  let declStmt var = "(declare-const " :: (var :: ( " Real)"  ::  []) ) in
  
  let hashTableMappings = ref [] in

  let toStringKeyValuePair key value =  (hashTableMappings:= List.append !hashTableMappings ["\n"; key ; ":"; value ; "\n"]) in   

  let mapVariable var =
    try
        ([],[Hashtbl.find hashtbl var])
    with Not_found ->
        noOfVar := !noOfVar + 1;
        let mappedVar = "x" ^ (string_of_int !noOfVar) in
        Hashtbl.add hashtbl var mappedVar;
	Hashtbl.add reverseHashTbl mappedVar var;
        (declStmt mappedVar,[mappedVar]) in   
  								               					          
  let rec getZ3Statements t cnt isReal mapOpposite =  (match Term.kind_of_term t with
  | Term.Const const ->  (match isReal with 
                         | true ->                                
			 		let formatStr = Format.asprintf "%a" pp_constr t in
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
					   	mapVariable formatTy
					  	(* [formatTy]*)
					  | false ->
						 ([],[])
					   )
			  | Maybe     ->  
					   (match Term.kind_of_term snd.(0) with
					   | Term.Const const ->
							        let formatStr = Format.asprintf "%a" pp_constr snd.(0) in
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
					   let listStr = ref ["("] in
					   let declList = ref [] in
					   let (declStmt,stmt) =  getZ3Statements fst (cnt+1) true mapOpposite   in 
					   listStr := List.append !listStr stmt; 
					   declList := List.append !declList declStmt;   
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
           let finalZ3Stmts = String.concat " " allStmts  in	   
	   let file = "/tmp/z3.txt" in
	   let oc = open_out file in
	   let _ = fprintf oc "%s\n" finalZ3Stmts in
	   let _ = close_out oc in 
	   let command = String.concat "" ["z3 -smt2 " ; file ]  in
	   let _ = Format.printf "Z3 Statements : %s\n" finalZ3Stmts in   
	   let _ = Format.printf "COMMAND  : %s\n" command  in
   	   let z3Output = read_process command in
	   let _ = Hashtbl.iter toStringKeyValuePair reverseHashTbl  in
           let outputStr = String.concat "" (List.append  [z3Output ; "\n" ;  ] !hashTableMappings)   in
	   store outputStr
   ) in 
  
   let _ = Pp.msgnl (Pp.str (pp_print ())) in    
   Tacticals.tclIDTAC gl 
    
TACTIC EXTEND exploit
  | ["z3Tactic"] ->     [z3Tactic]      END;;
