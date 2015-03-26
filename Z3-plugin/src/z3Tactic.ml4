open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors



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


let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)


type validOperation = ValidOp of string | InvalidOp
let mapOperator op = (match op with
		| "Rle" -> ValidOp "<="
   	        | "Rlt"  -> ValidOp "<"
                | "Rgt" -> ValidOp ">"
		| "Rge"  -> ValidOp ">="
		| "Rmult" -> ValidOp "*"
		| "Rplus" -> ValidOp "+"
		| "Rminus" -> ValidOp "-"
		| "eq" -> ValidOp "="
		| "Rinv" -> ValidOp "/ 1"
		| "Ropp" -> ValidOp "- 0"
		| x -> InvalidOp )
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
		| "Rinv" -> Valid
		| "Ropp" -> Valid
                | _ -> Invalid )

class ['a] assertion  (isgoal:bool) (assertionStmt:'a) (assertionName:string) =
	object (self)
	val mutable isGoal = isgoal
	val mutable assertion = assertionStmt
	val mutable translatedAssertion = ""
	val mutable name = assertionName
	method getName = name
	method getStmt = assertion
	method getisGoal = isGoal
	method setTranslatedAssertion (translatedStmt:string) = translatedAssertion <- translatedStmt
	method getTranslatedAssertion = translatedAssertion
	end

class ['a] hashTable size =
	object (self)
	val mutable htbl = Hashtbl.create size
	val mutable revhtbl = Hashtbl.create size
	val mutable noOfVar = 0
	method private incrementNoOfVar = noOfVar <- noOfVar + 1
	method getReverseHashTable = revhtbl
	method getHashTable = htbl
	method getMapping (var:'a) =
		try
			Hashtbl.find htbl var
		with Not_found ->
	  		self#incrementNoOfVar;
			let mappedVar = "x" ^ (string_of_int noOfVar) in
			Hashtbl.add htbl var mappedVar;
			Hashtbl.add revhtbl mappedVar var;
			mappedVar
	method exists (var : 'a) =
		try
			let _ = Hashtbl.find htbl var in
			true
		with Not_found ->
			false
	end

let declStmt var = "(declare-const " :: (var :: ( " Real)"  ::  []) )


let getDeclStmtForVariable var varMapping =  declStmt var

let rec getIndividualAssertions goal = (match Term.kind_of_term goal with
					| Term.Prod (n,b,t) ->         	b :: (getIndividualAssertions t)

					| _ ->    			[goal]
					)

let rec getHypothesisAssertions goal = (match Term.kind_of_term goal with
                                        | Term.Prod (n,b,t) ->
									( match n with
										|Names.Name id ->  let hypName = string_of_id id in
												   ((new assertion false b hypName) :: getHypothesisAssertions t)
										| Names.Anonymous -> (new assertion false b "unknown") :: getHypothesisAssertions t
									)

                                        | _ ->                          []
                                        )
let rec getGoalAssertion goal = (match Term.kind_of_term goal with
                                        | Term.Prod (n,b,t) ->          getGoalAssertion t

                                        | _ ->                          (new assertion true goal "G")
                                )


let rec getZ3Statements t varMapping cnt isReal=  (match Term.kind_of_term t with
  | Term.Const const ->  (match isReal with
                         | true ->      (*not happy doing this. real hacky. checking if its a real number or an operation or a parameter. would ideally want to break down the ast further. could not do so since the type constructors are not exposed outside*)
			 		let formatStr = Format.asprintf "%a" pp_constr t in
			 		(match formatStr with
			 		| "0%R" -> ([],["0"])
                         		| "1%R" -> ([],["1"])
					|  _ ->
						 (
						 match mapOperator formatStr with
						 | ValidOp op -> (match formatStr with
								| _ ->		([],[op])
								)
						 | InvalidOp ->
								(
                                        			match varMapping#exists formatStr with
   			                                        | false  ->  let mappedVar = varMapping#getMapping (formatStr) in
                           		                         ((getDeclStmtForVariable mappedVar varMapping),[mappedVar])
                                        			| true ->  let mappedVar = varMapping#getMapping (formatStr) in
		                                                 ([],[mappedVar])
               				                        )
						 )
					)

		 	| false ->
					([],[])	)
  | Term.App (fst,snd) -> let str = Format.asprintf "%a" pp_constr fst in
			  (match validityCheck str with
			  | Invalid   -> (match isReal with
					  | true ->
					  	let formatTy = Format.asprintf "%a" pp_constr t in
						(
	                                        match varMapping#exists formatTy with
        	                                | false  ->  let mappedVar = varMapping#getMapping formatTy in
						    let _ = Format.printf "var %s %s " mappedVar formatTy  in
                                                    ((getDeclStmtForVariable mappedVar varMapping),[mappedVar])
                	                        | true ->  let mappedVar = varMapping#getMapping formatTy in
                                                    ([],[mappedVar])
                        	                )

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
									let op = mapOperator str in
								 	(match op with
									| ValidOp op ->

								        	let (declStmt,stmt) = ([],[op]) in
										listStr := List.append !listStr stmt;
										declList := List.append !declList declStmt;
										for i =1 to ((Array.length snd)-1) do
											let val_i = snd.(i) in
											let (declStmt, stmt) = (getZ3Statements val_i varMapping (cnt+1) true) in
											listStr := List.append !listStr stmt;
											declList := List.append !declList declStmt
											done;
											listStr := List.append !listStr [")"];
											(!declList,!listStr)
									| InvalidOp ->  let _ = Format.printf "Something unexpected is happening" in
											([],[])
									)
								| _  -> ([],[]))
                                           | _ -> ([],[]) )
			  | Valid     ->
					   let listStr = ref ["("] in
					   let declList = ref [] in
					   let (declStmt,stmt) =  getZ3Statements fst varMapping (cnt+1) true   in
					   listStr := List.append !listStr stmt;
					   declList := List.append !declList declStmt;
			  		   for i = 0 to ((Array.length snd)-1) do
	              			   let 	val_i = snd.(i) in
					   let (declStmt,stmt) = (getZ3Statements val_i varMapping (cnt+1) true) in
			                   listStr := List.append !listStr stmt;
					   declList := List.append !declList declStmt
			  	           done;
			  	          listStr := List.append !listStr [")"] ;
					   (!declList,!listStr) )
  | Term.Var var-> 	(match isReal with
			| true ->	let str = Names.string_of_id var in
					let _ = Format.printf "variable %s" str in
					(
					match varMapping#exists (Names.string_of_id var) with
					| false  ->  let mappedVar = varMapping#getMapping (Names.string_of_id var) in
						    ((getDeclStmtForVariable mappedVar varMapping),[mappedVar])
					| true ->  let mappedVar = varMapping#getMapping (Names.string_of_id var) in
					 	    ([],[mappedVar])
					)
				     (*	([],[(Names.string_of_id var)]) *)
			| false ->
					([],[]))

  | _ ->  let _ = Format.printf "UNKNOWN REPRESENTATION" in ([],[]))


let getZ3Representation ty varMapping mapOpposite=   let z3Stmts = getZ3Statements ty varMapping 0 false in
                                                     (match z3Stmts with
                                                     | ([],[]) -> ""
                                                     | (declStmts,stmts) -> let assertStmt =
									    (match mapOpposite with
									    | true ->  List.append (List.append ["(assert (not "] stmts) ["))"]
									    | false -> List.append (List.append ["(assert "] stmts) [")"]
									    ) in
									    let allStmts = (List.append declStmts assertStmt) in
									    String.concat " " allStmts
						     )




let addToList a lst = a :: lst
let rec getAllSubsets lst = match lst with
			    | fst :: snd ->
				            (
					    match snd with
					    | []  -> [[fst]]
					    | _ ->
					      let subsets =  (getAllSubsets snd) in
					      let mapList = (List.map (addToList fst) subsets) in
					      List.append ([fst] :: mapList) subsets
					    )
			    |  []    ->        [[]]

let listCmp lst1 lst2 = if (List.length lst1) < (List.length lst2)  then -1 else 1

let rec printList lst =  match lst with
			 | fst :: snd  -> let _ = Format.printf "%s" fst in
					  printList snd
			 | [] ->   Format.printf "\n"

let rec printListOfLists lst = match lst with
			   | fst :: snd  ->  let _ = printList fst in
					     printListOfLists snd
			   | []     ->    Format.printf "\n"


let rec translateHypothesisAssertions assertions varMapping =   match assertions with
								| a :: b ->
									   let _ = a#setTranslatedAssertion (getZ3Representation a#getStmt varMapping false) in
							        	   a :: (translateHypothesisAssertions b varMapping)
							        | _  -> []
let rec translateGoalAssertion assertion varMapping =  let _ = assertion#setTranslatedAssertion (getZ3Representation assertion#getStmt varMapping true) in
						 	assertion


let getAllSubsetsOfHypothesisAssertions goal =
								let assertions = getHypothesisAssertions goal in
								let assertionsSubset = getAllSubsets assertions in
								assertionsSubset


let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let runZ3 finalZ3Stmts =

  let file = "/tmp/z3.txt" in
  let oc = open_out file in
  let _ = fprintf oc "%s\n" finalZ3Stmts in
  let _ = close_out oc in
  let command = String.concat "" ["z3 -smt2 " ; file ]  in
(*
  let _ = Format.printf "Z3 Statements : %s\n" finalZ3Stmts in
  let _ = Format.printf "COMMAND  : %s\n" command  in
*)
  let z3Output = read_process command in
  z3Output

let solveUsingZ3 assertions goal =
  let z3Stmts =
    let assertionStmts = List.map (fun stmt -> stmt#getTranslatedAssertion )  assertions in
    let goalStmt = [goal#getTranslatedAssertion] in
    String.concat " " (List.append (List.append assertionStmts goalStmt) ["(check-sat) "; "(get-model)"] ) in
  let z3Output = (runZ3 z3Stmts) in
  z3Output


let findTheSmallestSubsetGoalSolver goal =
  let hypothesisAssertionSubsets = getAllSubsetsOfHypothesisAssertions goal in
  let sortedHypothesisAssertionSubsets =  List.sort listCmp hypothesisAssertionSubsets in
  let translatedSortedHypoAssertionSubsets = List.map (fun hypoAssertions ->

    let ht = new hashTable 100 in
    let assertions = (translateHypothesisAssertions hypoAssertions ht) in
    (assertions,ht))
    sortedHypothesisAssertionSubsets in
  let goalAssertion = getGoalAssertion goal in
  let (isSolvable,output,solHt) = List.fold_left (fun b hypoAssertions->
    (
      match b with
      | (false,_,_)->
	let (assertions,ht) = hypoAssertions in
	let _ = (translateGoalAssertion goalAssertion ht) in
	let z3Output = (solveUsingZ3 assertions goalAssertion) in
	if contains z3Output "unsat" then
	  let assertionNames =List.map (fun assertion -> assertion#getName) assertions in
	  (true,String.concat " " assertionNames,ht) else (false,z3Output,ht)
      | (true,_,_) ->
	b
    ) ) (false,"",new hashTable 100) translatedSortedHypoAssertionSubsets in

  let hashMappings = Hashtbl.fold (fun key value str -> (String.concat
                                                           "" [str;"\n";"key : "; key ; "," ; "value : "; value ; "\n"]) ) solHt#getReverseHashTable "" in
  (isSolvable,
   if isSolvable then
     String.concat " "  ["Solvable : "; output ; hashMappings]
   else
     String.concat " " [output ; hashMappings])


let quick_solve goal =
  let hypothesisAssertionSubsets = [getHypothesisAssertions goal] in
  let sortedHypothesisAssertionSubsets =  List.sort listCmp hypothesisAssertionSubsets in
  let translatedSortedHypoAssertionSubsets = List.map (fun hypoAssertions ->

    let ht = new hashTable 100 in
    let assertions = (translateHypothesisAssertions hypoAssertions ht) in
    (assertions,ht))
    sortedHypothesisAssertionSubsets in
  let goalAssertion = getGoalAssertion goal in
  let (isSolvable,output,solHt) = List.fold_left (fun b hypoAssertions->
    (
      match b with
      | (false,_,_)->
	let (assertions,ht) = hypoAssertions in
	let _ = (translateGoalAssertion goalAssertion ht) in
	let z3Output = (solveUsingZ3 assertions goalAssertion) in
	if contains z3Output "unsat" then
	  let assertionNames =List.map (fun assertion -> assertion#getName) assertions in
	  (true,String.concat " " assertionNames,ht) else (false,z3Output,ht)
      | (true,_,_) ->
	b
    ) ) (false,"",new hashTable 100) translatedSortedHypoAssertionSubsets in

  let hashMappings = Hashtbl.fold (fun key value str -> (String.concat
                                                           "" [str;"\n";"key : "; key ; "," ; "value : "; value ; "\n"]) ) solHt#getReverseHashTable "" in
  (isSolvable
  , if isSolvable = true then
      String.concat " "  ["Solvable : "; output ; hashMappings]
    else
      String.concat " " [output ; hashMappings])



let z3_quick_solve = fun gl ->
  if fst (quick_solve (Tacmach.pf_concl gl)) then
    Tacticals.tclIDTAC gl
  else
    Tacticals.tclFAIL 1 (Pp.str "z3 failed to solve the goal") gl









let z3Tactic  = fun gl ->

  (* the type of [c] is [ty] *)
  let goal = Tacmach.pf_concl gl in

  let output = ref "" in
  let store str = output := str in
  let pp_print () = !output in

  let (is_solved,resultStr) = findTheSmallestSubsetGoalSolver goal in
  let _ = store resultStr in

 (*
  let hashTableMappings = ref [] in

  let toStringKeyValuePair key value =  (hashTableMappings:= List.append !hashTableMappings ["\n"; key ; ":"; value ; "\n"]) in

   let ht = new hashTable 100 in
   let finalZ3Stmts = getTranslatedAssertions goal ht in
   let  _ =(
   match finalZ3Stmts with
   | "" ->   Format.printf "NOT REAL ARITHMETIC"
   | _ ->
	   let file = "/tmp/z3.txt" in
	   let oc = open_out file in
	   let _ = fprintf oc "%s\n" finalZ3Stmts in
	   let _ = close_out oc in
	   let command = String.concat "" ["z3 -smt2 " ; file ]  in
	   let _ = Format.printf "Z3 Statements : %s\n" finalZ3Stmts in
	   let _ = Format.printf "COMMAND  : %s\n" command  in
   	   let z3Output = read_process command in
	   let _ = Hashtbl.iter toStringKeyValuePair ht#getReverseHashTable  in
           let outputStr = String.concat "" (List.append  [z3Output ; "\n" ;  ] !hashTableMappings)   in
	   store outputStr
   ) in
   let s = getAllSubsets ["1";"2";"3";"4"] in
   let sortedList = List.sort listCmp s in
   let _ = printListOfLists sortedList in
*)
   let _ = Pp.msgnl (Pp.str (pp_print ())) in
   if is_solved then
     Tacticals.tclIDTAC gl
   else
     Tacticals.tclFAIL 1 (Pp.str "z3 failed to solve the goal") gl

TACTIC EXTEND z3_tac
  | ["z3Tactic"] ->     [z3Tactic]
END;;

TACTIC EXTEND z3_tac_quick
  | ["z3" "quick" "solve"] ->     [z3Tactic]
END;;
