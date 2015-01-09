open BinNums
open Datatypes

(** val digits2_Pnat : positive -> nat **)

let rec digits2_Pnat = function
| Coq_xI p -> S (digits2_Pnat p)
| Coq_xO p -> S (digits2_Pnat p)
| Coq_xH -> O

