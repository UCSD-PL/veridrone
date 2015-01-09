open Compare_dec
open Datatypes
open Int31

type 'a coq_Comparable =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_Comparable *)

(** val compare : 'a1 coq_Comparable -> 'a1 -> 'a1 -> comparison **)

let compare comparable =
  comparable

(** val natComparable : nat coq_Comparable **)

let natComparable =
  nat_compare

(** val coq_PairComparable :
    'a1 coq_Comparable -> 'a2 coq_Comparable -> ('a1 * 'a2) coq_Comparable **)

let coq_PairComparable cA cB x y =
  let (xa, xb) = x in
  let (ya, yb) = y in
  (match compare cA xa ya with
   | Eq -> compare cB xb yb
   | _ -> compare cA xa ya)

(** val compare_eqb : 'a1 coq_Comparable -> 'a1 -> 'a1 -> bool **)

let compare_eqb c x y =
  match compare c x y with
  | Eq -> true
  | _ -> false

(** val compare_eqdec : 'a1 coq_Comparable -> 'a1 -> 'a1 -> bool **)

let compare_eqdec c x y =
  let c0 = compare c x y in
  (match c0 with
   | Eq -> true
   | _ -> false)

type 'a coq_Finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

(** val all_list : 'a1 coq_Finite -> 'a1 list **)

let all_list finite =
  finite

type 'a coq_Alphabet = { coq_AlphabetComparable : 'a coq_Comparable;
                         coq_AlphabetFinite : 'a coq_Finite }

(** val coq_AlphabetComparable : 'a1 coq_Alphabet -> 'a1 coq_Comparable **)

let coq_AlphabetComparable x = x.coq_AlphabetComparable

(** val coq_AlphabetFinite : 'a1 coq_Alphabet -> 'a1 coq_Finite **)

let coq_AlphabetFinite x = x.coq_AlphabetFinite

type 'a coq_Numbered = { inj : ('a -> int); surj : (int -> 'a);
                         inj_bound : int }

(** val inj : 'a1 coq_Numbered -> 'a1 -> int **)

let inj x = x.inj

(** val surj : 'a1 coq_Numbered -> int -> 'a1 **)

let surj x = x.surj

(** val inj_bound : 'a1 coq_Numbered -> int **)

let inj_bound x = x.inj_bound

(** val coq_NumberedAlphabet : 'a1 coq_Numbered -> 'a1 coq_Alphabet **)

let coq_NumberedAlphabet n =
  { coq_AlphabetComparable = (fun x y -> compare31 (n.inj x) (n.inj y));
    coq_AlphabetFinite =
    (fst
      (iter_int31 n.inj_bound (fun p -> (((n.surj (snd p)) :: (fst p)),
        (incr (snd p)))) ([], (Camlcoq.Int31.constr (false, false, false,
        false, false, false, false, false, false, false, false, false, false,
        false, false, false, false, false, false, false, false, false, false,
        false, false, false, false, false, false, false, false))))) }

module type ComparableM = 
 sig 
  type t 
  
  val tComparable : t coq_Comparable
 end

module OrderedTypeAlt_from_ComparableM = 
 functor (C:ComparableM) ->
 struct 
  type t = C.t
  
  (** val compare : t -> t -> comparison **)
  
  let compare =
    compare C.tComparable
 end

module OrderedType_from_ComparableM = 
 functor (C:ComparableM) ->
 struct 
  module Alt = OrderedTypeAlt_from_ComparableM(C)
  
  type t = Alt.t
  
  (** val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare **)
  
  let compare x y =
    match Alt.compare x y with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT
  
  (** val eq_dec : Alt.t -> Alt.t -> bool **)
  
  let eq_dec x y =
    match Alt.compare x y with
    | Eq -> true
    | _ -> false
 end

