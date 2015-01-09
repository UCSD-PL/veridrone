open AST
open BinInt
open BinNums
open Bool
open Compopts
open Coqlib
open Datatypes
open Floats
open Integers
open Lattice
open Maps
open Memdata
open Registers
open Zpower

type abool =
| Bnone
| Just of bool
| Maybe of bool
| Btop

(** val club : abool -> abool -> abool **)

let club x y =
  match x with
  | Bnone ->
    (match y with
     | Just b -> Maybe b
     | x0 -> x0)
  | Just b1 ->
    (match y with
     | Bnone -> Maybe b1
     | Just b2 -> if eqb b1 b2 then x else Btop
     | Maybe b2 -> if eqb b1 b2 then y else Btop
     | Btop -> Btop)
  | Maybe b1 ->
    (match y with
     | Bnone -> Maybe b1
     | Just b2 -> if eqb b1 b2 then x else Btop
     | Maybe b2 -> if eqb b1 b2 then x else Btop
     | Btop -> Btop)
  | Btop -> Btop

(** val cnot : abool -> abool **)

let cnot x = match x with
| Just b -> Just (negb b)
| Maybe b -> Maybe (negb b)
| _ -> x

type aptr =
| Pbot
| Gl of ident * Int.int
| Glo of ident
| Glob
| Stk of Int.int
| Stack
| Nonstack
| Ptop

(** val eq_aptr : aptr -> aptr -> bool **)

let eq_aptr p1 p2 =
  match p1 with
  | Pbot ->
    (match p2 with
     | Pbot -> true
     | _ -> false)
  | Gl (x, x0) ->
    (match p2 with
     | Gl (id0, ofs0) -> if ident_eq x id0 then Int.eq_dec x0 ofs0 else false
     | _ -> false)
  | Glo x ->
    (match p2 with
     | Glo id0 -> ident_eq x id0
     | _ -> false)
  | Glob ->
    (match p2 with
     | Glob -> true
     | _ -> false)
  | Stk x ->
    (match p2 with
     | Stk ofs0 -> Int.eq_dec x ofs0
     | _ -> false)
  | Stack ->
    (match p2 with
     | Stack -> true
     | _ -> false)
  | Nonstack ->
    (match p2 with
     | Nonstack -> true
     | _ -> false)
  | Ptop ->
    (match p2 with
     | Ptop -> true
     | _ -> false)

(** val plub : aptr -> aptr -> aptr **)

let plub p q =
  match p with
  | Pbot -> q
  | Gl (id1, ofs1) ->
    (match q with
     | Pbot -> p
     | Gl (id2, ofs2) ->
       if ident_eq id1 id2
       then if Int.eq_dec ofs1 ofs2 then p else Glo id1
       else Glob
     | Glo id2 -> if ident_eq id1 id2 then q else Glob
     | Glob -> Glob
     | Nonstack -> Nonstack
     | _ -> Ptop)
  | Glo id1 ->
    (match q with
     | Pbot -> p
     | Gl (id2, ofs2) -> if ident_eq id1 id2 then p else Glob
     | Glo id2 -> if ident_eq id1 id2 then p else Glob
     | Glob -> Glob
     | Nonstack -> Nonstack
     | _ -> Ptop)
  | Glob ->
    (match q with
     | Pbot -> p
     | Stk ofs -> Ptop
     | Stack -> Ptop
     | Nonstack -> Nonstack
     | Ptop -> Ptop
     | _ -> Glob)
  | Stk ofs1 ->
    (match q with
     | Pbot -> p
     | Stk ofs2 -> if Int.eq_dec ofs1 ofs2 then p else Stack
     | Stack -> Stack
     | _ -> Ptop)
  | Stack ->
    (match q with
     | Pbot -> p
     | Stk ofs -> Stack
     | Stack -> Stack
     | _ -> Ptop)
  | Nonstack ->
    (match q with
     | Pbot -> p
     | Stk ofs -> Ptop
     | Stack -> Ptop
     | Ptop -> Ptop
     | _ -> Nonstack)
  | Ptop ->
    (match q with
     | Pbot -> p
     | _ -> Ptop)

(** val pincl : aptr -> aptr -> bool **)

let pincl p q =
  match p with
  | Pbot -> true
  | Gl (id1, ofs1) ->
    (match q with
     | Pbot -> false
     | Gl (id2, ofs2) ->
       (&&) ((fun x -> x) (peq id1 id2))
         ((fun x -> x) (Int.eq_dec ofs1 ofs2))
     | Glo id2 -> (fun x -> x) (peq id1 id2)
     | Stk ofs -> false
     | Stack -> false
     | _ -> true)
  | Glo id1 ->
    (match q with
     | Glo id2 -> (fun x -> x) (peq id1 id2)
     | Glob -> true
     | Nonstack -> true
     | Ptop -> true
     | _ -> false)
  | Glob ->
    (match q with
     | Glob -> true
     | Nonstack -> true
     | Ptop -> true
     | _ -> false)
  | Stk ofs1 ->
    (match q with
     | Stk ofs2 -> (fun x -> x) (Int.eq_dec ofs1 ofs2)
     | Stack -> true
     | Ptop -> true
     | _ -> false)
  | Nonstack ->
    (match q with
     | Nonstack -> true
     | Ptop -> true
     | _ -> false)
  | _ ->
    (match q with
     | Ptop -> true
     | _ -> false)

(** val padd : aptr -> Int.int -> aptr **)

let padd p n =
  match p with
  | Gl (id, ofs) -> Gl (id, (Int.add ofs n))
  | Stk ofs -> Stk (Int.add ofs n)
  | _ -> p

(** val psub : aptr -> Int.int -> aptr **)

let psub p n =
  match p with
  | Gl (id, ofs) -> Gl (id, (Int.sub ofs n))
  | Stk ofs -> Stk (Int.sub ofs n)
  | _ -> p

(** val poffset : aptr -> aptr **)

let poffset p = match p with
| Gl (id, ofs) -> Glo id
| Stk ofs -> Stack
| _ -> p

(** val cmp_different_blocks : comparison -> abool **)

let cmp_different_blocks = function
| Ceq -> Maybe false
| Cne -> Maybe true
| _ -> Bnone

(** val pcmp : comparison -> aptr -> aptr -> abool **)

let pcmp c p1 p2 =
  match p1 with
  | Pbot -> Bnone
  | Gl (id1, ofs1) ->
    (match p2 with
     | Pbot -> Bnone
     | Gl (id2, ofs2) ->
       if peq id1 id2
       then Maybe (Int.cmpu c ofs1 ofs2)
       else cmp_different_blocks c
     | Glo id2 -> if peq id1 id2 then Btop else cmp_different_blocks c
     | Stk ofs -> cmp_different_blocks c
     | Stack -> cmp_different_blocks c
     | _ -> Btop)
  | Glo id1 ->
    (match p2 with
     | Pbot -> Bnone
     | Gl (id2, ofs2) -> if peq id1 id2 then Btop else cmp_different_blocks c
     | Glo id2 -> if peq id1 id2 then Btop else cmp_different_blocks c
     | Stk ofs -> cmp_different_blocks c
     | Stack -> cmp_different_blocks c
     | _ -> Btop)
  | Stk ofs1 ->
    (match p2 with
     | Pbot -> Bnone
     | Stk ofs2 -> Maybe (Int.cmpu c ofs1 ofs2)
     | Stack -> Btop
     | Ptop -> Btop
     | _ -> cmp_different_blocks c)
  | Stack ->
    (match p2 with
     | Pbot -> Bnone
     | Stk ofs -> Btop
     | Stack -> Btop
     | Ptop -> Btop
     | _ -> cmp_different_blocks c)
  | Ptop ->
    (match p2 with
     | Pbot -> Bnone
     | _ -> Btop)
  | _ ->
    (match p2 with
     | Pbot -> Bnone
     | Stk ofs -> cmp_different_blocks c
     | Stack -> cmp_different_blocks c
     | _ -> Btop)

(** val pdisjoint : aptr -> coq_Z -> aptr -> coq_Z -> bool **)

let pdisjoint p1 sz1 p2 sz2 =
  match p1 with
  | Pbot -> true
  | Gl (id1, ofs1) ->
    (match p2 with
     | Gl (id2, ofs2) ->
       if peq id1 id2
       then (||)
              ((fun x -> x)
                (zle (Z.add (Int.unsigned ofs1) sz1) (Int.unsigned ofs2)))
              ((fun x -> x)
                (zle (Z.add (Int.unsigned ofs2) sz2) (Int.unsigned ofs1)))
       else true
     | Glo id2 -> negb ((fun x -> x) (peq id1 id2))
     | Glob -> false
     | Nonstack -> false
     | Ptop -> false
     | _ -> true)
  | Glo id1 ->
    (match p2 with
     | Gl (id2, ofs2) -> negb ((fun x -> x) (peq id1 id2))
     | Glo id2 -> negb ((fun x -> x) (peq id1 id2))
     | Glob -> false
     | Nonstack -> false
     | Ptop -> false
     | _ -> true)
  | Stk ofs1 ->
    (match p2 with
     | Stk ofs2 ->
       (||)
         ((fun x -> x)
           (zle (Z.add (Int.unsigned ofs1) sz1) (Int.unsigned ofs2)))
         ((fun x -> x)
           (zle (Z.add (Int.unsigned ofs2) sz2) (Int.unsigned ofs1)))
     | Stack -> false
     | Ptop -> false
     | _ -> true)
  | Stack ->
    (match p2 with
     | Stk ofs -> false
     | Stack -> false
     | Ptop -> false
     | _ -> true)
  | Ptop ->
    (match p2 with
     | Pbot -> true
     | _ -> false)
  | _ ->
    (match p2 with
     | Pbot -> true
     | Stk ofs -> true
     | Stack -> true
     | _ -> false)

type aval =
| Vbot
| I of Int.int
| Uns of coq_Z
| Sgn of coq_Z
| L of Int64.int
| F of float
| FS of float32
| Ptr of aptr
| Ifptr of aptr

(** val eq_aval : aval -> aval -> bool **)

let eq_aval v1 v2 =
  match v1 with
  | Vbot ->
    (match v2 with
     | Vbot -> true
     | _ -> false)
  | I x ->
    (match v2 with
     | I n0 -> Int.eq_dec x n0
     | _ -> false)
  | Uns x ->
    (match v2 with
     | Uns n0 -> zeq x n0
     | _ -> false)
  | Sgn x ->
    (match v2 with
     | Sgn n0 -> zeq x n0
     | _ -> false)
  | L x ->
    (match v2 with
     | L n0 -> Int64.eq_dec x n0
     | _ -> false)
  | F x ->
    (match v2 with
     | F f0 -> Float.eq_dec x f0
     | _ -> false)
  | FS x ->
    (match v2 with
     | FS f0 -> Float32.eq_dec x f0
     | _ -> false)
  | Ptr x ->
    (match v2 with
     | Ptr p0 -> eq_aptr x p0
     | _ -> false)
  | Ifptr x ->
    (match v2 with
     | Ifptr p0 -> eq_aptr x p0
     | _ -> false)

(** val coq_Vtop : aval **)

let coq_Vtop =
  Ifptr Ptop

(** val itop : aval **)

let itop =
  Ifptr Pbot

(** val ftop : aval **)

let ftop =
  Ifptr Pbot

(** val ltop : aval **)

let ltop =
  Ifptr Pbot

(** val usize : Int.int -> coq_Z **)

let usize =
  Int.size

(** val ssize : Int.int -> coq_Z **)

let ssize i =
  Z.add (Int.size (if Int.lt i Int.zero then Int.not i else i)) (Zpos Coq_xH)

(** val uns : coq_Z -> aval **)

let uns n =
  if zle n (Zpos Coq_xH)
  then Uns (Zpos Coq_xH)
  else if zle n (Zpos (Coq_xI (Coq_xI Coq_xH)))
       then Uns (Zpos (Coq_xI (Coq_xI Coq_xH)))
       else if zle n (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
            then Uns (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
            else if zle n (Zpos (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
                 then Uns (Zpos (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
                 else if zle n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                           Coq_xH)))))
                      then Uns (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                             Coq_xH)))))
                      else itop

(** val sgn : coq_Z -> aval **)

let sgn n =
  if zle n (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  then Sgn (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  else if zle n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
       then Sgn (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
       else itop

(** val vlub : aval -> aval -> aval **)

let vlub v w =
  match v with
  | Vbot -> w
  | I i ->
    (match w with
     | Vbot -> v
     | I i2 ->
       if Int.eq i i2
       then v
       else if (||) (Int.lt i Int.zero) (Int.lt i2 Int.zero)
            then sgn (Z.max (ssize i) (ssize i2))
            else uns (Z.max (usize i) (usize i2))
     | Uns n ->
       if Int.lt i Int.zero
       then sgn (Z.max (ssize i) (Z.add n (Zpos Coq_xH)))
       else uns (Z.max (usize i) n)
     | Sgn n -> sgn (Z.max (ssize i) n)
     | Ptr p ->
       if (||) (va_strict ()) (Int.eq i Int.zero) then Ifptr p else coq_Vtop
     | Ifptr p ->
       if (||) (va_strict ()) (Int.eq i Int.zero) then Ifptr p else coq_Vtop
     | _ -> coq_Vtop)
  | Uns n1 ->
    (match w with
     | Vbot -> v
     | I i ->
       if Int.lt i Int.zero
       then sgn (Z.max (ssize i) (Z.add n1 (Zpos Coq_xH)))
       else uns (Z.max (usize i) n1)
     | Uns n2 -> Uns (Z.max n1 n2)
     | Sgn n2 -> sgn (Z.max (Z.add n1 (Zpos Coq_xH)) n2)
     | Ptr p -> if va_strict () then Ifptr p else coq_Vtop
     | Ifptr p -> if va_strict () then Ifptr p else coq_Vtop
     | _ -> coq_Vtop)
  | Sgn n1 ->
    (match w with
     | Vbot -> v
     | I i -> sgn (Z.max (ssize i) n1)
     | Uns n2 -> sgn (Z.max n1 (Z.add n2 (Zpos Coq_xH)))
     | Sgn n2 -> sgn (Z.max n1 n2)
     | Ptr p -> if va_strict () then Ifptr p else coq_Vtop
     | Ifptr p -> if va_strict () then Ifptr p else coq_Vtop
     | _ -> coq_Vtop)
  | L i1 ->
    (match w with
     | Vbot -> v
     | L i2 -> if Int64.eq i1 i2 then v else ltop
     | Ptr p -> if va_strict () then Ifptr p else coq_Vtop
     | Ifptr p -> if va_strict () then Ifptr p else coq_Vtop
     | _ -> coq_Vtop)
  | F f1 ->
    (match w with
     | Vbot -> v
     | F f2 -> if Float.eq_dec f1 f2 then v else ftop
     | Ptr p -> if va_strict () then Ifptr p else coq_Vtop
     | Ifptr p -> if va_strict () then Ifptr p else coq_Vtop
     | _ -> coq_Vtop)
  | FS f1 ->
    (match w with
     | Vbot -> v
     | FS f2 -> if Float32.eq_dec f1 f2 then v else ftop
     | Ptr p -> if va_strict () then Ifptr p else coq_Vtop
     | Ifptr p -> if va_strict () then Ifptr p else coq_Vtop
     | _ -> coq_Vtop)
  | Ptr p ->
    (match w with
     | Vbot -> v
     | I i ->
       if (||) (va_strict ()) (Int.eq i Int.zero) then Ifptr p else coq_Vtop
     | Ptr p0 -> Ptr (plub p p0)
     | Ifptr p0 -> Ifptr (plub p p0)
     | _ -> if va_strict () then Ifptr p else coq_Vtop)
  | Ifptr p ->
    (match w with
     | Vbot -> v
     | I i ->
       if (||) (va_strict ()) (Int.eq i Int.zero) then Ifptr p else coq_Vtop
     | Ptr p0 -> Ifptr (plub p p0)
     | Ifptr p0 -> Ifptr (plub p p0)
     | _ -> if va_strict () then Ifptr p else coq_Vtop)

(** val aptr_of_aval : aval -> aptr **)

let aptr_of_aval = function
| Ptr p -> p
| Ifptr p -> p
| _ -> Pbot

(** val vplub : aval -> aptr -> aptr **)

let vplub v p =
  match v with
  | Ptr q -> plub q p
  | Ifptr q -> plub q p
  | _ -> p

(** val vpincl : aval -> aptr -> bool **)

let vpincl v p =
  match v with
  | Ptr q -> pincl q p
  | Ifptr q -> pincl q p
  | _ -> true

(** val vincl : aval -> aval -> bool **)

let vincl v w =
  match v with
  | Vbot -> true
  | I i ->
    (match w with
     | I j -> (fun x -> x) (Int.eq_dec i j)
     | Uns n ->
       (&&) ((fun x -> x) (Int.eq_dec (Int.zero_ext n i) i))
         ((fun x -> x) (zle Z0 n))
     | Sgn n ->
       (&&) ((fun x -> x) (Int.eq_dec (Int.sign_ext n i) i))
         ((fun x -> x) (zlt Z0 n))
     | Ifptr p -> true
     | _ -> false)
  | Uns n ->
    (match w with
     | Uns m -> (fun x -> x) (zle n m)
     | Sgn m -> (fun x -> x) (zlt n m)
     | Ifptr p -> true
     | _ -> false)
  | Sgn n ->
    (match w with
     | Sgn m -> (fun x -> x) (zle n m)
     | Ifptr p -> true
     | _ -> false)
  | L i ->
    (match w with
     | L j -> (fun x -> x) (Int64.eq_dec i j)
     | Ifptr p -> true
     | _ -> false)
  | F i ->
    (match w with
     | F j -> (fun x -> x) (Float.eq_dec i j)
     | Ifptr p -> true
     | _ -> false)
  | FS i ->
    (match w with
     | FS j -> (fun x -> x) (Float32.eq_dec i j)
     | Ifptr p -> true
     | _ -> false)
  | Ptr p ->
    (match w with
     | Ptr q -> pincl p q
     | Ifptr q -> pincl p q
     | _ -> false)
  | Ifptr p ->
    (match w with
     | Ifptr q -> pincl p q
     | _ -> false)

(** val unop_int : (Int.int -> Int.int) -> aval -> aval **)

let unop_int sem = function
| I n -> I (sem n)
| _ -> itop

(** val binop_int :
    (Int.int -> Int.int -> Int.int) -> aval -> aval -> aval **)

let binop_int sem x y =
  match x with
  | I n ->
    (match y with
     | I m -> I (sem n m)
     | _ -> itop)
  | _ -> itop

(** val unop_float : (float -> float) -> aval -> aval **)

let unop_float sem = function
| F n -> F (sem n)
| _ -> ftop

(** val binop_float : (float -> float -> float) -> aval -> aval -> aval **)

let binop_float sem x y =
  match x with
  | F n ->
    (match y with
     | F m -> F (sem n m)
     | _ -> ftop)
  | _ -> ftop

(** val unop_single : (float32 -> float32) -> aval -> aval **)

let unop_single sem = function
| FS n -> FS (sem n)
| _ -> ftop

(** val binop_single :
    (float32 -> float32 -> float32) -> aval -> aval -> aval **)

let binop_single sem x y =
  match x with
  | FS n ->
    (match y with
     | FS m -> FS (sem n m)
     | _ -> ftop)
  | _ -> ftop

(** val shl : aval -> aval -> aval **)

let shl v = function
| I amount ->
  if Int.ltu amount Int.iwordsize
  then (match v with
        | I i -> I (Int.shl i amount)
        | Uns n -> uns (Z.add n (Int.unsigned amount))
        | Sgn n -> sgn (Z.add n (Int.unsigned amount))
        | _ -> itop)
  else itop
| _ -> itop

(** val shru : aval -> aval -> aval **)

let shru v = function
| I amount ->
  if Int.ltu amount Int.iwordsize
  then (match v with
        | I i -> I (Int.shru i amount)
        | Uns n -> uns (Z.sub n (Int.unsigned amount))
        | _ -> uns (Z.sub Int.zwordsize (Int.unsigned amount)))
  else itop
| _ -> itop

(** val shr : aval -> aval -> aval **)

let shr v = function
| I amount ->
  if Int.ltu amount Int.iwordsize
  then (match v with
        | I i -> I (Int.shr i amount)
        | Uns n -> sgn (Z.sub (Z.add n (Zpos Coq_xH)) (Int.unsigned amount))
        | Sgn n -> sgn (Z.sub n (Int.unsigned amount))
        | _ -> sgn (Z.sub Int.zwordsize (Int.unsigned amount)))
  else itop
| _ -> itop

(** val coq_and : aval -> aval -> aval **)

let coq_and v w =
  match v with
  | I i ->
    (match w with
     | I i0 -> I (Int.coq_and i i0)
     | Uns n -> uns (Z.min n (usize i))
     | _ -> uns (usize i))
  | Uns n ->
    (match w with
     | I i -> uns (Z.min n (usize i))
     | Uns n0 -> uns (Z.min n n0)
     | _ -> uns n)
  | Sgn n1 ->
    (match w with
     | I i -> uns (usize i)
     | Uns n -> uns n
     | Sgn n2 -> sgn (Z.max n1 n2)
     | _ -> itop)
  | _ ->
    (match w with
     | I i -> uns (usize i)
     | Uns n -> uns n
     | _ -> itop)

(** val coq_or : aval -> aval -> aval **)

let coq_or v w =
  match v with
  | I i ->
    (match w with
     | I i2 -> I (Int.coq_or i i2)
     | Uns n -> uns (Z.max n (usize i))
     | _ -> itop)
  | Uns n1 ->
    (match w with
     | I i -> uns (Z.max n1 (usize i))
     | Uns n2 -> uns (Z.max n1 n2)
     | _ -> itop)
  | Sgn n1 ->
    (match w with
     | Sgn n2 -> sgn (Z.max n1 n2)
     | _ -> itop)
  | _ -> itop

(** val xor : aval -> aval -> aval **)

let xor v w =
  match v with
  | I i ->
    (match w with
     | I i2 -> I (Int.xor i i2)
     | Uns n -> uns (Z.max n (usize i))
     | _ -> itop)
  | Uns n1 ->
    (match w with
     | I i -> uns (Z.max n1 (usize i))
     | Uns n2 -> uns (Z.max n1 n2)
     | _ -> itop)
  | Sgn n1 ->
    (match w with
     | Sgn n2 -> sgn (Z.max n1 n2)
     | _ -> itop)
  | _ -> itop

(** val notint : aval -> aval **)

let notint = function
| I i -> I (Int.not i)
| Uns n -> sgn (Z.add n (Zpos Coq_xH))
| Sgn n -> Sgn n
| _ -> itop

(** val ror : aval -> aval -> aval **)

let ror x = function
| I j ->
  (match x with
   | I i -> if Int.ltu j Int.iwordsize then I (Int.ror i j) else itop
   | _ -> itop)
| _ -> itop

(** val neg : aval -> aval **)

let neg =
  unop_int Int.neg

(** val add : aval -> aval -> aval **)

let add x y =
  match x with
  | I i ->
    (match y with
     | I j -> I (Int.add i j)
     | Ptr p -> Ptr (padd p i)
     | Ifptr p -> Ifptr (padd p i)
     | _ -> coq_Vtop)
  | Ptr p ->
    (match y with
     | I i -> Ptr (padd p i)
     | _ -> Ptr (poffset p))
  | Ifptr p ->
    (match y with
     | I i -> Ifptr (padd p i)
     | Ptr p0 -> Ptr (poffset p0)
     | Ifptr p0 -> Ifptr (plub (poffset p) (poffset p0))
     | _ -> Ifptr (poffset p))
  | _ ->
    (match y with
     | Ptr p -> Ptr (poffset p)
     | Ifptr p -> Ifptr (poffset p)
     | _ -> coq_Vtop)

(** val sub : aval -> aval -> aval **)

let sub v w =
  match v with
  | I i1 ->
    (match w with
     | I i2 -> I (Int.sub i1 i2)
     | _ -> coq_Vtop)
  | Ptr p ->
    (match w with
     | I i -> Ptr (psub p i)
     | _ -> Ifptr (poffset p))
  | Ifptr p1 ->
    (match w with
     | I i -> Ifptr (psub p1 i)
     | Uns n -> Ifptr (poffset p1)
     | Sgn n -> Ifptr (poffset p1)
     | Ptr p2 -> itop
     | _ -> coq_Vtop)
  | _ -> coq_Vtop

(** val mul : aval -> aval -> aval **)

let mul =
  binop_int Int.mul

(** val mulhs : aval -> aval -> aval **)

let mulhs =
  binop_int Int.mulhs

(** val mulhu : aval -> aval -> aval **)

let mulhu =
  binop_int Int.mulhu

(** val divs : aval -> aval -> aval **)

let divs v = function
| I i2 ->
  (match v with
   | I i1 ->
     if (||) (Int.eq i2 Int.zero)
          ((&&) (Int.eq i1 (Int.repr Int.min_signed)) (Int.eq i2 Int.mone))
     then if va_strict () then Vbot else itop
     else I (Int.divs i1 i2)
   | _ -> itop)
| _ -> itop

(** val divu : aval -> aval -> aval **)

let divu v = function
| I i2 ->
  (match v with
   | I i1 ->
     if Int.eq i2 Int.zero
     then if va_strict () then Vbot else itop
     else I (Int.divu i1 i2)
   | _ -> itop)
| _ -> itop

(** val mods : aval -> aval -> aval **)

let mods v = function
| I i2 ->
  (match v with
   | I i1 ->
     if (||) (Int.eq i2 Int.zero)
          ((&&) (Int.eq i1 (Int.repr Int.min_signed)) (Int.eq i2 Int.mone))
     then if va_strict () then Vbot else itop
     else I (Int.mods i1 i2)
   | _ -> itop)
| _ -> itop

(** val modu : aval -> aval -> aval **)

let modu v = function
| I i2 ->
  (match v with
   | I i1 ->
     if Int.eq i2 Int.zero
     then if va_strict () then Vbot else itop
     else I (Int.modu i1 i2)
   | _ -> uns (usize i2))
| _ -> itop

(** val shrx : aval -> aval -> aval **)

let shrx v w =
  match v with
  | I i ->
    (match w with
     | I j ->
       if Int.ltu j
            (Int.repr (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
       then I (Int.shrx i j)
       else itop
     | _ -> itop)
  | _ -> itop

(** val negf : aval -> aval **)

let negf =
  unop_float Float.neg

(** val absf : aval -> aval **)

let absf =
  unop_float Float.abs

(** val addf : aval -> aval -> aval **)

let addf =
  binop_float Float.add

(** val subf : aval -> aval -> aval **)

let subf =
  binop_float Float.sub

(** val mulf : aval -> aval -> aval **)

let mulf =
  binop_float Float.mul

(** val divf : aval -> aval -> aval **)

let divf =
  binop_float Float.div

(** val negfs : aval -> aval **)

let negfs =
  unop_single Float32.neg

(** val absfs : aval -> aval **)

let absfs =
  unop_single Float32.abs

(** val addfs : aval -> aval -> aval **)

let addfs =
  binop_single Float32.add

(** val subfs : aval -> aval -> aval **)

let subfs =
  binop_single Float32.sub

(** val mulfs : aval -> aval -> aval **)

let mulfs =
  binop_single Float32.mul

(** val divfs : aval -> aval -> aval **)

let divfs =
  binop_single Float32.div

(** val zero_ext : coq_Z -> aval -> aval **)

let zero_ext nbits = function
| I i -> I (Int.zero_ext nbits i)
| Uns n -> uns (Z.min n nbits)
| _ -> uns nbits

(** val sign_ext : coq_Z -> aval -> aval **)

let sign_ext nbits = function
| I i -> I (Int.sign_ext nbits i)
| Uns n -> if zlt n nbits then Uns n else sgn nbits
| Sgn n -> sgn (Z.min n nbits)
| _ -> sgn nbits

(** val singleoffloat : aval -> aval **)

let singleoffloat = function
| F f -> FS (Float.to_single f)
| _ -> ftop

(** val floatofsingle : aval -> aval **)

let floatofsingle = function
| FS f -> F (Float.of_single f)
| _ -> ftop

(** val intoffloat : aval -> aval **)

let intoffloat = function
| F f ->
  (match Float.to_int f with
   | Some i -> I i
   | None -> if va_strict () then Vbot else itop)
| _ -> itop

(** val floatofint : aval -> aval **)

let floatofint = function
| I i -> F (Float.of_int i)
| _ -> ftop

(** val intofsingle : aval -> aval **)

let intofsingle = function
| FS f ->
  (match Float32.to_int f with
   | Some i -> I i
   | None -> if va_strict () then Vbot else itop)
| _ -> itop

(** val singleofint : aval -> aval **)

let singleofint = function
| I i -> FS (Float32.of_int i)
| _ -> ftop

(** val longofwords : aval -> aval -> aval **)

let longofwords x y =
  match x with
  | I i ->
    (match y with
     | I j -> L (Int64.ofwords i j)
     | _ -> ltop)
  | _ -> ltop

(** val loword : aval -> aval **)

let loword = function
| L i -> I (Int64.loword i)
| _ -> itop

(** val hiword : aval -> aval **)

let hiword = function
| L i -> I (Int64.hiword i)
| _ -> itop

(** val cmp_intv : comparison -> (coq_Z * coq_Z) -> coq_Z -> abool **)

let cmp_intv c i n =
  let (lo, hi) = i in
  (match c with
   | Ceq ->
     if (||) ((fun x -> x) (zlt n lo)) ((fun x -> x) (zlt hi n))
     then Maybe false
     else Btop
   | Cne -> Btop
   | Clt ->
     if zlt hi n then Maybe true else if zle n lo then Maybe false else Btop
   | Cle ->
     if zle hi n then Maybe true else if zlt n lo then Maybe false else Btop
   | Cgt ->
     if zlt n lo then Maybe true else if zle hi n then Maybe false else Btop
   | Cge ->
     if zle n lo then Maybe true else if zlt hi n then Maybe false else Btop)

(** val uintv : aval -> coq_Z * coq_Z **)

let uintv = function
| I n -> ((Int.unsigned n), (Int.unsigned n))
| Uns n ->
  if zlt n Int.zwordsize
  then (Z0, (Z.sub (two_p n) (Zpos Coq_xH)))
  else (Z0, Int.max_unsigned)
| _ -> (Z0, Int.max_unsigned)

(** val sintv : aval -> coq_Z * coq_Z **)

let sintv = function
| I n -> ((Int.signed n), (Int.signed n))
| Uns n ->
  if zlt n Int.zwordsize
  then (Z0, (Z.sub (two_p n) (Zpos Coq_xH)))
  else (Int.min_signed, Int.max_signed)
| Sgn n ->
  if zlt n Int.zwordsize
  then let x = two_p (Z.sub n (Zpos Coq_xH)) in
       ((Z.opp x), (Z.sub x (Zpos Coq_xH)))
  else (Int.min_signed, Int.max_signed)
| _ -> (Int.min_signed, Int.max_signed)

(** val cmpu_bool : comparison -> aval -> aval -> abool **)

let cmpu_bool c v w =
  match v with
  | I i ->
    (match w with
     | I i0 -> Just (Int.cmpu c i i0)
     | Ptr p -> cmp_different_blocks c
     | _ ->
       club (cmp_intv (swap_comparison c) (uintv w) (Int.unsigned i))
         (cmp_different_blocks c))
  | Uns n ->
    (match w with
     | I i ->
       club (cmp_intv c (uintv v) (Int.unsigned i)) (cmp_different_blocks c)
     | Ptr p -> cmp_different_blocks c
     | _ -> Btop)
  | Sgn n ->
    (match w with
     | I i ->
       club (cmp_intv c (uintv v) (Int.unsigned i)) (cmp_different_blocks c)
     | Ptr p -> cmp_different_blocks c
     | _ -> Btop)
  | Ptr p1 ->
    (match w with
     | I i -> cmp_different_blocks c
     | Uns n -> cmp_different_blocks c
     | Sgn n -> cmp_different_blocks c
     | Ptr p2 -> pcmp c p1 p2
     | Ifptr p2 -> club (pcmp c p1 p2) (cmp_different_blocks c)
     | _ -> Btop)
  | Ifptr p1 ->
    (match w with
     | I i ->
       club (cmp_intv c (uintv v) (Int.unsigned i)) (cmp_different_blocks c)
     | Ptr p2 -> club (pcmp c p1 p2) (cmp_different_blocks c)
     | _ -> Btop)
  | _ ->
    (match w with
     | I i ->
       club (cmp_intv c (uintv v) (Int.unsigned i)) (cmp_different_blocks c)
     | _ -> Btop)

(** val cmp_bool : comparison -> aval -> aval -> abool **)

let cmp_bool c v w =
  match v with
  | I i ->
    (match w with
     | I i0 -> Just (Int.cmp c i i0)
     | _ -> cmp_intv (swap_comparison c) (sintv w) (Int.signed i))
  | _ ->
    (match w with
     | I i -> cmp_intv c (sintv v) (Int.signed i)
     | _ -> Btop)

(** val cmpf_bool : comparison -> aval -> aval -> abool **)

let cmpf_bool c v w =
  match v with
  | F f1 ->
    (match w with
     | F f2 -> Just (Float.cmp c f1 f2)
     | _ -> Btop)
  | _ -> Btop

(** val cmpfs_bool : comparison -> aval -> aval -> abool **)

let cmpfs_bool c v w =
  match v with
  | FS f1 ->
    (match w with
     | FS f2 -> Just (Float32.cmp c f1 f2)
     | _ -> Btop)
  | _ -> Btop

(** val maskzero : aval -> Int.int -> abool **)

let maskzero x mask =
  match x with
  | I i -> Just (Int.eq (Int.coq_and i mask) Int.zero)
  | Uns n ->
    if Int.eq (Int.zero_ext n mask) Int.zero then Maybe true else Btop
  | _ -> Btop

(** val of_optbool : abool -> aval **)

let of_optbool = function
| Just b -> I (if b then Int.one else Int.zero)
| _ -> Uns (Zpos Coq_xH)

(** val resolve_branch : abool -> bool option **)

let resolve_branch = function
| Just b -> Some b
| Maybe b -> Some b
| _ -> None

(** val vnormalize : memory_chunk -> aval -> aval **)

let vnormalize chunk v =
  match chunk with
  | Mint8signed ->
    (match v with
     | Vbot -> Vbot
     | I i -> I (Int.sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) i)
     | Uns n ->
       if zlt n (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
       then Uns n
       else Sgn (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
     | Sgn n -> Sgn (Z.min n (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
     | _ -> Sgn (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | Mint8unsigned ->
    (match v with
     | Vbot -> Vbot
     | I i -> I (Int.zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) i)
     | Uns n -> Uns (Z.min n (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
     | _ -> Uns (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | Mint16signed ->
    (match v with
     | Vbot -> Vbot
     | I i ->
       I (Int.sign_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) i)
     | Uns n ->
       if zlt n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
       then Uns n
       else Sgn (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
     | Sgn n ->
       Sgn (Z.min n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
     | _ -> Sgn (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | Mint16unsigned ->
    (match v with
     | Vbot -> Vbot
     | I i ->
       I (Int.zero_ext (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) i)
     | Uns n ->
       Uns (Z.min n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
     | _ -> Uns (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  | Mint32 ->
    (match v with
     | Vbot -> Vbot
     | I n -> v
     | Ptr p -> v
     | Ifptr p -> v
     | _ -> Ifptr Pbot)
  | Mint64 ->
    (match v with
     | Vbot -> Vbot
     | L n -> v
     | _ -> Ifptr Pbot)
  | Mfloat32 ->
    (match v with
     | Vbot -> Vbot
     | FS f -> v
     | _ -> Ifptr Pbot)
  | Mfloat64 ->
    (match v with
     | Vbot -> Vbot
     | F f -> v
     | _ -> Ifptr Pbot)
  | Many32 ->
    (match v with
     | Vbot -> Vbot
     | Uns n -> Ifptr Pbot
     | Sgn n -> Ifptr Pbot
     | L n -> Ifptr Pbot
     | F f -> Ifptr Pbot
     | _ -> v)
  | Many64 ->
    (match v with
     | Vbot -> Vbot
     | _ -> v)

type acontent =
| ACany
| ACval of memory_chunk * aval

(** val eq_acontent : acontent -> acontent -> bool **)

let eq_acontent c1 c2 =
  match c1 with
  | ACany ->
    (match c2 with
     | ACany -> true
     | ACval (chunk, av) -> false)
  | ACval (x, x0) ->
    (match c2 with
     | ACany -> false
     | ACval (chunk0, av0) ->
       if chunk_eq x chunk0 then eq_aval x0 av0 else false)

type ablock = { ab_contents : acontent ZMap.t; ab_summary : aptr }

(** val ab_contents : ablock -> acontent ZMap.t **)

let ab_contents x = x.ab_contents

(** val ab_summary : ablock -> aptr **)

let ab_summary x = x.ab_summary

(** val ablock_init : aptr -> ablock **)

let ablock_init p =
  { ab_contents = (ZMap.init ACany); ab_summary = p }

(** val chunk_compat : memory_chunk -> memory_chunk -> bool **)

let chunk_compat chunk chunk' =
  match chunk with
  | Mint8signed ->
    (match chunk' with
     | Mint8signed -> true
     | Mint8unsigned -> true
     | _ -> false)
  | Mint8unsigned ->
    (match chunk' with
     | Mint8signed -> true
     | Mint8unsigned -> true
     | _ -> false)
  | Mint32 ->
    (match chunk' with
     | Mint32 -> true
     | _ -> false)
  | Mint64 ->
    (match chunk' with
     | Mint64 -> true
     | _ -> false)
  | Mfloat32 ->
    (match chunk' with
     | Mfloat32 -> true
     | _ -> false)
  | Mfloat64 ->
    (match chunk' with
     | Mfloat64 -> true
     | _ -> false)
  | Many32 ->
    (match chunk' with
     | Many32 -> true
     | _ -> false)
  | Many64 ->
    (match chunk' with
     | Many64 -> true
     | _ -> false)
  | _ ->
    (match chunk' with
     | Mint16signed -> true
     | Mint16unsigned -> true
     | _ -> false)

(** val ablock_load : memory_chunk -> ablock -> coq_Z -> aval **)

let ablock_load chunk ab i =
  match ZMap.get i ab.ab_contents with
  | ACany -> vnormalize chunk (Ifptr ab.ab_summary)
  | ACval (chunk', av) ->
    if chunk_compat chunk chunk'
    then vnormalize chunk av
    else vnormalize chunk (Ifptr ab.ab_summary)

(** val ablock_load_anywhere : memory_chunk -> ablock -> aval **)

let ablock_load_anywhere chunk ab =
  vnormalize chunk (Ifptr ab.ab_summary)

(** val inval_after :
    coq_Z -> coq_Z -> acontent ZMap.t -> acontent ZMap.t **)

let rec inval_after lo hi c =
  if zle lo hi
  then inval_after lo (Z.sub hi (Zpos Coq_xH)) (ZMap.set hi ACany c)
  else c

(** val inval_if : coq_Z -> coq_Z -> acontent ZMap.t -> acontent ZMap.t **)

let inval_if hi lo c =
  match ZMap.get lo c with
  | ACany -> c
  | ACval (chunk, av) ->
    if zle (Z.add lo (size_chunk chunk)) hi then c else ZMap.set lo ACany c

(** val inval_before :
    coq_Z -> coq_Z -> acontent ZMap.t -> acontent ZMap.t **)

let rec inval_before hi lo c =
  if zlt lo hi
  then inval_before hi (Z.add lo (Zpos Coq_xH)) (inval_if hi lo c)
  else c

(** val ablock_store : memory_chunk -> ablock -> coq_Z -> aval -> ablock **)

let ablock_store chunk ab i av =
  { ab_contents =
    (ZMap.set i (ACval (chunk, av))
      (inval_before i (Z.sub i (Zpos (Coq_xI (Coq_xI Coq_xH))))
        (inval_after (Z.add i (Zpos Coq_xH))
          (Z.sub (Z.add i (size_chunk chunk)) (Zpos Coq_xH)) ab.ab_contents)));
    ab_summary = (vplub av ab.ab_summary) }

(** val ablock_store_anywhere : memory_chunk -> ablock -> aval -> ablock **)

let ablock_store_anywhere chunk ab av =
  ablock_init (vplub av ab.ab_summary)

(** val ablock_loadbytes : ablock -> aptr **)

let ablock_loadbytes ab =
  ab.ab_summary

(** val ablock_storebytes : ablock -> aptr -> coq_Z -> coq_Z -> ablock **)

let ablock_storebytes ab p ofs sz =
  { ab_contents =
    (inval_before ofs (Z.sub ofs (Zpos (Coq_xI (Coq_xI Coq_xH))))
      (inval_after ofs (Z.sub (Z.add ofs sz) (Zpos Coq_xH)) ab.ab_contents));
    ab_summary = (plub p ab.ab_summary) }

(** val ablock_storebytes_anywhere : ablock -> aptr -> ablock **)

let ablock_storebytes_anywhere ab p =
  ablock_init (plub p ab.ab_summary)

(** val bbeq : ablock -> ablock -> bool **)

let bbeq ab1 ab2 =
  (&&) ((fun x -> x) (eq_aptr ab1.ab_summary ab2.ab_summary))
    (PTree.beq (fun c1 c2 -> (fun x -> x) (eq_acontent c1 c2))
      (snd ab1.ab_contents) (snd ab2.ab_contents))

(** val combine_acontents_opt :
    acontent option -> acontent option -> acontent option **)

let combine_acontents_opt c1 c2 =
  match c1 with
  | Some a ->
    (match a with
     | ACany -> None
     | ACval (chunk1, v1) ->
       (match c2 with
        | Some a0 ->
          (match a0 with
           | ACany -> None
           | ACval (chunk2, v2) ->
             if chunk_eq chunk1 chunk2
             then Some (ACval (chunk1, (vlub v1 v2)))
             else None)
        | None -> None))
  | None -> None

(** val combine_contentmaps :
    acontent ZMap.t -> acontent ZMap.t -> acontent ZMap.t **)

let combine_contentmaps m1 m2 =
  (ACany, (PTree.combine combine_acontents_opt (snd m1) (snd m2)))

(** val blub : ablock -> ablock -> ablock **)

let blub ab1 ab2 =
  { ab_contents = (combine_contentmaps ab1.ab_contents ab2.ab_contents);
    ab_summary = (plub ab1.ab_summary ab2.ab_summary) }

type romem = ablock PTree.t

type amem = { am_stack : ablock; am_glob : ablock PTree.t;
              am_nonstack : aptr; am_top : aptr }

(** val am_stack : amem -> ablock **)

let am_stack x = x.am_stack

(** val am_glob : amem -> ablock PTree.t **)

let am_glob x = x.am_glob

(** val am_nonstack : amem -> aptr **)

let am_nonstack x = x.am_nonstack

(** val am_top : amem -> aptr **)

let am_top x = x.am_top

(** val minit : aptr -> amem **)

let minit p =
  { am_stack = (ablock_init p); am_glob = PTree.empty; am_nonstack = p;
    am_top = p }

(** val mtop : amem **)

let mtop =
  minit Ptop

(** val load : memory_chunk -> romem -> amem -> aptr -> aval **)

let load chunk rm m = function
| Pbot -> if va_strict () then Vbot else coq_Vtop
| Gl (id, ofs) ->
  (match PTree.get id rm with
   | Some ab -> ablock_load chunk ab (Int.unsigned ofs)
   | None ->
     (match PTree.get id m.am_glob with
      | Some ab -> ablock_load chunk ab (Int.unsigned ofs)
      | None -> vnormalize chunk (Ifptr m.am_nonstack)))
| Glo id ->
  (match PTree.get id rm with
   | Some ab -> ablock_load_anywhere chunk ab
   | None ->
     (match PTree.get id m.am_glob with
      | Some ab -> ablock_load_anywhere chunk ab
      | None -> vnormalize chunk (Ifptr m.am_nonstack)))
| Stk ofs -> ablock_load chunk m.am_stack (Int.unsigned ofs)
| Stack -> ablock_load_anywhere chunk m.am_stack
| Ptop -> vnormalize chunk (Ifptr m.am_top)
| _ -> vnormalize chunk (Ifptr m.am_nonstack)

(** val loadv : memory_chunk -> romem -> amem -> aval -> aval **)

let loadv chunk rm m addr =
  load chunk rm m (aptr_of_aval addr)

(** val store : memory_chunk -> amem -> aptr -> aval -> amem **)

let store chunk m p av =
  { am_stack =
    (match p with
     | Stk ofs -> ablock_store chunk m.am_stack (Int.unsigned ofs) av
     | Stack -> ablock_store_anywhere chunk m.am_stack av
     | Ptop -> ablock_store_anywhere chunk m.am_stack av
     | _ -> m.am_stack); am_glob =
    (match p with
     | Gl (id, ofs) ->
       let ab =
         match PTree.get id m.am_glob with
         | Some ab -> ab
         | None -> ablock_init m.am_nonstack
       in
       PTree.set id (ablock_store chunk ab (Int.unsigned ofs) av) m.am_glob
     | Glo id ->
       let ab =
         match PTree.get id m.am_glob with
         | Some ab -> ab
         | None -> ablock_init m.am_nonstack
       in
       PTree.set id (ablock_store_anywhere chunk ab av) m.am_glob
     | Glob -> PTree.empty
     | Nonstack -> PTree.empty
     | Ptop -> PTree.empty
     | _ -> m.am_glob); am_nonstack =
    (match p with
     | Pbot -> m.am_nonstack
     | Stk ofs -> m.am_nonstack
     | Stack -> m.am_nonstack
     | _ -> vplub av m.am_nonstack); am_top = (vplub av m.am_top) }

(** val storev : memory_chunk -> amem -> aval -> aval -> amem **)

let storev chunk m addr v =
  store chunk m (aptr_of_aval addr) v

(** val loadbytes : amem -> romem -> aptr -> aptr **)

let loadbytes m rm = function
| Pbot -> if va_strict () then Pbot else Ptop
| Gl (id, ofs) ->
  (match PTree.get id rm with
   | Some ab -> ablock_loadbytes ab
   | None ->
     (match PTree.get id m.am_glob with
      | Some ab -> ablock_loadbytes ab
      | None -> m.am_nonstack))
| Glo id ->
  (match PTree.get id rm with
   | Some ab -> ablock_loadbytes ab
   | None ->
     (match PTree.get id m.am_glob with
      | Some ab -> ablock_loadbytes ab
      | None -> m.am_nonstack))
| Glob -> m.am_nonstack
| Nonstack -> m.am_nonstack
| Ptop -> m.am_top
| _ -> ablock_loadbytes m.am_stack

(** val storebytes : amem -> aptr -> coq_Z -> aptr -> amem **)

let storebytes m dst sz p =
  { am_stack =
    (match dst with
     | Stk ofs -> ablock_storebytes m.am_stack p (Int.unsigned ofs) sz
     | Stack -> ablock_storebytes_anywhere m.am_stack p
     | Ptop -> ablock_storebytes_anywhere m.am_stack p
     | _ -> m.am_stack); am_glob =
    (match dst with
     | Gl (id, ofs) ->
       let ab =
         match PTree.get id m.am_glob with
         | Some ab -> ab
         | None -> ablock_init m.am_nonstack
       in
       PTree.set id (ablock_storebytes ab p (Int.unsigned ofs) sz) m.am_glob
     | Glo id ->
       let ab =
         match PTree.get id m.am_glob with
         | Some ab -> ab
         | None -> ablock_init m.am_nonstack
       in
       PTree.set id (ablock_storebytes_anywhere ab p) m.am_glob
     | Glob -> PTree.empty
     | Nonstack -> PTree.empty
     | Ptop -> PTree.empty
     | _ -> m.am_glob); am_nonstack =
    (match dst with
     | Pbot -> m.am_nonstack
     | Stk ofs -> m.am_nonstack
     | Stack -> m.am_nonstack
     | _ -> plub p m.am_nonstack); am_top = (plub p m.am_top) }

(** val mbeq : amem -> amem -> bool **)

let mbeq m1 m2 =
  (&&)
    ((&&)
      ((&&) ((fun x -> x) (eq_aptr m1.am_top m2.am_top))
        ((fun x -> x) (eq_aptr m1.am_nonstack m2.am_nonstack)))
      (bbeq m1.am_stack m2.am_stack)) (PTree.beq bbeq m1.am_glob m2.am_glob)

(** val combine_ablock : ablock option -> ablock option -> ablock option **)

let combine_ablock ob1 ob2 =
  match ob1 with
  | Some b1 ->
    (match ob2 with
     | Some b2 -> Some (blub b1 b2)
     | None -> None)
  | None -> None

(** val mlub : amem -> amem -> amem **)

let mlub m1 m2 =
  { am_stack = (blub m1.am_stack m2.am_stack); am_glob =
    (PTree.combine combine_ablock m1.am_glob m2.am_glob); am_nonstack =
    (plub m1.am_nonstack m2.am_nonstack); am_top =
    (plub m1.am_top m2.am_top) }

module AVal = 
 struct 
  type t = aval
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    (fun x -> x) (eq_aval x y)
  
  (** val bot : t **)
  
  let bot =
    Vbot
  
  (** val top : t **)
  
  let top =
    coq_Vtop
  
  (** val lub : aval -> aval -> aval **)
  
  let lub =
    vlub
 end

module AE = LPMap(AVal)

type aenv = AE.t

(** val einit_regs : reg list -> aenv **)

let rec einit_regs = function
| [] -> AE.top
| r1 :: rs -> AE.set r1 (Ifptr Nonstack) (einit_regs rs)

(** val eforget : reg list -> aenv -> aenv **)

let rec eforget rl ae =
  match rl with
  | [] -> ae
  | r1 :: rs -> eforget rs (AE.set r1 coq_Vtop ae)

module VA = 
 struct 
  type t' =
  | Bot
  | State of aenv * amem
  
  (** val t'_rect : 'a1 -> (aenv -> amem -> 'a1) -> t' -> 'a1 **)
  
  let t'_rect f f0 = function
  | Bot -> f
  | State (x, x0) -> f0 x x0
  
  (** val t'_rec : 'a1 -> (aenv -> amem -> 'a1) -> t' -> 'a1 **)
  
  let t'_rec f f0 = function
  | Bot -> f
  | State (x, x0) -> f0 x x0
  
  type t = t'
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    match x with
    | Bot ->
      (match y with
       | Bot -> true
       | State (ae, am) -> false)
    | State (ae1, am1) ->
      (match y with
       | Bot -> false
       | State (ae2, am2) -> (&&) (AE.beq ae1 ae2) (mbeq am1 am2))
  
  (** val bot : t **)
  
  let bot =
    Bot
  
  (** val lub : t -> t -> t **)
  
  let lub x y =
    match x with
    | Bot -> y
    | State (ae1, am1) ->
      (match y with
       | Bot -> x
       | State (ae2, am2) -> State ((AE.lub ae1 ae2), (mlub am1 am2)))
 end

