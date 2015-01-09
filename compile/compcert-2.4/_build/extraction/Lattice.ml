open BinNums
open Bool
open FSetInterface
open Maps

module type SEMILATTICE = 
 sig 
  type t 
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
 end

module type SEMILATTICE_WITH_TOP = 
 sig 
  type t 
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
  
  val top : t
 end

module LPMap1 = 
 functor (L:SEMILATTICE) ->
 struct 
  type t = L.t PTree.t
  
  (** val get : positive -> t -> L.t **)
  
  let get p x =
    match PTree.get p x with
    | Some x0 -> x0
    | None -> L.bot
  
  (** val set : positive -> L.t -> t -> t **)
  
  let set p v x =
    if L.beq v L.bot then PTree.remove p x else PTree.set p v x
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    PTree.beq L.beq x y
  
  (** val bot : t **)
  
  let bot =
    PTree.empty
  
  (** val opt_beq : L.t option -> L.t option -> bool **)
  
  let opt_beq ox oy =
    match ox with
    | Some x ->
      (match oy with
       | Some y -> L.beq x y
       | None -> false)
    | None ->
      (match oy with
       | Some t0 -> false
       | None -> true)
  
  type changed =
  | Unchanged
  | Changed of L.t PTree.t
  
  (** val combine_l :
      (L.t option -> L.t option -> L.t option) -> L.t PTree.t -> changed **)
  
  let rec combine_l f = function
  | PTree.Leaf -> Unchanged
  | PTree.Node (l, o, r) ->
    let o' = f o None in
    (match combine_l f l with
     | Unchanged ->
       (match combine_l f r with
        | Unchanged ->
          if opt_beq o' o
          then Unchanged
          else Changed (PTree.coq_Node' l o' r)
        | Changed r' -> Changed (PTree.coq_Node' l o' r'))
     | Changed l' ->
       (match combine_l f r with
        | Unchanged -> Changed (PTree.coq_Node' l' o' r)
        | Changed r' -> Changed (PTree.coq_Node' l' o' r')))
  
  (** val combine_r :
      (L.t option -> L.t option -> L.t option) -> L.t PTree.t -> changed **)
  
  let rec combine_r f = function
  | PTree.Leaf -> Unchanged
  | PTree.Node (l, o, r) ->
    let o' = f None o in
    (match combine_r f l with
     | Unchanged ->
       (match combine_r f r with
        | Unchanged ->
          if opt_beq o' o
          then Unchanged
          else Changed (PTree.coq_Node' l o' r)
        | Changed r' -> Changed (PTree.coq_Node' l o' r'))
     | Changed l' ->
       (match combine_r f r with
        | Unchanged -> Changed (PTree.coq_Node' l' o' r)
        | Changed r' -> Changed (PTree.coq_Node' l' o' r')))
  
  type changed2 =
  | Same
  | Same1
  | Same2
  | CC of L.t PTree.t
  
  (** val xcombine :
      (L.t option -> L.t option -> L.t option) -> L.t PTree.t -> L.t PTree.t
      -> changed2 **)
  
  let rec xcombine f m1 m2 =
    match m1 with
    | PTree.Leaf ->
      (match m2 with
       | PTree.Leaf -> Same
       | PTree.Node (t0, o, t1) ->
         (match combine_r f m2 with
          | Unchanged -> Same2
          | Changed m -> CC m))
    | PTree.Node (l1, o1, r1) ->
      (match m2 with
       | PTree.Leaf ->
         (match combine_l f m1 with
          | Unchanged -> Same1
          | Changed m -> CC m)
       | PTree.Node (l2, o2, r2) ->
         let o = f o1 o2 in
         (match xcombine f l1 l2 with
          | Same ->
            (match xcombine f r1 r2 with
             | Same ->
               if opt_beq o o1
               then if opt_beq o o2 then Same else Same1
               else if opt_beq o o2
                    then Same2
                    else CC (PTree.coq_Node' l1 o r1)
             | Same1 ->
               if opt_beq o o1 then Same1 else CC (PTree.coq_Node' l1 o r1)
             | Same2 ->
               if opt_beq o o2 then Same2 else CC (PTree.coq_Node' l2 o r2)
             | CC r -> CC (PTree.coq_Node' l1 o r))
          | Same1 ->
            (match xcombine f r1 r2 with
             | Same2 -> CC (PTree.coq_Node' l1 o r2)
             | CC r -> CC (PTree.coq_Node' l1 o r)
             | _ ->
               if opt_beq o o1 then Same1 else CC (PTree.coq_Node' l1 o r1))
          | Same2 ->
            (match xcombine f r1 r2 with
             | Same1 -> CC (PTree.coq_Node' l2 o r1)
             | CC r -> CC (PTree.coq_Node' l2 o r)
             | _ ->
               if opt_beq o o2 then Same2 else CC (PTree.coq_Node' l2 o r2))
          | CC l ->
            (match xcombine f r1 r2 with
             | Same2 -> CC (PTree.coq_Node' l o r2)
             | CC r -> CC (PTree.coq_Node' l o r)
             | _ -> CC (PTree.coq_Node' l o r1))))
  
  (** val combine :
      (L.t option -> L.t option -> L.t option) -> L.t PTree.t -> L.t PTree.t
      -> L.t PTree.t **)
  
  let combine f m1 m2 =
    match xcombine f m1 m2 with
    | Same2 -> m2
    | CC m -> m
    | _ -> m1
  
  (** val lub : t -> t -> t **)
  
  let lub x y =
    combine (fun a b ->
      match a with
      | Some u ->
        (match b with
         | Some v -> Some (L.lub u v)
         | None -> a)
      | None -> b) x y
 end

module LPMap = 
 functor (L:SEMILATTICE_WITH_TOP) ->
 struct 
  type t' =
  | Bot
  | Top_except of L.t PTree.t
  
  type t = t'
  
  (** val get : positive -> t -> L.t **)
  
  let get p = function
  | Bot -> L.bot
  | Top_except m ->
    (match PTree.get p m with
     | Some x0 -> x0
     | None -> L.top)
  
  (** val set : positive -> L.t -> t -> t **)
  
  let set p v = function
  | Bot -> Bot
  | Top_except m ->
    if L.beq v L.bot
    then Bot
    else Top_except
           (if L.beq v L.top then PTree.remove p m else PTree.set p v m)
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    match x with
    | Bot ->
      (match y with
       | Bot -> true
       | Top_except t0 -> false)
    | Top_except m ->
      (match y with
       | Bot -> false
       | Top_except n -> PTree.beq L.beq m n)
  
  (** val bot : t' **)
  
  let bot =
    Bot
  
  (** val top : t' **)
  
  let top =
    Top_except PTree.empty
  
  module LM = LPMap1(L)
  
  (** val opt_lub : L.t -> L.t -> L.t option **)
  
  let opt_lub x y =
    let z = L.lub x y in if L.beq z L.top then None else Some z
  
  (** val lub : t -> t -> t **)
  
  let lub x y =
    match x with
    | Bot -> y
    | Top_except m ->
      (match y with
       | Bot -> x
       | Top_except n ->
         Top_except
           (LM.combine (fun a b ->
             match a with
             | Some u ->
               (match b with
                | Some v -> opt_lub u v
                | None -> None)
             | None -> None) m n))
 end

module LFSet = 
 functor (S:WS) ->
 struct 
  type t = S.t
  
  (** val beq : t -> t -> bool **)
  
  let beq =
    S.equal
  
  (** val bot : t **)
  
  let bot =
    S.empty
  
  (** val lub : t -> t -> t **)
  
  let lub =
    S.union
 end

module LBoolean = 
 struct 
  type t = bool
  
  (** val beq : t -> t -> bool **)
  
  let beq =
    eqb
  
  (** val bot : bool **)
  
  let bot =
    false
  
  (** val top : bool **)
  
  let top =
    true
  
  (** val lub : t -> t -> bool **)
  
  let lub x y =
    (||) x y
 end

