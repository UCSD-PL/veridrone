open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type MAP = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val empty : 'a1 t
  
  val get : elt -> 'a1 t -> 'a1 option
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
 end

module type UNIONFIND = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type t 
  
  val repr : t -> elt -> elt
  
  val empty : t
  
  val find : t -> elt -> elt * t
  
  val union : t -> elt -> elt -> t
  
  val merge : t -> elt -> elt -> t
  
  val pathlen : t -> elt -> nat
 end

module UF = 
 functor (M:MAP) ->
 struct 
  type elt = M.elt
  
  (** val elt_eq : M.elt -> M.elt -> bool **)
  
  let elt_eq =
    M.elt_eq
  
  type unionfind =
    elt M.t
    (* singleton inductive, whose constructor was mk *)
  
  (** val m : unionfind -> elt M.t **)
  
  let m u =
    u
  
  type t = unionfind
  
  (** val getlink : elt M.t -> elt -> elt option **)
  
  let getlink m0 a =
    let o = M.get a m0 in
    (match o with
     | Some e -> Some e
     | None -> None)
  
  (** val coq_F_repr : t -> elt -> (elt -> __ -> elt) -> elt **)
  
  let coq_F_repr uf a rec0 =
    match getlink (m uf) a with
    | Some s -> rec0 s __
    | None -> a
  
  (** val repr : t -> elt -> elt **)
  
  let rec repr uf a =
    coq_F_repr uf a (fun y _ -> repr uf y)
  
  (** val empty : t **)
  
  let empty =
    M.empty
  
  (** val identify : t -> elt -> elt -> unionfind **)
  
  let identify uf a b =
    M.set a b (m uf)
  
  (** val union : t -> elt -> elt -> t **)
  
  let union uf a b =
    let a' = repr uf a in
    let b' = repr uf b in if M.elt_eq a' b' then uf else identify uf a' b'
  
  (** val merge : t -> elt -> elt -> t **)
  
  let merge uf a b =
    let a' = repr uf a in
    let b' = repr uf b in if M.elt_eq a' b' then uf else identify uf a' b
  
  (** val coq_F_pathlen : t -> elt -> (elt -> __ -> nat) -> nat **)
  
  let coq_F_pathlen uf a rec0 =
    match getlink (m uf) a with
    | Some s -> S (rec0 s __)
    | None -> O
  
  (** val pathlen : t -> elt -> nat **)
  
  let rec pathlen uf a =
    coq_F_pathlen uf a (fun y _ -> pathlen uf y)
  
  (** val compress : t -> elt -> elt -> unionfind **)
  
  let compress uf a b =
    M.set a b (m uf)
  
  (** val find_x : t -> elt -> (elt * t) **)
  
  let rec find_x uf x =
    let find_x0 = fun a -> find_x uf a in
    let filtered_var = M.get x (m uf) in
    (match filtered_var with
     | Some a' ->
       let filtered_var0 = find_x0 a' in
       let (b, uf') = filtered_var0 in (b, (compress uf' x b))
     | None -> (x, uf))
  
  (** val find : t -> elt -> elt * t **)
  
  let find uf a =
    find_x uf a
 end

