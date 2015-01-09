open BinInt
open BinNums
open ZArith_dec

module type Int = 
 sig 
  type t 
  
  val i2z : t -> coq_Z
  
  val _0 : t
  
  val _1 : t
  
  val _2 : t
  
  val _3 : t
  
  val plus : t -> t -> t
  
  val opp : t -> t
  
  val minus : t -> t -> t
  
  val mult : t -> t -> t
  
  val max : t -> t -> t
  
  val gt_le_dec : t -> t -> bool
  
  val ge_lt_dec : t -> t -> bool
  
  val eq_dec : t -> t -> bool
 end

module Z_as_Int = 
 struct 
  type t = coq_Z
  
  (** val _0 : coq_Z **)
  
  let _0 =
    Z0
  
  (** val _1 : coq_Z **)
  
  let _1 =
    Zpos Coq_xH
  
  (** val _2 : coq_Z **)
  
  let _2 =
    Zpos (Coq_xO Coq_xH)
  
  (** val _3 : coq_Z **)
  
  let _3 =
    Zpos (Coq_xI Coq_xH)
  
  (** val plus : coq_Z -> coq_Z -> coq_Z **)
  
  let plus =
    Z.add
  
  (** val opp : coq_Z -> coq_Z **)
  
  let opp =
    Z.opp
  
  (** val minus : coq_Z -> coq_Z -> coq_Z **)
  
  let minus =
    Z.sub
  
  (** val mult : coq_Z -> coq_Z -> coq_Z **)
  
  let mult =
    Z.mul
  
  (** val max : coq_Z -> coq_Z -> coq_Z **)
  
  let max =
    Z.max
  
  (** val gt_le_dec : coq_Z -> coq_Z -> bool **)
  
  let gt_le_dec =
    coq_Z_gt_le_dec
  
  (** val ge_lt_dec : coq_Z -> coq_Z -> bool **)
  
  let ge_lt_dec =
    coq_Z_ge_lt_dec
  
  (** val eq_dec : coq_Z -> coq_Z -> bool **)
  
  let eq_dec =
    Z.eq_dec
  
  (** val i2z : t -> coq_Z **)
  
  let i2z n =
    n
 end

