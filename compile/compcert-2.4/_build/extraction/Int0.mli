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

module Z_as_Int : 
 sig 
  type t = coq_Z
  
  val _0 : coq_Z
  
  val _1 : coq_Z
  
  val _2 : coq_Z
  
  val _3 : coq_Z
  
  val plus : coq_Z -> coq_Z -> coq_Z
  
  val opp : coq_Z -> coq_Z
  
  val minus : coq_Z -> coq_Z -> coq_Z
  
  val mult : coq_Z -> coq_Z -> coq_Z
  
  val max : coq_Z -> coq_Z -> coq_Z
  
  val gt_le_dec : coq_Z -> coq_Z -> bool
  
  val ge_lt_dec : coq_Z -> coq_Z -> bool
  
  val eq_dec : coq_Z -> coq_Z -> bool
  
  val i2z : t -> coq_Z
 end

