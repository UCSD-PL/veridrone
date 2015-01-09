type __ = Obj.t

type 'x arrows_left = __

type 'x arrows_right = __

type tuple = __

(** val uncurry : __ list -> 'a1 arrows_left -> tuple -> 'a1 **)

let rec uncurry args f x =
  match args with
  | [] -> Obj.magic f
  | _ :: q -> let (d, t) = Obj.magic x in Obj.magic uncurry q f t d

