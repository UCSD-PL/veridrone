open BinNums

type errcode =
| MSG of char list
| CTX of positive
| POS of positive

type errmsg = errcode list

(** val msg : char list -> errmsg **)

let msg s =
  (MSG s) :: []

type 'a res =
| OK of 'a
| Error of errmsg

(** val assertion_failed : 'a1 res **)

let assertion_failed =
  Error
    (msg
      ('A'::('s'::('s'::('e'::('r'::('t'::('i'::('o'::('n'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))))))

