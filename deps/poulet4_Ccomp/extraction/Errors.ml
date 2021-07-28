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
