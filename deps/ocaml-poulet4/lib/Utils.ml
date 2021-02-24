
(** val list_rec :
    'a3 -> ('a1 -> 'a1 list -> 'a2 -> 'a3 -> 'a3) -> ('a1 -> 'a2) -> 'a1 list
    -> 'a3 **)

let rec list_rec hAListNil hAListCons rec0 = function
| [] -> hAListNil
| f :: l' -> hAListCons f l' (rec0 f) (list_rec hAListNil hAListCons rec0 l')

(** val option_rec :
    'a3 -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 option -> 'a3 **)

let option_rec pAOptionNone pAOptionSome rec0 = function
| Some a -> pAOptionSome a (rec0 a)
| None -> pAOptionNone
