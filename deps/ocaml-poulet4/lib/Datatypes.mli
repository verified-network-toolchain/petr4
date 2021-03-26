
type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt
