
val list_rec :
  'a3 -> ('a1 -> 'a1 list -> 'a2 -> 'a3 -> 'a3) -> ('a1 -> 'a2) -> 'a1 list
  -> 'a3

val option_rec :
  'a3 -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 option -> 'a3
