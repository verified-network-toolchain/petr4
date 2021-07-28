
(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val reflect_dec : bool -> reflect -> bool **)

let reflect_dec _ = function
| ReflectT -> true
| ReflectF -> false

(** val eqb_spec : bool -> bool -> reflect **)

let eqb_spec b b' =
  if b
  then if b' then ReflectT else ReflectF
  else if b' then ReflectF else ReflectT
