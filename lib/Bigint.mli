exception Overflow

type sign = Pos | Neg

type t    = Bigint of sign * int list

val t_of_sexp: Sexplib.Sexp.t -> t
val sexp_of_t: t -> Sexplib.Sexp.t
val zero: t
val one: t
val minus_one: t
val of_int: int -> t
val of_int32: Int32.t -> t
val of_int64: Int64.t -> t
val of_nativeint: nativeint -> t
val of_float: float -> t
val of_string: string -> t
val of_substring : string -> pos:int -> len:int -> t
val succ: t -> t
val pred: t -> t
val abs: t -> t
val neg: t -> t
val add: t -> t -> t
val sub: t -> t -> t
val mul: t -> t -> t
val div: t -> t -> t
val rem: t -> t -> t
val div_rem: t -> t -> (t * t)
val cdiv: t -> t -> t
val fdiv: t -> t -> t
val ediv_rem: t -> t -> (t * t)
val ediv: t -> t -> t
val erem: t -> t -> t
val divexact: t -> t -> t
val bit_and: t -> t -> t
val bit_or: t -> t -> t
val bit_xor: t -> t -> t
val bit_not: t -> t
val shift_left : t -> int -> t
val shift_right : t -> int -> t
val numbits : t -> int
val to_int: t -> int option
val to_int_exn: t -> int
val to_int32: t -> int32
val to_int64: t -> int64
val to_nativeint: t -> nativeint
val to_float: t -> float
val to_string: t -> string
val compare : t -> t -> int
val equal: t -> t -> bool
val leq: t -> t -> bool
val geq: t -> t -> bool
val lt: t -> t -> bool
val gt: t -> t -> bool
val sign: t -> int
val min: t -> t -> t
val max: t -> t -> t
val is_even: t -> bool
val is_odd: t -> bool
val gcd: t -> t -> t
val pow: t -> int -> t
val (%): t -> t -> t
val (~-): t -> t
val (~+): t -> t
val (+): t -> t -> t
val (-): t -> t -> t
val ( * ): t -> t -> t
val (/): t -> t -> t
val (/>): t -> t -> t
val (/<): t -> t -> t
val (/|): t -> t -> t
val (mod): t -> t -> t
val (land): t -> t -> t
val (lor): t -> t -> t
val (lxor): t -> t -> t
val (~!): t -> t
val (lsl): t -> int -> t
val (asr): t -> int -> t
val (~$): int -> t
val ( ** ): t -> int -> t
val (=): t -> t -> bool
val (<): t -> t -> bool
val (>): t -> t -> bool
val (<=): t -> t -> bool
val (>=): t -> t -> bool
val (<>): t -> t -> bool
