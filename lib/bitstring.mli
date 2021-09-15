type t = bool list

(** [shift_bitstring_left v o] is [v] shifted left by [o]. *)
val shift_bitstring_left : t -> t -> t

(** [shift_bitstring_right v o] is [v] shifted right by [o]. *)
val shift_bitstring_right : t -> t -> bool -> t -> t

(** [power_of_two n] is [2] raised to the power of [n]. *)
val power_of_two : t -> t

(** [bitstring_slice n m l] is the bitstring slice [n[m:l]]. *)
val bitstring_slice : t -> int -> int -> t

(** [of_twos_complement n w] is [n] coerced with modular arithmetic to be in the
    range [0 .. 2^w-1]. *)
val of_twos_complement : t -> t -> t

(** [to_twos_complement n w] is [n] coerced with modular arithmetic to be in the
    range [-2^(w-1) .. 2^(w-1)-1]. *)
val to_twos_complement : t -> t -> t

val bit_of_rawint : t -> int -> Prog.coq_ValueBase

val int_of_rawint : t -> int -> Prog.coq_ValueBase

(* [bitwsie_neg_of_bigint n w] computes the bitwise negation of n as a
   w-bit two's complement number. *)
val bitwise_neg_of_bigint : t -> t -> t
