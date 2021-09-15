open Core_kernel

type t = bool list

let shift_bitstring_left (v : t) (o : t) : t =
  failwith "shift_bitstring_left unimplemented"

let shift_bitstring_right (v : t) (o : t)
    (arith : bool) (mx : t) : t =
  failwith "shift_bitstring_right unimplemented"

let power_of_two (w : t) : t =
  failwith "power_of_two unimplemented"

let width (n: t) : int =
  List.length n

let bitstring_slice (n : t) (m : int) (l : int) : t =
  failwith "bitstring_slice unimplemented"

let of_twos_complement (n : t) (w : t) : t =
  failwith "of_twos_complement unimplemented"

let to_twos_complement (n : t) (w : t) : t =
  failwith "to_twos_complement unimplemented"

let bit_of_rawint (n : t) (w : int) : Prog.coq_ValueBase =
  ValBaseBit (List.take n w)

let int_of_rawint (n : t) (w : int) : Prog.coq_ValueBase =
  ValBaseInt (List.take n w)

let bitwise_neg_of_bigint (n : t) (w : t) : t =
  failwith "bitwise_neg_of_bigint unimplemented"
