open Prog.Value

type t = Bigint.t

let rec shift_bitstring_left (v : Bigint.t) (o : Bigint.t) : Bigint.t =
  if Bigint.(o > zero)
  then shift_bitstring_left Bigint.(v * (one + one)) Bigint.(o - one)
  else v

let rec shift_bitstring_right (v : Bigint.t) (o : Bigint.t) : Bigint.t =
  if Bigint.(v = -one)
  then v
  else if Bigint.(o > zero)
  then shift_bitstring_right Bigint.(v / (one + one)) Bigint.(o - one)
  else v  

let power_of_two (w : Bigint.t) : Bigint.t =
  shift_bitstring_left Bigint.one w  

let rec bitstring_slice (n : Bigint.t) (m : Bigint.t) (l : Bigint.t) : Bigint.t =
  Bigint.(
    if l > zero
    then bitstring_slice (n/(one + one)) (m-one) (l-one)
    else n % (power_of_two (m + one)))

let rec of_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
  let w' = power_of_two w in
  if Bigint.(n >= w')
  then Bigint.(n % w')
  else if Bigint.(n < zero)
  then of_twos_complement Bigint.(n + w') w
  else n

let rec to_twos_complement (n : Bigint.t) (w : Bigint.t) : Bigint.t =
  let two = Bigint.(one + one) in
  let w' = power_of_two w in
  if Bigint.(n >= (w' / two))
  then to_twos_complement Bigint.(n-w') w
  else if Bigint.(n < -(w'/two))
  then to_twos_complement Bigint.(n+w') w
  else n

let bit_of_rawint (n : Bigint.t) (w : Bigint.t) : value =
  VBit{w;v=of_twos_complement n w}  

let int_of_rawint (n : Bigint.t) (w : Bigint.t) : value =
  VInt{w;v=to_twos_complement n w}