open Core_kernel
open Prog.Value

type t = Bigint.t

let rec shift_bitstring_left (v : Bigint.t) (o : Bigint.t) : Bigint.t =
  if Bigint.(o > zero)
  then shift_bitstring_left Bigint.(v * (one + one)) Bigint.(o - one)
  else v

let rec shift_bitstring_right (v : Bigint.t) (o : Bigint.t)
    (arith : bool) (mx : Bigint.t) : Bigint.t =
  if not arith then begin
    if Bigint.(o > zero)
    then shift_bitstring_right Bigint.(v / (one + one)) Bigint.(o - one) arith mx
    else v
  end
  else begin
    if Bigint.(o > zero)
    then shift_bitstring_right Bigint.((v / (one + one)) + mx) Bigint.(o - one) arith mx
    else v
  end

let power_of_two (w : Bigint.t) : Bigint.t =
  shift_bitstring_left Bigint.one w

let rec width (n: Bigint.t) : int =
  if Bigint.(n < zero)
  then failwith "cannot get width of negative number"
  else
    if Bigint.(n = zero || n = one)
    then 1
    else 1 + width (Bigint.(n asr 1))

let bitstring_slice (n : Bigint.t) (m : Bigint.t) (l : Bigint.t) : Bigint.t =
  let open Bigint in
  let slice_width = m + one - l in
  if l < zero then raise (Invalid_argument "bitslice x[y:z] must have y > z > 0");
  let shifted = n asr to_int_exn l in
  let mask = power_of_two slice_width - one in
  bit_and shifted mask

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

let rec bitwise_neg_of_bigint (n : Bigint.t) (w : Bigint.t) : Bigint.t =
  if Bigint.(w > zero) then
    let w' = power_of_two Bigint.(w-one) in
    let g = bitstring_slice n Bigint.(w - one) Bigint.(w - one) in
    if Bigint.(g = zero)
    then bitwise_neg_of_bigint Bigint.(n + w') Bigint.(w-one)
    else bitwise_neg_of_bigint Bigint.(n - w') Bigint.(w-one)
  else n
