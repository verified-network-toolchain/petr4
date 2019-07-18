open Value
open Core

type packet = bool list * int
type value = packet pre_value

let rec fixed_width_extract (p : packet) (v : value) : packet * value =
  match v with
  | VBit(len,_) -> bits_of_packet p len
  | _ -> failwith "header field population unimplemented"

and var_width_extract (packet : packet) (hdr : value)
    (size : value) : packet * value =
  failwith "variable width extraction unimplemented"

and lookahead (p : packet) (v: value) : packet =
  failwith "lookahead unimplemented"

and packet_length (p : packet) : value = VBit(32,snd p |> Bigint.of_int)

and advance (p : packet) (v : value) : packet =
  failwith "advancing unimplemented"

and emit (p : packet) (v : value) : packet =
  match v with
  | VStruct(n,fs)    -> emit_struct p fs
  | VHeader(_,fs,b)  -> emit_header p fs b
  | VUnion(_,v,bs)   -> emit_union p v bs
  | VStack(_,vs,_,_) -> emit_stack p vs
  | _ -> failwith "cannot emit this type"

and emit_struct (p : packet) (fs : (string * value) list) : packet  =
  failwith "struct emission unimlemented"

and bits_of_packet (p : packet) (len : int) : packet * value =
  let rec h p l v =
    if l = 0 then (p,v)
    else
      let (a,b) = match v with
        | VBit(a,b) -> (a,b)
        | _ -> failwith "not a bitstring" in
      let two = Bigint.(one + one) in
      match p with
      | [] -> failwith "packet too short"
      | x :: y ->
        h y (l-1) (VBit(a+1,Bigint.((if x then one else zero) + (two * b)))) in
  let (p',v) = h (fst p) len (VBit(0,Bigint.zero)) in
  ((p',snd p), v)

and emit_header (p : packet) (fs : (string * value) list) (b : bool) : packet =
  if not b then p else
    let prefix = fs
                 |> List.map ~f:snd
                 |> List.map ~f:packet_of_value
                 |> List.fold_right ~init:[] ~f:(@) in
    ((prefix @ fst p), snd p)

and emit_union (p : packet) (v : value) (bs : (string * bool) list) : packet =
  failwith "union emission unimplemented"

and emit_stack (p : packet) (vs : value list) : packet =
  failwith "stack emission unimplemented"

and packet_of_value (v : value) : bool list =
  match v with
  | VBit(w,n) -> packet_of_bitstring w n
  | _ -> failwith "value of packet conversion unimplemented"

and packet_of_bitstring (w : int) (n : Bigint.t) : bool list =
  let rec h w n l =
    if w = 0 then l
    else h (w-1) Bigint.(n/(one+one)) (Bigint.(n%(one+one)=one) :: l) in
  h w n []

and packet_of_list (p : bool list) : packet = (p, List.length p)
