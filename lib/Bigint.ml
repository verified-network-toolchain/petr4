exception Overflow

type sign = Pos | Neg

type t = Bigint of sign * int list

let zero = Bigint (Pos, [])

let one = Bigint (Pos, [ 1 ])

let two = Bigint (Pos, [ 2 ])

let minus_one = Bigint (Neg, [ 1 ])

let radix = 10

let trimzeros listy =
  let rec helper_trim listy' =
    match listy' with
    | [] -> []
    | [ 0 ] -> []
    | h :: t -> (
        let t' = helper_trim t in
        match h, t' with
        | 0, [] -> []
        | h, _ -> h :: t' )
  in
  helper_trim listy

let charlist_of_string s = List.init (String.length s) (String.get s)

let of_string str =
  let len = String.length str in
  let to_intlist first =
    let substr = String.sub str first (len - first) in
    let digit char = int_of_char char - int_of_char '0' in
    substr |> charlist_of_string |> List.rev |> List.map digit |> trimzeros
  in
  if str.[0] = '-' then Bigint (Neg, to_intlist 1)
  else Bigint (Pos, to_intlist 0)

let of_substring s ~pos ~len = of_string (String.sub s pos len)

let of_int i = of_string (string_of_int i)

let of_int32 i = of_string (Int32.to_string i)

let of_int64 i = of_string (Int64.to_string i)

let of_nativeint i = of_string (Nativeint.to_string i)

let of_float i = of_string (Int64.to_string (Int64.of_float i))

let to_string (Bigint (sign, value)) =
  match value with
  | [] -> "0"
  | value ->
      let reversed = List.rev value in
      let str_sign = if sign = Pos then "" else "-" in
      String.concat "" (str_sign :: List.map string_of_int reversed)

(* cmp list1 list2 = bigger list *)
let rec cmp list1 list2 =
  if List.length list1 > List.length list2 then 1
  else if List.length list1 < List.length list2 then -1
  else
    match list1, list2 with
    | [], [] -> 0
    | list1, list2 ->
        let reverselist1 = List.rev list1 in
        let reverselist2 = List.rev list2 in
        if List.hd reverselist1 > List.hd reverselist2 then 1
        else if List.hd reverselist1 < List.hd reverselist2 then -1
        else
          let list1' = List.rev (List.tl reverselist1) in
          let list2' = List.rev (List.tl reverselist2) in
          cmp list1' list2'

let rec add' list1 list2 carry =
  match list1, list2, carry with
  | list1, [], 0 -> list1
  | [], list2, 0 -> list2
  | list1, [], _ -> add' list1 [ carry ] 0
  | [], list2, _ -> add' [ carry ] list2 0
  | h1 :: t1, h2 :: t2, _ ->
      let sum = h1 + h2 + carry in
      (sum mod radix) :: add' t1 t2 (sum / radix)

let rec sub' list1 list2 carry =
  match list1, list2, carry with
  | [], [], 0 -> []
  | _, [], 0 -> list1
  | _, [], _ -> sub' list1 [ carry ] 0
  | [], _, _ -> sub' [ 0 ] list2 carry
  | h1 :: t1, h2 :: t2, _ ->
      let diff = h1 - h2 - carry in
      if diff >= 0 then diff :: sub' t1 t2 0 else (diff + 10) :: sub' t1 t2 1

let double listy = add' listy listy 0

let rec mul' list1 list2 powerof2 =
  if cmp powerof2 list1 = 1 then list1, [ 0 ]
  else
    let rem, prod = mul' list1 (double list2) (double powerof2) in
    if cmp rem powerof2 = -1 then rem, prod
    else trimzeros (sub' rem powerof2 0), add' prod list2 0

let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
  if neg1 = neg2 then Bigint (neg1, add' value1 value2 0)
  else if cmp value1 value2 = 1 then
    Bigint (neg1, trimzeros (sub' value1 value2 0))
  else if cmp value1 value2 = -1 then
    Bigint (neg2, trimzeros (sub' value2 value1 0))
  else zero

let swap_sign = function
  | Pos -> Neg
  | Neg -> Pos

let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
  if neg1 = neg2 then
    if cmp value1 value2 = 1 then
      Bigint (neg1, trimzeros (sub' value1 value2 0))
    else if cmp value1 value2 = -1 then
      Bigint (swap_sign neg1, trimzeros (sub' value2 value1 0))
    else zero
  else Bigint (neg1, add' value1 value2 0)

let mul (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
  let _, prod = mul' value1 value2 [ 1 ] in
  if neg1 = neg2 then Bigint (Pos, prod) else Bigint (Neg, prod)

let rec div_rem' list1 list2' powerof2 =
  if cmp list2' list1 = 1 then [], list1
  else
    let quo, rem =
      div_rem' list1 (double list2') (double powerof2)
    in
    if cmp rem list2' = -1 then quo, rem
    else add' quo powerof2 0, trimzeros (sub' rem list2' 0)

let div_rem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
  let quo, rem = div_rem' value1 value2 [ 1 ] in
  let rem = if rem = [] then zero else Bigint (neg1, rem) in
  if neg1 = neg2 then Bigint (Pos, quo), rem
  else Bigint (Neg, quo), rem

let compare (Bigint (neg1, v1)) (Bigint (neg2, v2)) =
  match neg1, neg2 with
  | Neg, Pos -> -1
  | Pos, Neg -> 1
  | Neg, Neg -> ~-(cmp v1 v2)
  | Pos, Pos -> cmp v1 v2

let sign n = if n = zero then 0 else if compare n zero < 0 then -1 else 1

let gt x y = compare x y > 0

let lt x y = compare x y < 0

let div a b =
  let quo, _ = div_rem a b in
  quo

let rem a b =
  let _, rem = div_rem a b in
  rem

let rec ediv_rem' t0 t1 cum =
  let (Bigint (_, v0)) = t0 in
  let t0' = Bigint (Pos, v0) in
  let (Bigint (_, v1)) = t1 in
  let t1' = Bigint (Pos, v1) in
  let r = sub t0' t1' in
  if cmp v0 v1 = 1 then ediv_rem' r t1' (add cum one)
  else
    let (Bigint (_, rv)) = r in
    if cmp rv [ 0 ] = 0 then cum, r else add cum one, r

let ediv_rem a b =
  if b = zero then raise Division_by_zero
  else
    let (Bigint (neg1, _)) = a in
    let (Bigint (neg2, _)) = b in
    match neg1, neg2 with
    | Pos, Pos -> div_rem a b
    | Pos, Neg -> div_rem a b
    | Neg, _ ->
        let Bigint (_, q), Bigint (_, r) = ediv_rem' a b zero in
        let r = trimzeros r in
        Bigint (Neg, q), Bigint (Pos, r)

let ediv a b =
  let quo, _ = ediv_rem a b in
  quo

let erem a b =
  let _, rem = ediv_rem a b in
  rem

let cdiv a b =
  let quo, rem = div_rem a b in
  if gt rem zero then add quo one else quo

let fdiv a b =
  let quo, rem = div_rem a b in
  if lt rem zero then sub quo one else quo

let divexact a b =
  let quo, _ = div_rem a b in
  quo

let is_even (Bigint (_neg, value)) =
  let _, rem = div_rem' value [ 2 ] [ 1 ] in
  rem = [] || rem = [ 0 ]

let is_odd a = not (is_even a)

let rec gcd' a b =
  let c = erem a b in
  if c = zero then b else gcd' b c

let gcd x y = gcd' x y

let rec pow' base exp acc =
  if exp <= 0 then acc else pow' base (exp - 1) (mul acc base)

let pow base exp =
  if exp < 0 then
    raise (Invalid_argument "The exp must be >= 0")
  else if exp = 0 then one
  else if exp = 1 then base
  else pow' base exp one

let abs (Bigint (_neg, value)) = Bigint (Pos, value)

let shift_left x n = mul x (pow (of_int 2) n)

let shift_right x n = div x (pow (of_int 2) n)

let neg (Bigint (sn, n)) =
  match sn with
  | Pos -> Bigint (Neg, n)
  | Neg -> Bigint (Pos, n)

let equal x y = compare x y = 0

let leq x y = compare x y < 1

let geq x y = compare x y > -1

let succ x = add x one

let pred x = sub x one

let numbits n' =
  let rec helper_numbits n acc =
    if gt n zero then helper_numbits (div n two) (acc + 1) else acc
  in
  helper_numbits (abs n') 0

let logand n1 n2 =
  let rec helper_logand n1 n2 byte_val res =
    if gt n1 zero || gt n2 zero then
      let res' = add res byte_val in
      let n1' = div n1 two in
      let n2' = div n2 two in
      let byte_val' = mul byte_val two in
      helper_logand n1' n2' byte_val' res'
    else res
  in
  helper_logand n1 n2 one zero

let logor n1 n2 =
  let rec helper_logor n1 n2 byte_val res =
    if gt n1 zero || gt n2 zero then
      let n1' = div n1 two in
      let n2' = div n2 two in
      let byte_val' = mul byte_val two in
      let res' =
        if equal (rem n1 two) one || equal (rem n2 two) one then
          add res byte_val
        else res
      in
      helper_logor n1' n2' byte_val' res'
    else res
  in
  helper_logor n1 n2 one zero

let logxor n1 n2 =
  let rec logxor_helper n1 n2 byte_val res =
    if gt n1 zero || gt n2 zero then
      let n1' = div n1 two in
      let n2' = div n2 two in
      let byte_val' = mul byte_val two in
      let res' =
        if not @@ equal (rem n1 two) (rem n2 two) then add res byte_val
        else res
      in
      logxor_helper n1' n2' byte_val' res'
    else res
  in
  logxor_helper n1 n2 one zero

let lognot n1 =
  let rec lognot_helper byte_val =
    if lt byte_val n1 then lognot_helper (mul byte_val two) else byte_val
  in
  let byte_val = lognot_helper one in
  sub byte_val n1

let min x y = if leq x y then x else y

let max x y = if geq x y then x else y

let ( ~- ) = neg

let ( ~+ ) x = x

let ( + ) = add

let ( - ) = sub

let ( * ) = mul

let ( / ) = div

let ( /> ) = cdiv

let ( /< ) = fdiv

let ( /| ) = divexact

let ( mod ) = rem

let ( % ) = rem

let ( land ) = logand

let ( lor ) = logor

let ( lxor ) = logxor

let ( ~! ) = lognot

let ( lsl ) = shift_left

let ( asr ) = shift_right

let ( ~$ ) = of_int

let ( ** ) = pow

let ( = ) = equal

let ( < ) = lt

let ( > ) = gt

let ( <= ) = leq

let ( >= ) = geq

let ( <> ) x y = not (equal x y)

let to_int i =
  if i > of_int max_int || i < of_int min_int then None
  else Some (int_of_string (to_string i))

let to_int_exn i =
  match to_int i with
  | None -> raise Overflow
  | Some x -> x

let to_int32 i =
  if i > of_int32 Int32.max_int || i < of_int32 Int32.min_int then
    raise Overflow
  else Int32.of_string (to_string i)

let to_int64 i =
  if i > of_int64 Int64.max_int || i < of_int64 Int64.min_int then
    raise Overflow
  else Int64.of_string (to_string i)

let to_nativeint i =
  if i > of_nativeint Nativeint.max_int || i < of_nativeint Nativeint.min_int
  then raise Overflow
  else Nativeint.of_string (to_string i)

let to_float i = float_of_string (to_string i)

let t_of_sexp s =
  match s with
  | Sexplib.Sexp.Atom s -> of_string s
  | Sexplib.Sexp.List
      [
        Sexplib.Sexp.Atom float_part;
        Sexplib.Sexp.Atom "+";
        Sexplib.Sexp.Atom rational_part;
      ] ->
      let t1 = of_string float_part in
      let t2 = of_string rational_part in
      add t1 t2
  | Sexplib.Sexp.List _ ->
      Sexplib.Conv.of_sexp_error
        "expected Atom or List [float; \"+\"; rem]" s

let sexp_of_t t = to_string t |> Sexplib.Sexp.Atom

let bit_and = logand

let bit_or = logor

let bit_xor = logxor

let bit_not = lognot
