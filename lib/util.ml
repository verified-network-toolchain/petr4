(* Copyright 2019-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *)
open Core

module StringMap = Map.Make(String)

type ('a,'b) alternative =
    Left of 'a
  | Right of 'b
  [@@deriving sexp,show,yojson]

let option_map f = function
  | Some x -> Some (f x)
  | None -> None

let option_collapse = function
  | Some (Some x) -> Some x
  | _ -> None

let opt_to_exn e = function
  | Some x -> x
  | None -> raise e

let list_option_flip l =
  let check checked x =
    match checked, x with
    | Some l, Some x -> Some (l @ [x])
    | _ -> None
  in
  List.fold ~f:check ~init:(Some []) l

let uncurry f (x, y) = f x y

let rec combine_opt xs ys =
  match xs, ys with
  | x :: xs, y :: ys ->
      (Some x, Some y) :: combine_opt xs ys
  | x :: xs, [] ->
      (Some x, None) :: combine_opt xs []
  | [], y :: ys ->
      (None, Some y) :: combine_opt [] ys
  | [], [] -> []

let eq_lists ~f xs ys =
  match List.zip xs ys with
  | Ok xys -> List.for_all ~f xys
  | Unequal_lengths -> false

let zip_map_fold ~f ~merge ~init xs ys =
  match List.zip xs ys with
  | Ok xys ->
     Some (List.fold_left ~f:merge ~init @@ List.map ~f xys)
  | Unequal_lengths -> None

let rec find_and_drop ~f xs =
  match xs with
  | [] -> None, []
  | x :: xs ->
     if f x
     then Some x, xs
     else let found, list = find_and_drop ~f xs in
          found, x :: list

let rec find_map_and_drop ~f xs =
  match xs with
  | [] -> None, []
  | x :: xs ->
     match f x with
     | Some y -> Some y, xs
     | None ->
        let found, list = find_map_and_drop ~f xs in
        found, x :: list

let find_exn xs x =
  match List.Assoc.find xs x ~equal:String.equal with
  | Some v -> v
  | None -> raise (Failure ("couldn't find name " ^ x))

let sorted_eq xs ys ~compare =
  let xs_sorted = List.sort ~compare xs in
  let ys_sorted = List.sort ~compare ys in
  let eq x y = compare x y = 0 in
  List.equal eq xs_sorted ys_sorted

let sorted_eq_strings xs ys =
  sorted_eq xs ys ~compare:String.compare

type bigint = Bigint.t [@@deriving sexp]

let bigint_to_yojson (b:bigint) : Yojson.Safe.t =
  `String (Bigint.to_string b)

let bigint_of_yojson (json:Yojson.Safe.t) =
  Ok (Bigint.of_string (Yojson.Safe.to_string json))

let show_bigint (b:bigint) : string =
  Bigint.to_string b

let pp_bigint fmt b = 
  Format.pp_print_string fmt (Bigint.to_string b)

let eq_opt ~f o1 o2 =
  match o1, o2 with
  | None, None -> true
  | Some v1, Some v2 -> f v1 v2
  | _ -> false

let rec repeat (n: int) (a: 'a) : 'a list =
  if n > 0
  then a :: repeat (n - 1) a
  else []

let pad8 (bits: bool list) =
  let gap = 8 - List.length bits in
  if gap > 0
  then bits @ repeat gap false
  else bits

let rec pos_int_to_rev_bits' (acc: bool list) (k: int) : bool list =
  assert (k >= 0);
  if k = 0
  then pad8 acc
  else if k mod 2 = 0
       then pos_int_to_rev_bits' (false :: acc) (k / 2)
       else pos_int_to_rev_bits' (true :: acc)  ((k - 1) / 2)

let pos_int_to_rev_bits (k: int) : bool list =
  pos_int_to_rev_bits' [] k

(** Convert a hexadecimal nibble to a string of 4 bits. 
 * Values outside [a-fA-F0-9] are sent to the empty list. *)
let nibble_to_bits (c: char) : bool list =
  match Char.uppercase c with
  | '0' -> [false; false; false; false]
  | '1' -> [false; false; false;  true]
  | '2' -> [false; false;  true; false]
  | '3' -> [false; false;  true;  true]
  | '4' -> [false;  true; false; false]
  | '5' -> [false;  true; false;  true]
  | '6' -> [false;  true;  true; false]
  | '7' -> [false;  true;  true;  true]
  | '8' -> [ true; false; false; false]
  | '9' -> [ true; false; false;  true]
  | 'A' -> [ true; false;  true; false]
  | 'B' -> [ true; false;  true;  true]
  | 'C' -> [ true;  true; false; false]
  | 'D' -> [ true;  true; false;  true]
  | 'E' -> [ true;  true;  true; false]
  | 'F' -> [ true;  true;  true;  true]
  |  _  -> []

(** If nibble_to_bits c = bits and bits is non-nil,
 * then bits_to_nibble bits = Char.uppercase c. *)
let bits_to_nibble (l: bool list) : char option =
  match l with
  | [false; false; false; false] -> Some '0'
  | [false; false; false;  true] -> Some '1'
  | [false; false;  true; false] -> Some '2'
  | [false; false;  true;  true] -> Some '3'
  | [false;  true; false; false] -> Some '4'
  | [false;  true; false;  true] -> Some '5'
  | [false;  true;  true; false] -> Some '6'
  | [false;  true;  true;  true] -> Some '7'
  | [ true; false; false; false] -> Some '8'
  | [ true; false; false;  true] -> Some '9'
  | [ true; false;  true; false] -> Some 'A'
  | [ true; false;  true;  true] -> Some 'B'
  | [ true;  true; false; false] -> Some 'C'
  | [ true;  true; false;  true] -> Some 'D'
  | [ true;  true;  true; false] -> Some 'E'
  | [ true;  true;  true;  true] -> Some 'F'
  |                            _ -> None

let string_to_bits (s: string) : bool list =
  s
  |> String.to_list
  |> List.concat_map ~f:nibble_to_bits

let bool_to_int (b: bool) : int =
  if b then 1 else 0

let rec group8' acc lst =
  match lst with
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: lst' ->
     group8' ([b1; b2; b3; b4; b5; b6; b7; b8] :: acc) lst'
  | [] -> acc
  | _ -> lst :: acc

let group8 lst =
  group8' [] lst
  |> List.rev

let rec bits_to_nibbles (bs: bool list) : char list option =
  match bs with
  | [] -> Some []
  | b1 :: b2 :: b3 :: b4 :: some_more ->
    begin match bits_to_nibble [b1; b2; b3; b4],
                bits_to_nibbles some_more with
    | Some nibble, Some more ->
      Some (nibble :: more)
    | _, _ -> None
    end
  | _ -> None

let bits_to_string (bs: bool list) : string =
  match bits_to_nibbles bs with
  | Some nibbles -> String.of_char_list nibbles
  | None ->
    failwith (Printf.sprintf "bool list of irregular length %d passed to bits_to_string" (List.length bs))
  
let hex_of_nibble (i : int) : string =
  match i with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"
  | 10 -> "A"
  | 11 -> "B"
  | 12 -> "C"
  | 13 -> "D"
  | 14 -> "E"
  | 15 -> "F"
  | _ -> failwith ("hex_of_nibble: " ^ string_of_int i)
       
let hex_of_int (i : int) : string =
  hex_of_nibble (i/16) ^ hex_of_nibble (i%16) ^ " "

let hex_of_char (c : char) : string =
  c |> Char.to_int |> hex_of_int

let hex_of_string (s : string) : string =
  s
  |> String.to_list
  |> List.map ~f:hex_of_char
  |> List.fold_left ~init:"" ~f:(^)
