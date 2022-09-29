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
