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

open Core_kernel
open Sexplib.Conv

type t =
  | I of
    { filename :string;
      line_start: int;
      line_end: int option;
      col_start: int;
      col_end : int } [@name "info"]
  | M of string [@name "missing_info"]
[@@deriving sexp,show,yojson]

let dummy = M ""

(* to_string info
   String containing the location information of info *)
let to_string = function
  | M s -> s
  | I {filename; line_start; line_end; col_start; col_end; _ } ->
    let f = "File " ^ filename ^ "," in
    match line_end with
    | None ->
      Printf.sprintf "%s line %d, characters %d-%d"
        f line_start col_start col_end
    | Some line_end ->
      Printf.sprintf "%s from line %d character %d to line %d character %d"
        f line_start col_start line_end col_end

let start_pos = function
    M _ -> (Int.max_value, Int.max_value)
  | I { filename; line_start; line_end; col_start; col_end } ->
    (line_start, col_start)

let end_pos = function
    M _ -> (0, 0)
  | I { filename; line_start; line_end; col_start; col_end } ->
    (match line_end with
     | None -> (line_start, col_end)
     | Some line_end -> (line_end, col_end))

let follows i1 i2 = 
  match i1, i2 with 
    | M _, _
    | _ ,M _ -> false
    | I _, I _ -> 
       begin 
         let l1,c1 = end_pos i1 in 
         let l2,c2 = start_pos i2 in
         (l1 = l2 && c1 = c2)
       end

let file = function
    M _ -> ""
  | I  { filename; line_start; line_end; col_start; col_end } ->
    filename

let merge (info1 : t) (info2 : t) =
  match info2 with
  | M _ -> info1
  | I _ ->
    match info1 with
    | M _ -> info2
    | I _ ->
      let start_l, start_c = Poly.min (start_pos info1) (start_pos info2)   in
      let end_l, end_c     = Poly.max (end_pos info1)   (end_pos info2)     in
      let end_l_opt = if (start_l = end_l) then None else (Some end_l) in
      I { filename = file info1;
          line_start = start_l;
          line_end = end_l_opt;
          col_start = start_c;
          col_end = end_c }

(* Because header unions associate a label with the name of a type
 * this type name must be used to find the actual corresponding type
 * the environment *)
let header_union_info = M "To look up header union type labels in the environment."
