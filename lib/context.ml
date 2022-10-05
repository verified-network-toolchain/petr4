(* Copyright 2018-present Cornell University
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
open Util

type t = (bool StringMap.t) list [@@deriving sexp]

(* Current context, stored as a mutable global variable *)
let context = ref [StringMap.empty]
let backup = ref []

(* Resets context *)
let reset () =
  context := [StringMap.empty];
  backup := []

(* Associates [id] with [b] in map for current scope *)
let declare (id: P4string.t) b =
  match !context with
  | [] ->
    failwith "ill-formed context"
  | m :: l ->
    context := StringMap.set m ~key:id.str ~data:b :: l

let declare_type id = declare id true
let declare_var id = declare id false

(* Tests whether [id] is known as a type name. *)
let is_typename (id: P4string.t) =
  let rec loop =
    function
    | [] ->
      false
    | m::rest ->
      match StringMap.find m id.str with
      | None -> loop rest
      | Some b -> b in
  loop !context

(* Takes a snapshot of the current context. *)
let push_scope () = context := StringMap.empty::!context

(* Remove scope *)
let pop_scope () =
  match !context with
  | [] ->
    failwith "ill-formed context"
  | [_] ->
    failwith "pop would produce ill-formed context"
  | _::l ->
    context := l

let go_toplevel () =
  let rec loop c =
    match c with
    | [] ->
      failwith "ill-formed context"
    | [_] ->
      context := c
    | _::l ->
      loop l in
  backup := !context;
  loop !context

let go_local () =
  context := !backup

(* Printing functions for debugging *)
let print_entry x b = Printf.printf "%s : %b" x b
let print_map m = StringMap.iteri m ~f:(fun ~key:x ~data:b -> print_entry x b; print_endline "")
let print_context () = List.iter !context ~f:(fun m -> print_map m; print_endline "----")
