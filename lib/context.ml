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

type has_params = bool
[@@deriving sexp]

type ident_kind =
  | TypeName of has_params
  | Ident of has_params
[@@deriving sexp]

type t = (ident_kind StringMap.t) list [@@deriving sexp]

(* Current context, stored as a mutable global variable *)
let context : t ref = ref [StringMap.empty]
let backup : t ref = ref []

(* Resets context *)
let reset () =
  context := [StringMap.empty];
  backup := []

(* Associates [id] with [k] in map for current scope *)
let declare (id : P4string.t) (k : ident_kind) : unit =
  match !context with
  | [] ->
    failwith "ill-formed context"
  | m :: l ->
    context := StringMap.set m ~key:id.str ~data:k :: l

let declare_type id has_params = declare id (TypeName has_params)
let declare_var id has_params = declare id (Ident has_params)

(* Tests whether [id] is known as a type name. *)
let get_kind (id: P4string.t) : ident_kind =
  let rec loop =
    function
    | [] ->
      Ident false
    | m::rest ->
      match StringMap.find m id.str with
      | None -> loop rest
      | Some k -> k in
  loop !context

let is_typename (id: P4string.t) : bool =
  match get_kind id with
  | TypeName _ -> true
  | _ -> false

let mark_template (id: P4string.t) =
  let rec loop =
    function
    | [] -> []
    | m::rest ->
      match StringMap.find m id.str with
      | None -> m :: loop rest
      | Some (TypeName b) ->
        StringMap.set m ~key:id.str ~data:(TypeName true) :: rest
      | Some (Ident b) ->
        StringMap.set m ~key:id.str ~data:(Ident true) :: rest
  in
  context := loop !context

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
let print_entry x k =
  match k with
  | TypeName true ->
    Printf.printf "%s : type<...>" x
  | TypeName false ->
    Printf.printf "%s : type" x
  | Ident true ->
    Printf.printf "%s : ident<...>" x
  | Ident false ->
    Printf.printf "%s : ident" x

let print_map m = StringMap.iteri m ~f:(fun ~key:x ~data:k -> print_entry x k; print_endline "")
let print_context () = List.iter !context ~f:(fun m -> print_map m; print_endline "----")
