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

type has_params = bool
[@@deriving sexp]

type ident_kind =
  | TypeName of has_params
  | Ident of has_params
[@@deriving sexp]

type t [@@deriving sexp]

val reset : unit -> unit
val declare_var : P4string.t -> has_params -> unit
val declare_type : P4string.t -> has_params -> unit
val mark_template : P4string.t -> unit
val get_kind : P4string.t -> ident_kind
val is_typename : P4string.t -> bool
val go_toplevel : unit -> unit
val go_local : unit -> unit                
val push_scope : unit -> unit
val pop_scope : unit -> unit
val print_context : unit -> unit
