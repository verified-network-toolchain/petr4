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

type t [@@deriving sexp]

val reset : unit -> unit
val declare_var : Info.t * string -> unit
val declare_type : Info.t * string -> unit
val is_typename : Info.t * string -> bool
val go_toplevel : unit -> unit
val go_local : unit -> unit                
val push_scope : unit -> unit
val pop_scope : unit -> unit
val print_context : unit -> unit
