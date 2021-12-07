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

module P4Int : sig
  val format_t : Format.formatter -> P4int.t -> unit
end

module P4String : sig
  val format_t : Format.formatter -> P4string.t -> unit
end

module Expression : sig
  val format_t : Format.formatter -> Surface.Expression.t -> unit
end

module MethodPrototype : sig
  val format_t : Format.formatter -> Surface.MethodPrototype.t -> unit
end

module Statement : sig
  val format_t : Format.formatter -> Surface.Statement.t -> unit
end

module Block : sig
  val format_t : Format.formatter -> Surface.Block.t -> unit
end

module Argument : sig
  val format_t : Format.formatter -> Surface.Argument.t -> unit
end

module Type : sig
  val format_t : Format.formatter -> Surface.Type.t -> unit
end

module Annotation : sig
  val format_t : Format.formatter -> Surface.Annotation.t -> unit
end

module Direction : sig
  val format_t : Format.formatter -> Surface.Direction.t -> unit
end

module Parameter : sig
  val format_t : Format.formatter -> Surface.Parameter.t -> unit
end

module Match: sig
  val format_t : Format.formatter -> Surface.Match.t -> unit
end

module Parser : sig
  val format_state : Format.formatter -> Surface.Parser.state -> unit
  val format_states : Format.formatter -> Surface.Parser.state list -> unit
end

module Table : sig
  val format_property : Format.formatter -> Surface.Table.property -> unit
end

module Declaration : sig
  val format_t : Format.formatter -> Surface.Declaration.t -> unit
end

val format_program : Format.formatter -> Surface.program -> unit
