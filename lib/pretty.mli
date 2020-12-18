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
  val format_t : Format.formatter -> Types.Expression.t -> unit
end

module MethodPrototype : sig
  val format_t : Format.formatter -> Types.MethodPrototype.t -> unit
end

module Statement : sig
  val format_t : Format.formatter -> Types.Statement.t -> unit
end

module Block : sig
  val format_t : Format.formatter -> Types.Block.t -> unit
end

module Argument : sig
  val format_t : Format.formatter -> Types.Argument.t -> unit
end

module Type : sig
  val format_t : Format.formatter -> Types.Type.t -> unit
end

module Annotation : sig
  val format_t : Format.formatter -> Types.Annotation.t -> unit
end

module Direction : sig
  val format_t : Format.formatter -> Types.Direction.t -> unit
end

module Parameter : sig
  val format_t : Format.formatter -> Types.Parameter.t -> unit
end

module Match: sig
  val format_t : Format.formatter -> Types.Match.t -> unit
end

module Parser : sig
  val format_state : Format.formatter -> Types.Parser.state -> unit
  val format_states : Format.formatter -> Types.Parser.state list -> unit
end

module Table : sig
  val format_property : Format.formatter -> Types.Table.property -> unit
end

module Declaration : sig
  val format_t : Format.formatter -> Types.Declaration.t -> unit
end

val format_program : Format.formatter -> Types.program -> unit
