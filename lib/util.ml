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

type ('a,'b) alternative = 
    Left of 'a 
  | Right of 'b
  [@@deriving sexp,yojson]

let option_map f = function
  | Some x -> Some (f x)
  | None -> None

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
  | Some xys -> List.for_all ~f xys
  | None -> false
