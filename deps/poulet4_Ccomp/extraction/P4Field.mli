open Basics
open Datatypes
open EquivDec
open List0

module Field :
 sig
  type ('k, 'v) f = 'k * 'v

  type ('k, 'v) fs = ('k, 'v) f list

  val key : ('a1, 'a2) f -> 'a1

  val value : ('a1, 'a2) f -> 'a2

  val keys : ('a1, 'a2) fs -> 'a1 list

  val values : ('a1, 'a2) fs -> 'a2 list

  val filter : ('a2 -> bool) -> ('a1, 'a2) fs -> ('a1, 'a2) fs

  val map : ('a2 -> 'a3) -> ('a1, 'a2) fs -> ('a1, 'a3) fs

  val fold : ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) fs -> 'a3 -> 'a3

  val find_value : ('a1 -> bool) -> ('a1, 'a2) fs -> 'a2 option

  val get : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> 'a2 option

  val get_index_rec :
    'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> nat -> nat option

  val get_index : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> nat option

  val update : 'a1 coq_EqDec -> 'a1 -> 'a2 -> ('a1, 'a2) fs -> ('a1, 'a2) fs

  val eqb_f :
    'a1 coq_EqDec -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) f -> ('a1, 'a2) f ->
    bool

  val eqb_fs :
    'a1 coq_EqDec -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) fs -> ('a1, 'a2) fs
    -> bool

  module RelfEquiv :
   sig
   end

  module FieldTactics :
   sig
   end
 end
