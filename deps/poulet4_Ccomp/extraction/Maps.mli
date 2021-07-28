open BinNums
open Coqlib
open Datatypes
open EquivDec
open List0

type __ = Obj.t

module type TREE =
 sig
  type elt

  val elt_eq : elt -> elt -> bool

  type 'x t

  val empty : 'a1 t

  val get : elt -> 'a1 t -> 'a1 option

  val set : elt -> 'a1 -> 'a1 t -> 'a1 t

  val remove : elt -> 'a1 t -> 'a1 t

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (elt * 'a1) list

  val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module PTree :
 sig
  type elt = positive

  val elt_eq : positive -> positive -> bool

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val get : positive -> 'a1 t -> 'a1 option

  val set : positive -> 'a1 -> 'a1 t -> 'a1 t

  val remove : positive -> 'a1 t -> 'a1 t

  val bempty : 'a1 t -> bool

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val prev_append : positive -> positive -> positive

  val prev : positive -> positive

  val xmap : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t

  val map : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t

  val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t

  val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xelements :
    'a1 t -> positive -> (positive * 'a1) list -> (positive * 'a1) list

  val elements : 'a1 t -> (positive * 'a1) list

  val xkeys : 'a1 t -> positive -> positive list

  val xfold :
    ('a2 -> positive -> 'a1 -> 'a2) -> positive -> 'a1 t -> 'a2 -> 'a2

  val fold : ('a2 -> positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module Tree_Properties :
 functor (T:TREE) ->
 sig
  val fold_ind_aux :
    ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> 'a1 T.t -> ('a1 T.t -> __ -> 'a3)
    -> ('a1 T.t -> 'a2 -> T.elt -> 'a1 -> __ -> __ -> 'a3 -> 'a3) ->
    (T.elt * 'a1) list -> 'a1 T.t -> 'a3

  val fold_ind :
    ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> 'a1 T.t -> ('a1 T.t -> __ -> 'a3)
    -> ('a1 T.t -> 'a2 -> T.elt -> 'a1 -> __ -> __ -> 'a3 -> 'a3) -> 'a3

  val cardinal : 'a1 T.t -> nat

  val for_all : 'a1 T.t -> (T.elt -> 'a1 -> bool) -> bool

  val exists_ : 'a1 T.t -> (T.elt -> 'a1 -> bool) -> bool

  val coq_Equal_dec : 'a1 coq_EqDec -> 'a1 T.t -> 'a1 T.t -> bool

  val coq_Equal_EqDec : 'a1 coq_EqDec -> 'a1 T.t coq_EqDec

  val of_list : (T.elt * 'a1) list -> 'a1 T.t
 end

module PTree_Properties :
 sig
  val fold_ind_aux :
    ('a2 -> PTree.elt -> 'a1 -> 'a2) -> 'a2 -> 'a1 PTree.t -> ('a1 PTree.t ->
    __ -> 'a3) -> ('a1 PTree.t -> 'a2 -> PTree.elt -> 'a1 -> __ -> __ -> 'a3
    -> 'a3) -> (PTree.elt * 'a1) list -> 'a1 PTree.t -> 'a3

  val fold_ind :
    ('a2 -> PTree.elt -> 'a1 -> 'a2) -> 'a2 -> 'a1 PTree.t -> ('a1 PTree.t ->
    __ -> 'a3) -> ('a1 PTree.t -> 'a2 -> PTree.elt -> 'a1 -> __ -> __ -> 'a3
    -> 'a3) -> 'a3

  val cardinal : 'a1 PTree.t -> nat

  val for_all : 'a1 PTree.t -> (PTree.elt -> 'a1 -> bool) -> bool

  val exists_ : 'a1 PTree.t -> (PTree.elt -> 'a1 -> bool) -> bool

  val coq_Equal_dec : 'a1 coq_EqDec -> 'a1 PTree.t -> 'a1 PTree.t -> bool

  val coq_Equal_EqDec : 'a1 coq_EqDec -> 'a1 PTree.t coq_EqDec

  val of_list : (PTree.elt * 'a1) list -> 'a1 PTree.t
 end
