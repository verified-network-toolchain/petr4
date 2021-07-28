open BinNums
open Coqlib
open Datatypes
open EquivDec
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

module PTree =
 struct
  type elt = positive

  (** val elt_eq : positive -> positive -> bool **)

  let elt_eq =
    peq

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val get : positive -> 'a1 t -> 'a1 option **)

  let rec get i = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match i with
     | Coq_xI ii -> get ii r
     | Coq_xO ii -> get ii l
     | Coq_xH -> o)

  (** val set : positive -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec set i v = function
  | Leaf ->
    (match i with
     | Coq_xI ii -> Node (Leaf, None, (set ii v Leaf))
     | Coq_xO ii -> Node ((set ii v Leaf), None, Leaf)
     | Coq_xH -> Node (Leaf, (Some v), Leaf))
  | Node (l, o, r) ->
    (match i with
     | Coq_xI ii -> Node (l, o, (set ii v r))
     | Coq_xO ii -> Node ((set ii v l), o, r)
     | Coq_xH -> Node (l, (Some v), r))

  (** val remove : positive -> 'a1 t -> 'a1 t **)

  let rec remove i m =
    match i with
    | Coq_xI ii ->
      (match m with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match l with
          | Leaf ->
            (match o with
             | Some _ -> Node (l, o, (remove ii r))
             | None ->
               (match remove ii r with
                | Leaf -> Leaf
                | Node (t0, o0, t1) -> Node (Leaf, None, (Node (t0, o0, t1)))))
          | Node (_, _, _) -> Node (l, o, (remove ii r))))
    | Coq_xO ii ->
      (match m with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match o with
          | Some _ -> Node ((remove ii l), o, r)
          | None ->
            (match r with
             | Leaf ->
               (match remove ii l with
                | Leaf -> Leaf
                | Node (t0, o0, t1) -> Node ((Node (t0, o0, t1)), None, Leaf))
             | Node (_, _, _) -> Node ((remove ii l), o, r))))
    | Coq_xH ->
      (match m with
       | Leaf -> Leaf
       | Node (l, _, r) ->
         (match l with
          | Leaf ->
            (match r with
             | Leaf -> Leaf
             | Node (_, _, _) -> Node (l, None, r))
          | Node (_, _, _) -> Node (l, None, r)))

  (** val bempty : 'a1 t -> bool **)

  let rec bempty = function
  | Leaf -> true
  | Node (l, o, r) ->
    (match o with
     | Some _ -> false
     | None -> (&&) (bempty l) (bempty r))

  (** val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec beq beqA m1 m2 =
    match m1 with
    | Leaf -> bempty m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> bempty m1
       | Node (l2, o2, r2) ->
         (&&)
           ((&&)
             (match o1 with
              | Some y1 ->
                (match o2 with
                 | Some y2 -> beqA y1 y2
                 | None -> false)
              | None -> (match o2 with
                         | Some _ -> false
                         | None -> true)) (beq beqA l1 l2)) (beq beqA r1 r2))

  (** val prev_append : positive -> positive -> positive **)

  let rec prev_append i j =
    match i with
    | Coq_xI i' -> prev_append i' (Coq_xI j)
    | Coq_xO i' -> prev_append i' (Coq_xO j)
    | Coq_xH -> j

  (** val prev : positive -> positive **)

  let prev i =
    prev_append i Coq_xH

  (** val xmap : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t **)

  let rec xmap f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmap f l (Coq_xO i)),
        (match o with
         | Some x -> Some (f (prev i) x)
         | None -> None), (xmap f r (Coq_xI i)))

  (** val map : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    xmap f m Coq_xH

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map1 f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((map1 f l), (option_map f o), (map1 f r))

  (** val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t **)

  let coq_Node' l x r =
    match l with
    | Leaf ->
      (match x with
       | Some _ -> Node (l, x, r)
       | None ->
         (match r with
          | Leaf -> Leaf
          | Node (_, _, _) -> Node (l, x, r)))
    | Node (_, _, _) -> Node (l, x, r)

  (** val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t **)

  let rec filter1 pred = function
  | Leaf -> Leaf
  | Node (l, o, r) ->
    let o' = match o with
             | Some x -> if pred x then o else None
             | None -> None
    in
    coq_Node' (filter1 pred l) o' (filter1 pred r)

  (** val xcombine_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec xcombine_l f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_l f l) (f o None) (xcombine_l f r)

  (** val xcombine_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec xcombine_r f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_r f l) (f None o) (xcombine_r f r)

  (** val combine :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec combine f m1 m2 =
    match m1 with
    | Leaf -> xcombine_r f m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> xcombine_l f m1
       | Node (l2, o2, r2) ->
         coq_Node' (combine f l1 l2) (f o1 o2) (combine f r1 r2))

  (** val xelements :
      'a1 t -> positive -> (positive * 'a1) list -> (positive * 'a1) list **)

  let rec xelements m i k =
    match m with
    | Leaf -> k
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         xelements l (Coq_xO i) (((prev i), x) :: (xelements r (Coq_xI i) k))
       | None -> xelements l (Coq_xO i) (xelements r (Coq_xI i) k))

  (** val elements : 'a1 t -> (positive * 'a1) list **)

  let elements m =
    xelements m Coq_xH []

  (** val xkeys : 'a1 t -> positive -> positive list **)

  let xkeys m i =
    List0.map fst (xelements m i [])

  (** val xfold :
      ('a2 -> positive -> 'a1 -> 'a2) -> positive -> 'a1 t -> 'a2 -> 'a2 **)

  let rec xfold f i m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         let v1 = xfold f (Coq_xO i) l v in
         let v2 = f v1 (prev i) x in xfold f (Coq_xI i) r v2
       | None -> let v1 = xfold f (Coq_xO i) l v in xfold f (Coq_xI i) r v1)

  (** val fold : ('a2 -> positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m v =
    xfold f Coq_xH m v

  (** val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold1 f m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x -> let v1 = fold1 f l v in let v2 = f v1 x in fold1 f r v2
       | None -> let v1 = fold1 f l v in fold1 f r v1)
 end

module Tree_Properties =
 functor (T:TREE) ->
 struct
  (** val fold_ind_aux :
      ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> 'a1 T.t -> ('a1 T.t -> __ ->
      'a3) -> ('a1 T.t -> 'a2 -> T.elt -> 'a1 -> __ -> __ -> 'a3 -> 'a3) ->
      (T.elt * 'a1) list -> 'a1 T.t -> 'a3 **)

  let fold_ind_aux f init _ h_base h_rec l m =
    let f' = fun p a -> f a (fst p) (snd p) in
    let h_base' = fun m0 -> h_base m0 __ in
    let h_rec' = fun k v _ a hR m0 ->
      h_rec m0 a k v __ __ (hR (T.remove k m0) __)
    in
    let rec f0 = function
    | [] -> (fun _ _ m0 _ -> h_base' m0)
    | y :: l1 ->
      let iHl = f0 l1 in
      (fun _ _ m0 _ ->
      h_rec' (fst y) (snd y) l1 (fold_right f' init l1) (iHl __ __) m0)
    in f0 l __ __ m __

  (** val fold_ind :
      ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> 'a1 T.t -> ('a1 T.t -> __ ->
      'a3) -> ('a1 T.t -> 'a2 -> T.elt -> 'a1 -> __ -> __ -> 'a3 -> 'a3) ->
      'a3 **)

  let fold_ind f init m_final h_base h_rec =
    let l' = rev (T.elements m_final) in
    fold_ind_aux f init m_final h_base h_rec l' m_final

  (** val cardinal : 'a1 T.t -> nat **)

  let cardinal x =
    length (T.elements x)

  (** val for_all : 'a1 T.t -> (T.elt -> 'a1 -> bool) -> bool **)

  let for_all m f =
    T.fold (fun b x a -> (&&) b (f x a)) m true

  (** val exists_ : 'a1 T.t -> (T.elt -> 'a1 -> bool) -> bool **)

  let exists_ m f =
    T.fold (fun b x a -> (||) b (f x a)) m false

  (** val coq_Equal_dec : 'a1 coq_EqDec -> 'a1 T.t -> 'a1 T.t -> bool **)

  let coq_Equal_dec eqAdec m1 m2 =
    let filtered_var =
      T.beq (fun a1 a2 -> (fun x -> x) (equiv_dec eqAdec a1 a2)) m1 m2
    in
    if filtered_var then true else false

  (** val coq_Equal_EqDec : 'a1 coq_EqDec -> 'a1 T.t coq_EqDec **)

  let coq_Equal_EqDec =
    coq_Equal_dec

  (** val of_list : (T.elt * 'a1) list -> 'a1 T.t **)

  let of_list l =
    let f = fun m k_v -> T.set (fst k_v) (snd k_v) m in fold_left f l T.empty
 end

module PTree_Properties = Tree_Properties(PTree)
