open Basics
open Datatypes
open EquivDec
open List0

module Field =
 struct
  type ('k, 'v) f = 'k * 'v

  type ('k, 'v) fs = ('k, 'v) f list

  (** val key : ('a1, 'a2) f -> 'a1 **)

  let key =
    fst

  (** val value : ('a1, 'a2) f -> 'a2 **)

  let value =
    snd

  (** val keys : ('a1, 'a2) fs -> 'a1 list **)

  let keys x =
    map key x

  (** val values : ('a1, 'a2) fs -> 'a2 list **)

  let values x =
    map value x

  (** val filter : ('a2 -> bool) -> ('a1, 'a2) fs -> ('a1, 'a2) fs **)

  let filter pred =
    filter (compose pred snd)

  (** val map : ('a2 -> 'a3) -> ('a1, 'a2) fs -> ('a1, 'a3) fs **)

  let map f0 =
    map (fun pat -> let (x, u) = pat in (x, (f0 u)))

  (** val fold : ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) fs -> 'a3 -> 'a3 **)

  let fold f0 fds init =
    fold_right (fun pat acc -> let (x, u) = pat in f0 x u acc) init fds

  (** val find_value : ('a1 -> bool) -> ('a1, 'a2) fs -> 'a2 option **)

  let rec find_value f0 = function
  | [] -> None
  | f1 :: fds0 ->
    let (k, v) = f1 in if f0 k then Some v else find_value f0 fds0

  (** val get : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> 'a2 option **)

  let rec get h0 k = function
  | [] -> None
  | f0 :: fds0 ->
    let (k', u') = f0 in if equiv_dec h0 k k' then Some u' else get h0 k fds0

  (** val get_index_rec :
      'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> nat -> nat option **)

  let rec get_index_rec h0 k fds current =
    match fds with
    | [] -> None
    | f0 :: fds0 ->
      let (k', _) = f0 in
      if equiv_dec h0 k k'
      then Some current
      else get_index_rec h0 k fds0 (S current)

  (** val get_index : 'a1 coq_EqDec -> 'a1 -> ('a1, 'a2) fs -> nat option **)

  let get_index h0 k fds =
    get_index_rec h0 k fds O

  (** val update :
      'a1 coq_EqDec -> 'a1 -> 'a2 -> ('a1, 'a2) fs -> ('a1, 'a2) fs **)

  let rec update h0 k u = function
  | [] -> []
  | f0 :: fds0 ->
    let (k', u') = f0 in
    (k', (if equiv_dec h0 k k' then u else u')) :: (update h0 k u fds0)

  (** val eqb_f :
      'a1 coq_EqDec -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) f -> ('a1, 'a2) f
      -> bool **)

  let eqb_f h0 feq pat pat0 =
    let (x1, u1) = pat in
    let (x2, u2) = pat0 in if equiv_dec h0 x1 x2 then feq u1 u2 else false

  (** val eqb_fs :
      'a1 coq_EqDec -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) fs -> ('a1, 'a2) fs
      -> bool **)

  let rec eqb_fs h0 feq fs1 fs2 =
    match fs1 with
    | [] -> (match fs2 with
             | [] -> true
             | _ :: _ -> false)
    | f1 :: fs3 ->
      (match fs2 with
       | [] -> false
       | f2 :: fs4 -> (&&) (eqb_f h0 feq f1 f2) (eqb_fs h0 feq fs3 fs4))

  module RelfEquiv =
   struct
   end

  module FieldTactics =
   struct
   end
 end
