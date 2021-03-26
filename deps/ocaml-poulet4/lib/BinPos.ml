open BinPosDef
open Datatypes
open Nat

module Pos =
 struct
  (** val succ : Bigint.t -> Bigint.t **)

  let rec succ x =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      (succ p))
      (fun p ->
      (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
      p)
      (fun _ ->
      (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      (Bigint.of_zarith_bigint Z.one))
      x

  (** val add : Bigint.t -> Bigint.t -> Bigint.t **)

  let rec add x y =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (add_carry p q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (add p q))
        (fun _ ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (add p q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (add p q))
        (fun _ ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (succ q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        q)
        (fun _ ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (Bigint.of_zarith_bigint Z.one))
        y)
      x

  (** val add_carry : Bigint.t -> Bigint.t -> Bigint.t **)

  and add_carry x y =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (add_carry p q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (add_carry p q))
        (fun _ ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (add_carry p q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (add p q))
        (fun _ ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (succ q))
        (fun q ->
        (fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        (succ q))
        (fun _ ->
        (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
        (Bigint.of_zarith_bigint Z.one))
        y)
      x

  (** val pred_double : Bigint.t -> Bigint.t **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
      ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      p))
      (fun p ->
      (fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
      (pred_double p))
      (fun _ -> (Bigint.of_zarith_bigint Z.one))
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Bigint.t
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos (Bigint.of_zarith_bigint Z.one)
  | IsPos p ->
    IsPos
      ((fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
      p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p ->
    IsPos
      ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      p)
  | x0 -> x0

  (** val double_pred_mask : Bigint.t -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p -> IsPos
      ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      p)))
      (fun p -> IsPos
      ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : Bigint.t -> Bigint.t -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos
        ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
        p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : Bigint.t -> Bigint.t -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val size : Bigint.t -> Bigint.t **)

  let rec size p =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> (Bigint.of_zarith_bigint Z.one))
      p

  (** val compare_cont : comparison -> Bigint.t -> Bigint.t -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : Bigint.t -> Bigint.t -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Bigint.t -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : Bigint.t -> int **)

  let to_nat x =
    iter_op Nat.add x (Pervasives.succ 0)
 end
