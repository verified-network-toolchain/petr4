open BinPos
open Datatypes

module N =
 struct
  (** val succ_double : Bigint.t -> Bigint.t **)

  let succ_double x =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> (Bigint.of_zarith_bigint Z.one))
      (fun p ->
      ((fun p -> Bigint.of_zarith_bigint (Z.succ (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p))))
      p))
      x

  (** val double : Bigint.t -> Bigint.t **)

  let double n =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> (Bigint.of_zarith_bigint Z.zero))
      (fun p ->
      ((fun p -> Bigint.of_zarith_bigint (Z.mul (Z.of_int 2) (Bigint.to_zarith_bigint p)))
      p))
      n

  (** val add : Bigint.t -> Bigint.t -> Bigint.t **)

  let add n m =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
        (fun _ -> n)
        (fun q -> (Pos.add p q))
        m)
      n

  (** val sub : Bigint.t -> Bigint.t -> Bigint.t **)

  let sub n m =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> (Bigint.of_zarith_bigint Z.zero))
      (fun n' ->
      (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
        (fun _ -> n)
        (fun m' ->
        match Pos.sub_mask n' m' with
        | Pos.IsPos p -> p
        | _ -> (Bigint.of_zarith_bigint Z.zero))
        m)
      n

  (** val compare : Bigint.t -> Bigint.t -> comparison **)

  let compare n m =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ ->
      (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
        (fun _ -> Eq)
        (fun _ -> Lt)
        m)
      (fun n' ->
      (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
        (fun _ -> Gt)
        (fun m' -> Pos.compare n' m')
        m)
      n

  (** val leb : Bigint.t -> Bigint.t -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val log2 : Bigint.t -> Bigint.t **)

  let log2 n =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> (Bigint.of_zarith_bigint Z.zero))
      (fun p0 ->
      (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
        (fun p -> (Pos.size p))
        (fun p -> (Pos.size p))
        (fun _ -> (Bigint.of_zarith_bigint Z.zero))
        p0)
      n

  (** val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
        (fun _ -> ((Bigint.of_zarith_bigint Z.zero),
        (Bigint.of_zarith_bigint Z.one)))
        (fun p ->
        (fun f2p1 f2p f1 p -> if Z.leq (Bigint.to_zarith_bigint p) Z.one then f1 () else let (q,r) = Z.div_rem (Bigint.to_zarith_bigint p) (Z.of_int 2) in if Z.equal r Z.zero then f2p (Bigint.of_zarith_bigint q) else f2p1 (Bigint.of_zarith_bigint q))
          (fun _ -> ((Bigint.of_zarith_bigint Z.zero),
          (Bigint.of_zarith_bigint Z.one)))
          (fun _ -> ((Bigint.of_zarith_bigint Z.zero),
          (Bigint.of_zarith_bigint Z.one)))
          (fun _ -> ((Bigint.of_zarith_bigint Z.one),
          (Bigint.of_zarith_bigint Z.zero)))
          p)
        b)
      a

  (** val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t **)

  let div_eucl a b =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> ((Bigint.of_zarith_bigint Z.zero),
      (Bigint.of_zarith_bigint Z.zero)))
      (fun na ->
      (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
        (fun _ -> ((Bigint.of_zarith_bigint Z.zero), a))
        (fun _ -> pos_div_eucl na b)
        b)
      a

  (** val to_nat : Bigint.t -> int **)

  let to_nat a =
    (fun fO fp n -> if Z.sign (Bigint.to_zarith_bigint n) <= 0 then fO () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a
 end
