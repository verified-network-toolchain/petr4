open Bool

(** val eqb_spec : char -> char -> reflect **)

let eqb_spec a b =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
      match eqb_spec b0 b8 with
      | ReflectT ->
        (match eqb_spec b1 b9 with
         | ReflectT ->
           (match eqb_spec b2 b10 with
            | ReflectT ->
              (match eqb_spec b3 b11 with
               | ReflectT ->
                 (match eqb_spec b4 b12 with
                  | ReflectT ->
                    (match eqb_spec b5 b13 with
                     | ReflectT ->
                       (match eqb_spec b6 b14 with
                        | ReflectT -> eqb_spec b7 b15
                        | ReflectF -> ReflectF)
                     | ReflectF -> ReflectF)
                  | ReflectF -> ReflectF)
               | ReflectF -> ReflectF)
            | ReflectF -> ReflectF)
         | ReflectF -> ReflectF)
      | ReflectF -> ReflectF)
      b)
    a


