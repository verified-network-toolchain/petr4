open AST0
open BinNums
open BinPos
open Bool
open Datatypes
open EquivDec
open EquivUtil

module P = P4cub

module F = P.F

module E = P.Expr

module TypeEquivalence =
 struct
  (** val eqbt : E.t -> E.t -> bool **)

  let rec eqbt _UU03c4_1 _UU03c4_2 =
    let lstruct =
      let rec lstruct ts1 ts2 =
        match ts1 with
        | [] -> (match ts2 with
                 | [] -> true
                 | _ :: _ -> false)
        | t1 :: ts3 ->
          (match ts2 with
           | [] -> false
           | t2 :: ts4 -> (&&) (eqbt t1 t2) (lstruct ts3 ts4))
      in lstruct
    in
    let fstruct =
      let rec fstruct ts1 ts2 =
        match ts1 with
        | [] -> (match ts2 with
                 | [] -> true
                 | _ :: _ -> false)
        | f0 :: ts3 ->
          let (x1, t1) = f0 in
          (match ts2 with
           | [] -> false
           | f1 :: ts4 ->
             let (x2, t2) = f1 in
             if equiv_dec coq_StringEqDec x1 x2
             then (&&) (eqbt t1 t2) (fstruct ts3 ts4)
             else false)
      in fstruct
    in
    (match _UU03c4_1 with
     | E.TBool -> (match _UU03c4_2 with
                   | E.TBool -> true
                   | _ -> false)
     | E.TBit w1 ->
       (match _UU03c4_2 with
        | E.TBit w2 -> Pos.eqb w1 w2
        | _ -> false)
     | E.TInt w1 ->
       (match _UU03c4_2 with
        | E.TInt w2 -> Pos.eqb w1 w2
        | _ -> false)
     | E.TError -> (match _UU03c4_2 with
                    | E.TError -> true
                    | _ -> false)
     | E.TMatchKind ->
       (match _UU03c4_2 with
        | E.TMatchKind -> true
        | _ -> false)
     | E.TTuple ts1 ->
       (match _UU03c4_2 with
        | E.TTuple ts2 -> lstruct ts1 ts2
        | _ -> false)
     | E.TStruct ts1 ->
       (match _UU03c4_2 with
        | E.TStruct ts2 -> fstruct ts1 ts2
        | _ -> false)
     | E.THeader ts1 ->
       (match _UU03c4_2 with
        | E.THeader ts2 -> fstruct ts1 ts2
        | _ -> false)
     | E.THeaderStack (ts1, n1) ->
       (match _UU03c4_2 with
        | E.THeaderStack (ts2, n2) -> (&&) (Pos.eqb n1 n2) (fstruct ts1 ts2)
        | _ -> false))

  (** val eqbt_reflect : E.t -> E.t -> reflect **)

  let eqbt_reflect t1 t2 =
    let b = eqbt t1 t2 in if b then ReflectT else ReflectF

  (** val coq_TypeEqDec : E.t coq_EqDec **)

  let coq_TypeEqDec t1 t2 =
    reflect_dec (eqbt t1 t2) (eqbt_reflect t1 t2)
 end
