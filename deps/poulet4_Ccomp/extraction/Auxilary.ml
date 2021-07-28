open AST0
open BinNums
open BinPos
open Datatypes
open Equality
open EquivDec
open EquivUtil
open List0
open Nat

module P = P4cub

module E = P.Expr

module SynDefs =
 struct
  (** val width_of_typ : E.t -> nat **)

  let rec width_of_typ = function
  | E.TBool -> S O
  | E.TBit w -> Pos.to_nat w
  | E.TInt w -> Pos.to_nat w
  | E.TTuple ts -> fold_left (fun acc t0 -> add acc (width_of_typ t0)) ts O
  | E.TStruct fs0 -> F.fold (fun _ t0 acc -> add acc (width_of_typ t0)) fs0 O
  | E.THeader fs0 -> F.fold (fun _ t0 acc -> add acc (width_of_typ t0)) fs0 O
  | E.THeaderStack (fs0, s0) ->
    mul (F.fold (fun _ t0 acc -> add acc (width_of_typ t0)) fs0 O)
      (Pos.to_nat s0)
  | _ -> O
 end
