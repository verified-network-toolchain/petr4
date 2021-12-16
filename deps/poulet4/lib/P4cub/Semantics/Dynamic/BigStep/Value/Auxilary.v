Require Import Coq.NArith.BinNat
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Coq.PArith.BinPos Coq.ZArith.BinInt
        Poulet4.P4cub.Syntax.CubNotations.
Import Val ValueNotations AllCubNotations.

(** Intial/Default value from a type. *)
Fixpoint vdefault (τ : Expr.t) : option v :=
  match τ with
  | {{ error }}      => Some ~{ ERROR None }~
  | {{ matchkind }}  => Some ~{ MATCHKIND exact }~
  | {{ Bool }}       => Some ~{ FALSE }~
  | {{ bit<w> }}     => Some $ VBit w 0%Z
  | {{ int<w> }}     => Some $ VInt w 0%Z
  | {{ tuple ts }}
    => vs <<| sequence $ List.map vdefault ts ;; VTuple vs
  | {{ struct { ts } }}
    => vs <<| sequence $ List.map (fun '(x,t) => v <<| vdefault t ;; (x, v)) ts ;;
      ~{ STRUCT { vs } }~
  | {{ hdr { ts } }}
    => vs <<| sequence $ List.map (fun '(x,t) => v <<| vdefault t ;; (x, v)) ts ;;
      ~{ HDR { vs } VALID:=false }~
  | {{ stack ts[n] }}
    => vs <<| sequence $ List.map (fun '(x,t) => v <<| vdefault t ;; (x, v)) ts ;;
      VHeaderStack ts (repeat (false, vs) (Pos.to_nat n)) 0
  | Expr.TVar _ => None
  end.
(**[]*)

Fixpoint match_pattern (p : Parser.pat) (V : v) : bool :=
  match p, V with
  | [{ ?? }], _ => true
  | [{ (w PW a) &&& (_ PW b) }], ~{ _ VW c }~
    => (Z.land a b =? Z.land c b)%Z
  | [{ (w PW a) .. (_ PW b) }], ~{ _ VW c }~
    => (a <=? c)%Z && (c <=? b)%Z
  | [{ w1 PW n1 }], ~{ w2 VW n2 }~ =>
    (w1 =? w2)%N && (n1 =? n2)%Z
  | [{ w1 PS n1 }], ~{ w2 VS n2 }~ =>
    (w1 =? w2)%positive && (n1 =? n2)%Z
  | [{ PTUP ps }], ~{ TUPLE vs }~ =>
    (fix F ps vs :=
       match ps, vs with
       | [], [] => true
       | p::ps, v::vs => match_pattern p v && F ps vs
       | _, _ => false
       end) ps vs
  | _,_ => false
  end.
(**[]*)

Fixpoint approx_type (V : v) : Expr.t :=
  match V with
  | ~{ VBOOL _ }~ => {{ Bool }}
  | ~{ w VW _ }~ => {{ bit<w> }}
  | ~{ w VS _ }~ => {{ int<w> }}
  | ~{ ERROR _ }~ => {{ error }}
  | ~{ MATCHKIND _ }~ => {{ matchkind }}
  | ~{ TUPLE vs }~ => Expr.TTuple $ List.map approx_type vs
  | ~{ STRUCT { vs } }~
    => Expr.TStruct $ F.map approx_type vs
  | ~{ HDR { vs } VALID:=_ }~
    => Expr.THeader $ F.map approx_type vs
  | ~{ STACK hs:ts NEXT:=_ }~ => Expr.THeaderStack ts (Pos.of_nat (length hs))
  end.
(**[]*)
                      
Section Util.
  Context {tags_t : Type}.

  Variable i : tags_t.
  
  Fixpoint expr_of_value (V : v) : Expr.e tags_t :=
    match V with
    | ~{ VBOOL b }~ => <{ BOOL b @ i }>
    | ~{ w VW n }~ => <{ w W n @ i }>
    | ~{ w VS z }~ => <{ w S z @ i }>
    | ~{ ERROR err }~ => <{ Error err @ i }>
    | ~{ MATCHKIND mk }~ => <{ Matchkind mk @ i }>
    | ~{ TUPLE vs }~
      => Expr.ETuple (List.map expr_of_value vs) i
    | ~{ STRUCT { vs } }~
      => Expr.EStruct (F.map expr_of_value vs) i
    | ~{ HDR { vs } VALID:=b }~
      => Expr.EHeader (F.map expr_of_value vs) <{ BOOL b @ i }> i
    | ~{ STACK hs:ts NEXT:=ni }~
      => Expr.EHeaderStack
          ts
          (List.map
             (fun '(b,vs) =>
                Expr.EHeader
                  (F.map expr_of_value vs) <{ BOOL b @ i }> i) hs) ni i
    end.
End Util.
