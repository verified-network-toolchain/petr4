Require Import Coq.PArith.BinPos.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.

Require Import Poulet4.AList.
Require Poulet4.P4String.
Require Poulet4.P4Int.
Require Export Poulet4.Typed.
Require Export Poulet4.Syntax.
Require Export Poulet4.P4cub.AST.
Import P4cub.P4cubNotations.

(** * P4light -> P4cub *)

Module P := P4cub.
Module F := P.F.
Module E := P.Expr.

Section Metamorphosis.
  Context {tags_t : Type}.

  (** Type Metamorphosis.
      QUESTIONS:
      - Why do controls & functions have both
        constructors in P4Type and their own
        singleton types?
      - What to do about parametric polymorphism?
      - How exactly will types for
        controls, functions, parsers, actions, tables, & externs be
        translated? How will they be mapped to
        p4cub's constructor types?
      - How, when, & where will [TInteger] be casted?
      - Should &, if so, how will
        header unions, strings, enums, varbits, & sets be compiled?
      - Why is there both a record and a struct type? *)
  Fixpoint type_morph (t : P4Type) : option E.t :=
    let fix lrec (ts : list P4Type) : option (list E.t) :=
        match ts with
        | []     => Some []
        | t :: ts => t <- type_morph t ;;
                   ts <- lrec ts ;;
                   Some (t :: ts)
        end in
    let fix frec (fs : P4String.AList tags_t P4Type) : option (F.fs string E.t) :=
        match fs with
        | []         => Some []
        | (x,t) :: fs => t <- type_morph t ;;
                       fs <- frec fs ;;
                       Some ((P4String.str x, t) :: fs)
        end in
    match t with
    | TypBool => Some {{ Bool }}
    | TypInteger => None (* TODO *)
    | TypString => None (* TODO *)
    | TypInt w => Some # E.TInt # Pos.of_nat w
    | TypBit w => Some # E.TBit # Pos.of_nat w
    | TypVarBit _ => None (* TODO *)
    | TypArray t n =>
      let n := Pos.of_nat n in
      t <- type_morph t ;;
      match t with
      | {{ hdr { ts } }} => Some {{ stack ts[n] }}
      | _ => None
      end
    | TypTuple ts
    | TypList  ts => ts <<| lrec ts ;; {{ tuple ts }}
    | TypRecord fs
    | TypStruct fs => fs <<| frec fs ;; {{ rec { fs } }}
    | TypSet _ => None (* TODO *)
    | TypError => Some {{ error }}
    | TypMatchKind => Some {{ matchkind }}
    | TypVoid => None (* TODO *)
    | TypHeader fs => fs <<| frec fs ;; {{ hdr { fs } }}
    | TypHeaderUnion _ => None (* TODO *)
    | TypEnum _ _ _ => None (* TODO *)
    | TypTypeName _ => None (* TODO *)
    | TypNewType _ t => type_morph t
    | TypControl _ => None (* TODO *)
    | TypParser _  => None (* TODO *)
    | TypExtern _  => None (* TODO *)
    | TypFunction _ => None (* TODO *)
    | TypAction _ _ => None (* TODO *)
    | TypTable _ => None (* TODO *)
    | TypPackage _ _ _ => None (* TODO *)
    | TypSpecializedType _ _ => None (* TODO, type subsitution? *)
    | TypConstructor _ _ _ _ => None (* TODO, type subsitution? *)
    end.
  (**[]*)

  (** Unary Operations *)
  Definition uop_morph (op : OpUni) : E.uop :=
    match op with
    | Not => E.Not
    | BitNot => E.BitNot
    | UMinus => E.UMinus
    end.
  (**[]*)

  (** Binary Operations. *)
  Definition bop_morph (op : OpBin) : option E.bop :=
    match op with
    | Plus => Some E.Plus
    | PlusSat => Some E.PlusSat
    | Minus => Some E.Minus
    | MinusSat => Some E.MinusSat
    | Mul => Some E.Times
    | Div => None
    | Mod => None
    | Shl => Some E.Shl
    | Shr => Some E.Shr
    | Le => Some E.Le
    | Ge => Some E.Ge
    | Lt => Some E.Lt
    | Gt => Some E.Gt
    | Eq => Some E.Eq
    | NotEq => Some E.NotEq
    | BitAnd => Some E.BitAnd
    | BitXor => Some E.BitXor
    | BitOr => Some E.BitOr
    | PlusPlus => Some E.PlusPlus
    | And => Some E.And
    | Or => Some E.Or
    end.
  (**[]*)

  (** Expression Metamorphosis.
      Questions:
      1. How to translate expressions for:
         - integers?
         - strings?
         - type members [ExpTypemember]?
         - ternary expressions?
         - function calls?
         - nameless instantiations?
         - don't care expressions?
         - masks?
         - ranges?
      2. Is [P4Name.t] now redundant by [Locator]?
      3. How to translate [Locator]s?
      4. Should p4cub's header stack accesses
         be restricted to compile-time-known indices?
         From 8.17 "Operations on header stacks",
         "Some implementations may impose the constraint that the
          index expression evaluates to a compile-time known value.
          A P4 compiler must give an error if an index value that is
          a compile-time constant is out of range".
          Otherwise progress needs more assumptions.
      5. Why is [N] still used in [Syntax.v]?
         Didn't we decide it was undesirable to
         use both [N] and [Z]? *)
  Fixpoint expr_morph (e : Expression) : option (E.e tags_t) :=
    let fix lrec (es : list Expression) : option (list (E.e tags_t)) :=
        match es with
        | []     => Some []
        | e :: es => e <- expr_morph e ;;
                   es <<| lrec es ;; e :: es
        end in
    let fix frec (fs : list KeyValue) : option (F.fs string (E.t * E.e tags_t)) :=
        match fs with
        | [] => Some []
        | (MkKeyValue _ x ((MkExpression _ _ t _) as e))
            :: fs => t <- type_morph t ;;
                   e <- expr_morph e ;;
                   fs <<| frec fs ;;
                   (P4String.str x, (t, e)) :: fs
        end in
    match e with
    | MkExpression i (ExpBool b) _ _ => Some <{ BOOL b @ i }>
    | MkExpression i (ExpInt n)  _ _
      => let z := P4Int.value n in
        wsigned <- P4Int.width_signed n ;;
        match wsigned with
        | (w, false) => let w := Pos.of_nat w in Some <{ w W z @ i }>
        | (w, true)  => let w := Pos.of_nat w in Some <{ w S z @ i }>
        end
    | MkExpression i (ExpName (BareName x) _) t _
      => t <<| type_morph t ;;
        E.EVar t (P4String.str x) i
    | MkExpression i (ExpArrayAccess e1 e2) _ _
      => e1 <- expr_morph e1 ;;
        e2 <- expr_morph e2 ;;
        match e2 with
        | <{ _ W idx @ _ }> => Some <{ Access e1[idx] @ i }>
        | _ => None (* TODO *)
        end
    | MkExpression i (ExpBitStringAccess e lo hi) t _
      => let lo := Pos.pred # N.succ_pos lo in
        let hi := Pos.pred # N.succ_pos hi in
        t <- type_morph t ;;
        e <<| expr_morph e ;; <{ Slice e:t [hi:lo] @ i }>
    | MkExpression i (ExpList es) _ _
      => es <<| lrec es ;; <{ tup es @ i }>
    | MkExpression i (ExpRecord fs) _ _
      => fs <<| frec fs ;; <{ rec { fs } @ i }>
    | MkExpression i (ExpUnaryOp op e) t _
      => t <- type_morph t ;;
        e <<| expr_morph e ;;
        E.EUop (uop_morph op) t e i
    | MkExpression
        i
        (ExpBinaryOp
           op
           ((MkExpression _ _ t1 _) as e1, (MkExpression _ _ t2 _) as e2))
        _ _ => op <- bop_morph op ;;
              t1 <- type_morph t1 ;;
              t2 <- type_morph t2 ;;
              e1 <- expr_morph e1 ;;
              e2 <<| expr_morph e2 ;; <{ BOP e1:t1 op e2:t2 @ i }>
    | MkExpression i (ExpCast t e) _ _
      => t <- type_morph t ;;
        e <<| expr_morph e ;; <{ Cast e:t @ i }>
    | MkExpression i (ExpErrorMember err) _ _
      => Some # E.EError (Some # P4String.str err) i
    | _ => None
    end.
  (**[]*)
End Metamorphosis.
