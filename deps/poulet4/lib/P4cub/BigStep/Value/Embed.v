Require Export Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.Value Poulet4.P4Arith Coq.Strings.String.
Require Poulet4.P4String.
Import P4cub.P4cubNotations Val.ValueNotations.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation VAL := (@ValueBase tags_t bool).

  Variable dummy : tags_t.

  Definition str_of_str := P4String.Build_t _ dummy.
  
  Fixpoint embed (v : Val.v) : VAL :=
    match v with
    | ~{ VBOOL b }~ => ValBaseBool b
    | ~{ w VW n }~  => ValBaseBit $ to_lbool w n
    | ~{ w VS z }~  => ValBaseInt $ to_lbool (Npos w) z
    | ~{ TUPLE vs }~      => ValBaseTuple $ map embed vs
    | ~{ STRUCT { vs } }~ =>
      ValBaseStruct
        $ map (fun '(x,v) => (str_of_str x, embed v)) vs
    | ~{ HDR { vs } VALID:=b }~ =>
      ValBaseHeader
        (map (fun '(x,v) => (str_of_str x, embed v)) vs) b
    | Val.VError (Some err)   => ValBaseError $ str_of_str err
    | ~{ ERROR  None       }~ => ValBaseError $ str_of_str "no error"
    | ~{ MATCHKIND exact   }~ => ValBaseMatchKind $ str_of_str "exact"
    | ~{ MATCHKIND ternary }~ => ValBaseMatchKind $ str_of_str "ternary"
    | ~{ MATCHKIND lpm     }~ => ValBaseMatchKind $ str_of_str "lpm"
    | ~{ STACK hs:_ [n] NEXT:=i }~ =>
      ValBaseStack
        (map
           (fun '(b,vs) =>
              ValBaseHeader
                (map (fun '(x,v) => (str_of_str x, embed v)) vs) b) hs)
        (Npos n) (BinInt.Z.to_N i)
    end.
End Embed.
