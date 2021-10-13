Require Export Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.Value Poulet4.P4Arith Coq.Strings.String
        Poulet4.P4cub.BigStep.Value.IndPrincip
        Poulet4.Utils.
Require Poulet4.P4String.
Import P4cub.P4cubNotations Val.ValueNotations.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation VAL := (@ValueBase tags_t bool).

  Inductive Embed : Val.v -> VAL -> Prop :=
  | Embed_bool b :
      Embed ~{ VBOOL b }~ (ValBaseBool b)
  | Embed_bit w n :
      Embed ~{ w VW n }~ (ValBaseBit (to_lbool w n))
  | Embed_int w z :
      Embed ~{ w VS z }~ (ValBaseInt (to_lbool (Npos w) z))
  | Embed_tuple vs vs' :
      Forall2 Embed vs vs' ->
      Embed ~{ TUPLE vs }~ (ValBaseTuple vs')
  | Embed_struct vs vs' :
      Forall2 (fun xv xv' =>
                 fst xv = P4String.str (fst xv') /\
                 Embed (snd xv) (snd xv')) vs vs' ->
      Embed ~{ STRUCT { vs } }~ (ValBaseStruct vs')
  | Embed_header vs vs' b :
      Forall2 (fun xv xv' =>
                 fst xv = P4String.str (fst xv') /\
                 Embed (snd xv) (snd xv')) vs vs' ->
      Embed ~{ HDR { vs } VALID:=b }~ (ValBaseHeader vs' b)
  | Embed_error eo er :
      match eo with
      | Some err => err 
      | None     => "no error"%string
      end = P4String.str er ->
      Embed ~{ ERROR eo }~ (ValBaseError er)
  | Embed_matchkind mk mk' :
      match mk with
      | E.MKExact   => "exact"%string
      | E.MKTernary => "ternary"%string
      | E.MKLpm     => "lpm"%string
      end = P4String.str mk' ->
      Embed ~{ MATCHKIND mk }~ (ValBaseMatchKind mk')
  | Embed_stack hs ts n i hs' :
      Forall2
        (fun v v' =>
           Embed (Val.VHeader (snd v) (fst v)) v')
        hs hs' ->
      Embed
        ~{ STACK hs:ts [n] NEXT:=i }~
        (ValBaseStack hs' (Npos n) (BinInt.Z.to_N i)).
  
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

  Local Hint Constructors Embed : core.
  
  Lemma embed_Embed : forall v, Embed v (embed v).
  Proof.
    intro v; induction v using custom_value_ind;
      unravel in *; auto.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall; auto.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall.
      unfold F.predfs_data, F.predf_data in H.
      unravel in *.
      rewrite Forall_forall in H.
      rewrite Forall_forall.
      intros [x v] Hin; unravel in *.
      firstorder.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall.
      unfold F.predfs_data, F.predf_data in H.
      unravel in *.
      rewrite Forall_forall in H.
      rewrite Forall_forall.
      intros [x v] Hin; unravel in *.
      firstorder.
    - destruct err; auto.
    - destruct mk; auto.
    - constructor.
      rewrite <- Forall2_map_r, Forall2_Forall.
      unfold F.predfs_data, F.predf_data in H.
      unravel in *.
      rewrite Forall_forall in H.
      rewrite Forall_forall.
      intros [b h] Hin; unravel in *.
      constructor.
      rewrite <- Forall2_map_r, Forall2_Forall.
      apply H in Hin; auto; simpl in *.
      rewrite Forall_forall in Hin.
      rewrite Forall_forall.
      intros [x v] Hin'; unravel in *.
      firstorder.
  Qed.
End Embed.
