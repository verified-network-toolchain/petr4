Require Export Coq.Strings.String
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4light.Syntax.Value
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        Poulet4.Utils.ForallMap
        Poulet4.Utils.Utils Poulet4.Utils.P4Arith.
Require Poulet4.P4light.Syntax.P4String.
Require Import Poulet4.P4cub.Syntax.CubNotations.
Import AllCubNotations Val.ValueNotations.
Local Open Scope string_scope.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Notation VAL := (@ValueBase bool).

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
                 fst xv = fst xv' /\
                 Embed (snd xv) (snd xv')) vs vs' ->
      Embed ~{ STRUCT { vs } }~ (ValBaseStruct vs')
  | Embed_header vs vs' b :
      Forall2 (fun xv xv' =>
                 fst xv = fst xv' /\
                 Embed (snd xv) (snd xv')) vs vs' ->
      Embed ~{ HDR { vs } VALID:=b }~ (ValBaseHeader vs' b)
  | Embed_error eo er :
      match eo with
      | Some err => err 
      | None     => "no error"%string
      end = er ->
      Embed ~{ ERROR eo }~ (ValBaseError er)
  | Embed_stack hs ts i hs' :
      Forall2
        (fun v v' =>
           Embed (Val.VHeader (snd v) (fst v)) v')
        hs hs' ->
      Embed
        ~{ STACK hs:ts NEXT:=i }~
        (ValBaseStack hs' (BinInt.Z.to_N i)).

  Fixpoint embed (v : Val.v) : VAL :=
    match v with
    | ~{ VBOOL b }~ => ValBaseBool b
    | ~{ w VW n }~  => ValBaseBit $ to_lbool w n
    | ~{ w VS z }~  => ValBaseInt $ to_lbool (Npos w) z
    | ~{ TUPLE vs }~      => ValBaseTuple $ map embed vs
    | ~{ STRUCT { vs } }~ =>
      ValBaseStruct
        $ map (fun '(x,v) => (x, embed v)) vs
    | ~{ HDR { vs } VALID:=b }~ =>
      ValBaseHeader
        (map (fun '(x,v) => (x, embed v)) vs) b
    | Val.VError (Some err)   => ValBaseError $ err
    | ~{ ERROR  None       }~ => ValBaseError $ "no error"
    | ~{ STACK hs:_ NEXT:=i }~ =>
      ValBaseStack
        (map
           (fun '(b,vs) =>
              ValBaseHeader
                (map (fun '(x,v) => (x, embed v)) vs) b) hs)
        (BinInt.Z.to_N i)
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
