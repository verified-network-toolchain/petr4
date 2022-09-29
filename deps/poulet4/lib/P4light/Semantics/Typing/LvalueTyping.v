Require Export Poulet4.P4light.Semantics.Typing.ValueTyping Coq.ZArith.BinInt.

(** L-value typing. *)

Section Tags.
  Context {tags_t:Type}.
  Notation typ := (@P4Type tags_t).

  (** Typing analogue to [Semantics.loc_to_sval]. *)
  Definition typ_of_loc_var
             (l: Locator) (g: PathMap.t typ) : option typ :=
    match l with
    | LInstance p => PathMap.get p g
    | LGlobal   _ => None
    end.
End Tags.

Reserved Notation "x '⊢ₗ' lv '\:' t" (at level 80, no associativity).

Inductive lval_typ
          {tags_t: Type} (Γ : PathMap.t (@P4Type tags_t))
  : ValueLvalue -> @P4Type tags_t -> Prop :=
| typ_left_name l τ :
  typ_of_loc_var l Γ = Some τ ->
  Γ ⊢ₗ ValLeftName l \: τ
| typ_left_member lv x τ τ' τs :
  x <> "size"%string ->
  x <> "lastIndex"%string ->
  AList.get (P4String.clear_AList_tags τs) x = Some τ' ->
  member_type τs τ ->
  Γ ⊢ₗ lv \: τ ->
  Γ ⊢ₗ ValLeftMember lv x \: τ'
| typ_left_bit_access lv hi lo w :
  (lo <= hi < w)%N ->
  Γ ⊢ₗ lv \: TypBit w ->
  Γ ⊢ₗ ValLeftBitAccess lv hi lo \: TypBit (hi - lo + 1)%N
| typ_left_array_access lv (z : Z) τ n :
  (0 <= z)%Z ->
  Γ ⊢ₗ lv \: TypArray τ n ->
  Γ ⊢ₗ ValLeftArrayAccess lv z \: τ
where "Γ '⊢ₗ' lv '\:' t" := (lval_typ Γ lv t) : type_scope.
