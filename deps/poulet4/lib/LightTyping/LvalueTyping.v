Require Export Poulet4.LightTyping.ValueTyping Coq.ZArith.BinInt.

(** L-value typing. *)

Section Tags.
  Context {tags_t:Type}.
  Notation typ := (@P4Type tags_t).
  Notation lvalue := (@ValueLvalue tags_t).
  
  Definition typ_of_lv '(MkValueLvalue _ t : lvalue) : typ := t.

  (** Typing analogue to [Semantics.loc_to_sval]. *)
  Definition typ_of_loc_var
             (l: Locator) (g: PathMap.t typ) : option typ :=
    match l with
    | LInstance p => PathMap.get p g
    | LGlobal   _ => None
    end.
End Tags.

Reserved Notation "x '⊢ₗ' lv" (at level 80, no associativity).

Inductive lval_typ
          {tags_t : Type}
          (Δ : list String.string) (Γ : PathMap.t (@P4Type tags_t))
  : @ValueLvalue tags_t -> Prop :=
| typ_left_name x l τ :
    typ_of_loc_var l Γ = Some τ ->
    Δ ⊢ok τ ->
    (Δ,Γ) ⊢ₗ MkValueLvalue (ValLeftName x l) τ
| typ_left_member lv x τ τs :
    AList.get (P4String.clear_AList_tags τs) x = Some τ ->
    member_type τs (typ_of_lv lv) ->
    Δ ⊢ok τ ->
    (Δ,Γ) ⊢ₗ lv ->
    (Δ,Γ) ⊢ₗ MkValueLvalue (ValLeftMember lv x) τ
| typ_left_bit_access lv hi lo w :
    (lo <= hi < w)%N ->
    typ_of_lv lv = TypBit w ->
    (Δ,Γ) ⊢ₗ lv ->
    (Δ,Γ) ⊢ₗ MkValueLvalue (ValLeftBitAccess lv hi lo) (TypBit (hi - lo + 1)%N)
| typ_left_array_access lv (z : Z) τ n :
    (0 <= z)%Z ->
    typ_of_lv lv = TypArray τ n ->
    (Δ,Γ) ⊢ₗ lv ->
    (Δ,Γ) ⊢ₗ MkValueLvalue (ValLeftArrayAccess lv z) τ
where "x '⊢ₗ' lv"
        := (lval_typ (fst x) (snd x) lv) : type_scope.
