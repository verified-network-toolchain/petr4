Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.

Definition AList
    (K V: Type)
    (R: Relation_Definitions.relation K)
    `{Equivalence K R} :=
  list (K * V)
.

Section AList.
  Context {K V: Type}.
  Context {R: Relation_Definitions.relation K}.
  Context `{H: Equivalence K R}.
  Context {KEqDec: EqDec K R}.

  Definition get (l: AList K V R) (k: K) : option V :=
    let filter := fun '(k', _) =>
      if KEqDec k k' then true else false in
    match List.find filter l with
    | None => None
    | Some (k, v) => Some v
    end
  .

  Fixpoint set (l: AList K V R) (k: K) (v: V) : option (AList K V R) :=
    match l with
    | (k', v') :: l' =>
      if KEqDec k k'
      then Some ((k, v) :: l')
      else match set l' k v with
           | Some l'' => Some ((k, v) :: l')
           | None => None
           end
    | nil =>
      None
    end. 
  
  Theorem k_eqdec: forall k1 k2 : K, {k1 = k2} + {k1 <> k2}. 
  Admitted.

  Definition key_unique (l: AList K V R) : bool :=
    let (ks, vs) := List.split l in
    let ks_nodup := List.nodup k_eqdec ks in
    (Nat.eqb (length ks_nodup) (length ks_nodup)).

End AList.
