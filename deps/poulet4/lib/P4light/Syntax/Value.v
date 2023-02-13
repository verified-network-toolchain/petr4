From Coq Require Import ZArith.BinInt ZArith.ZArith Lists.List Strings.String.
Import ListNotations.
From Poulet4 Require Import Utils.AList (*P4light.Syntax.Syntax*) Utils.ForallMap.
From Poulet4.P4light.Syntax Require P4String P4Int Typed.

Section Value.

  (* little-endian *)
  Inductive ValueBase {bit : Type} :=
  | ValBaseNull
  | ValBaseBool (_: bit)
  | ValBaseInteger (_: Z)
  | ValBaseBit (value: list bit)
  | ValBaseInt (value: list bit)
  | ValBaseVarbit (max: N) (value: list bit)
  | ValBaseString (_: string)
  | ValBaseTuple (_: list (@ValueBase bit))
  | ValBaseError (_: string)
  | ValBaseMatchKind (_: string)
  | ValBaseStruct (fields: StringAList (@ValueBase bit))
  | ValBaseHeader (fields: StringAList (@ValueBase bit)) (is_valid: bit)
  | ValBaseUnion (fields: StringAList (@ValueBase bit))
  | ValBaseStack (headers: list (@ValueBase bit)) (next: N)
  | ValBaseEnumField (typ_name: string) (enum_name: string)
  | ValBaseSenumField (typ_name: string) (value: (@ValueBase bit)).

  Section ValBaseInd.
    Variable bit : Type.
    Notation V := (@ValueBase bit).
    Variable P : V -> Prop.

    Hypothesis HNull : P ValBaseNull.
    Hypothesis HBool : forall b, P (ValBaseBool b).
    Hypothesis HInteger : forall z, P (ValBaseInteger z).
    Hypothesis HBit : forall n, P (ValBaseBit n).
    Hypothesis HInt : forall z, P (ValBaseInt z).
    Hypothesis HVarbit : forall w n, P (ValBaseVarbit w n).
    Hypothesis HString : forall s, P (ValBaseString s).
    Hypothesis HTuple : forall vs,
        Forall P vs -> P (ValBaseTuple vs).
    Hypothesis HError : forall err, P (ValBaseError err).
    Hypothesis HMatchKind : forall mk, P (ValBaseMatchKind mk).
    Hypothesis HStruct : forall vs,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseStruct vs).
    Hypothesis HHeader : forall vs b,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseHeader vs b).
    Hypothesis HUnion : forall vs,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseUnion vs).
    Hypothesis HStack : forall vs i,
        Forall P vs -> P (ValBaseStack vs i).
    Hypothesis HEnumField : forall t x, P (ValBaseEnumField t x).
    Hypothesis HSenumField : forall t v,
        P v -> P (ValBaseSenumField t v).

    Definition custom_ValueBase_ind :
      forall v : V, P v :=
      fix vind (v : V) : P v :=
        let fix lind (vs : list V) : Forall P vs :=
            match vs with
            | []     => Forall_nil _
            | v :: vs => Forall_cons _ (vind v) (lind vs)
            end in
        let fix alind (vs : AList.AList _ V _) : Forall (fun '(_,v) => P v) vs :=
            match vs with
            | []          => Forall_nil _
            | (_,v) as xv :: vs => Forall_cons xv (vind v) (alind vs)
            end in
        match v with
        | ValBaseNull             => HNull
        | ValBaseBool b           => HBool b
        | ValBaseInteger z        => HInteger z
        | ValBaseBit n            => HBit n
        | ValBaseInt z            => HInt z
        | ValBaseVarbit w n       => HVarbit w n
        | ValBaseString s         => HString s
        | ValBaseTuple vs         => HTuple _ (lind vs)
        | ValBaseError err        => HError err
        | ValBaseMatchKind mk     => HMatchKind mk
        | ValBaseStruct vs        => HStruct _ (alind vs)
        | ValBaseHeader vs b      => HHeader _ b (alind vs)
        | ValBaseUnion vs         => HUnion _ (alind vs)
        | ValBaseStack vs i       => HStack _ i (lind vs)
        | ValBaseEnumField t x    => HEnumField t x
        | ValBaseSenumField t v   => HSenumField t _ (vind v)
        end.
  End ValBaseInd.

  Section ValueBaseFunctor.
    Context {A B : Type}.
    Variable (f : A -> B).

    Fixpoint ValueBaseMap (v : @ValueBase A) : @ValueBase B :=
      match v with
      | ValBaseNull         => ValBaseNull
      | ValBaseInteger z    => ValBaseInteger z
      | ValBaseString s     => ValBaseString s
      | ValBaseError e      => ValBaseError e
      | ValBaseMatchKind mk => ValBaseMatchKind mk
      | ValBaseBool a       => ValBaseBool (f a)
      | ValBaseBit n        => ValBaseBit (map f n)
      | ValBaseInt z        => ValBaseInt (map f z)
      | ValBaseVarbit w n   => ValBaseVarbit w (map f n)
      | ValBaseTuple vs     => ValBaseTuple (map ValueBaseMap vs)
      | ValBaseStruct vs    =>
        ValBaseStruct (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseHeader vs a  =>
        ValBaseHeader (map (fun '(x,v) => (x, ValueBaseMap v)) vs) (f a)
      | ValBaseUnion vs     =>
        ValBaseUnion (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseStack vs i =>
        ValBaseStack (map ValueBaseMap vs) i
      | ValBaseEnumField t x => ValBaseEnumField t x
      | ValBaseSenumField t v => ValBaseSenumField t (ValueBaseMap v)
      end.
  End ValueBaseFunctor.

  Hint Rewrite map_id : core.

  Ltac list_solve :=
    match goal with
    | H: Forall (fun v : ValueBase => ValueBaseMap (fun x => x) v = v) ?vs
      |- map (ValueBaseMap (fun x => x)) ?vs = ?vs =>
      apply map_ext_Forall in H;
      rewrite H, map_id; reflexivity
    end.

  Ltac alist_solve :=
    match goal with
    | H: Forall (fun '(_, _) => _) ?vs
      |- map _ _ = _ =>
      try rewrite Forall_snd in H;
      try apply map_ext_Forall in H;
      try rewrite map_only_snd;
      pose proof split_combine vs as Hcsvs;
      destruct (split vs) as [xs vls] eqn:Hvs;
      specialize (Hcsvs xs vls ltac:(reflexivity));
      try rewrite <- Hcsvs; try f_equal;
      try rewrite <- Hcsvs in H;
      pose proof split_length_l vs as Hsl1;
      pose proof split_length_r vs as Hsl2;
      try rewrite Hvs in Hsl1, Hsl2; simpl in *;
      try rewrite <- Hsl2 in Hsl1;
      try rewrite <- map_map with (f := snd) in H
    end.

  Lemma ValueBaseMap_id : forall (A : Type) (v : @ValueBase A),
      ValueBaseMap (fun x => x) v = v.
  Proof.
    intros A v;
      induction v using custom_ValueBase_ind;
      simpl; autorewrite with core; f_equal; auto;
        try list_solve;
        try (alist_solve;
             rewrite map_snd_combine in H by auto; assumption).
  Qed.

  Lemma ValueBaseMap_compose : forall (T U W : Type) (f : T -> U) (g : U -> W) v,
      ValueBaseMap g (ValueBaseMap f v) =
      ValueBaseMap (fun t => g (f t)) v.
  Proof.
    intros T U W f g v;
      induction v using custom_ValueBase_ind;
      simpl; f_equal; auto; try apply map_map;
        try (rewrite map_map;
             apply map_ext_Forall in H; auto; assumption);
        try alist_solve;
        try (rewrite <- map_map with (g := ValueBaseMap g) in H;
             rewrite <- map_map with (g := ValueBaseMap f) in H;
             rewrite map_snd_combine in H by auto;
             repeat rewrite map_only_snd;
             rewrite combine_split by auto;
             assert (Hsl : length xs = length (map (ValueBaseMap f) vls))
               by (rewrite map_length; assumption);
             rewrite combine_split by auto;
             f_equal; rewrite H; reflexivity).
  Qed.
End Value.

Fixpoint width_of_val {bit : Type} (v: @ValueBase bit) : N :=
  let fix fields_width (fields: StringAList ValueBase) : N :=
      match fields with
      | nil => N.of_nat O
      | (id, v) :: rest => (width_of_val v + fields_width rest)%N
      end in
  match v with
  | ValBaseNull => N.of_nat O
  | ValBaseBool _ => 1
  | ValBaseBit bits
  | ValBaseInt bits
  | ValBaseVarbit _ bits => Z.to_N (Zlength bits)
  | ValBaseTuple vs => List.fold_right N.add (0)%N (List.map width_of_val vs)
  | ValBaseStruct fields
  | ValBaseHeader fields _ => fields_width fields
  | ValBaseSenumField _ v => width_of_val v
  | _ => N.of_nat O
  end.
