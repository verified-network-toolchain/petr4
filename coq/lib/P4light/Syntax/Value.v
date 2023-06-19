From Coq Require Import ZArith.BinInt Lists.List Strings.String.
Import ListNotations.
From Poulet4 Require Import Utils.AList P4light.Syntax.Syntax Utils.ForallMap.
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

  Fixpoint list_bit_eqb {bit: Type} (bit_eqb: bit -> bit -> bool)
                        (l1 l2: list bit): bool :=
    match l1, l2 with
    | [], []           => true
    | t1 :: ts1, t2 :: ts2 => (bit_eqb t1 t2 && list_bit_eqb bit_eqb ts1 ts2)%bool
    | _, _             => false
    end.

  Fixpoint val_eqb {bit: Type} (bit_eqb: bit -> bit -> bool)
    (v1 v2: @ValueBase bit): bool :=
    let fix list_val_eqb (l1 l2 : list (@ValueBase bit)) : bool :=
    match l1, l2 with
    | [], []           => true
    | t1 :: ts1, t2 :: ts2 => (val_eqb bit_eqb t1 t2 && list_val_eqb ts1 ts2)%bool
    | _, _             => false
    end in
    let fix list_field_eqb (l1 l2 : StringAList (@ValueBase bit)) : bool :=
    match l1, l2 with
    | [], []           => true
    | (k1, t1) :: ts1, (k2, t2) :: ts2 =>
        (String.eqb k1 k2 && val_eqb bit_eqb t1 t2 && list_field_eqb ts1 ts2)%bool
    | _, _             => false
    end in
    match v1, v2 with
    | ValBaseNull, ValBaseNull => true
    | ValBaseBool b1, ValBaseBool b2 => bit_eqb b1 b2
    | ValBaseInteger z1, ValBaseInteger z2 => Z.eqb z1 z2
    | ValBaseBit l1, ValBaseBit l2 => list_bit_eqb bit_eqb l1 l2
    | ValBaseInt l1, ValBaseInt l2 => list_bit_eqb bit_eqb l1 l2
    | ValBaseVarbit m1 l1, ValBaseVarbit m2 l2 =>
        (BinNat.N.eqb m1 m2 && list_bit_eqb bit_eqb l1 l2)%bool
    | ValBaseString s1, ValBaseString s2 => String.eqb s1 s2
    | ValBaseTuple l1, ValBaseTuple l2 => list_val_eqb l1 l2
    | ValBaseError s1, ValBaseError s2 => String.eqb s1 s2
    | ValBaseMatchKind s1, ValBaseMatchKind s2 => String.eqb s1 s2
    | ValBaseStruct f1, ValBaseStruct f2 => list_field_eqb f1 f2
    | ValBaseHeader f1 b1, ValBaseHeader f2 b2 =>
        list_field_eqb f1 f2 && bit_eqb b1 b2
    | ValBaseUnion f1, ValBaseUnion f2 => list_field_eqb f1 f2
    | ValBaseStack s1 n1, ValBaseStack s2 n2 =>
        list_val_eqb s1 s2 && BinNat.N.eqb n1 n2
    | ValBaseEnumField t1 e1, ValBaseEnumField t2 e2 =>
        String.eqb t1 t2 && String.eqb e1 e2
    | ValBaseSenumField t1 l1, ValBaseSenumField t2 l2 =>
        String.eqb t1 t2 && val_eqb bit_eqb l1 l2
    | _, _ => false
    end.

  Inductive ValueLvalue :=
  | ValLeftName (loc: Syntax.Locator)
  | ValLeftMember (expr: ValueLvalue) (name: string)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: N) (lsb: N)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: Z).

  Inductive ValueSet:=
  | ValSetSingleton (value: (@ValueBase bool))
  | ValSetUniversal
  | ValSetMask (value: (@ValueBase bool)) (mask: (@ValueBase bool))
  | ValSetRange (lo: (@ValueBase bool)) (hi: (@ValueBase bool))
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (nbits: N) (value: (@ValueBase bool))
  | ValSetValueSet (size: N) (members: list (list ValueSet)) (sets: list ValueSet).

  Definition ValueLoc := string.

  Context {tags_t : Type}.

  Inductive ValueTable :=
  | MkValTable (name: string) (keys: list (@Syntax.TableKey tags_t))
               (actions: list (@Syntax.TableActionRef tags_t))
               (default_action: @Syntax.TableActionRef tags_t)
               (const_entries: list (@Syntax.TableEntry tags_t)).


  Definition Env_env binding := list (StringAList binding).

  Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env (@Typed.P4Type tags_t)) (namespace: string).

  Inductive ValueFunctionImplementation :=
  | ValFuncImplUser (scope: Env_EvalEnv) (body: (@Syntax.Block tags_t))
  | ValFuncImplExtern (name: string) (caller: option (ValueLoc * string))
  | ValFuncImplBuiltin (name: string) (caller: ValueLvalue).

  Inductive ValueObject :=
  | ValObjParser (scope: Env_EvalEnv)
                 (constructor_params: list (@Typed.P4Parameter tags_t))
                 (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                 (states: list (@Syntax.ParserState tags_t))
  | ValObjTable (_: ValueTable)
  | ValObjControl (scope: Env_EvalEnv)
                  (constructor_params: list (@Typed.P4Parameter tags_t))
                  (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                  (apply: (@Syntax.Block tags_t))
  | ValObjPackage (args: StringAList ValueLoc)
  | ValObjRuntime (loc: ValueLoc) (obj_name: string)
  | ValObjFun (params: list (@Typed.P4Parameter tags_t)) (impl: ValueFunctionImplementation)
  | ValObjAction (scope: Env_EvalEnv) (params: list (@Typed.P4Parameter tags_t))
                 (body: (@Syntax.Block tags_t))
  | ValObjPacket (bits: list bool).

  Inductive ValueConstructor :=
  | ValConsParser (scope: Env_EvalEnv) (constructor_params: list (@Typed.P4Parameter tags_t))
                  (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                  (states: list (@Syntax.ParserState tags_t))
  | ValConsTable (_: ValueTable)
  | ValConsControl (scope: Env_EvalEnv) (constructor_params: list (@Typed.P4Parameter tags_t))
                   (params: list (@Typed.P4Parameter tags_t)) (locals: list (@Syntax.Declaration tags_t))
                   (apply: (@Syntax.Block tags_t))
  | ValConsPackage (params: list (@Typed.P4Parameter tags_t)) (args: StringAList ValueLoc)
  | ValConsExternObj (_: StringAList (list (@Typed.P4Parameter tags_t))).

  Inductive Value (bit : Type) :=
  | ValBase (_: @ValueBase bit)
  | ValObj (_: ValueObject)
  | ValCons (_: ValueConstructor).

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

  Section ValueSetInd.

    Variable P : ValueSet -> Prop.

    Hypothesis HSingleton : forall value, P (ValSetSingleton value).

    Hypothesis HUniversal : P ValSetUniversal.

    Hypothesis HMask : forall value mask, P (ValSetMask value mask).

    Hypothesis HRange : forall lo hi, P (ValSetRange lo hi).

    Hypothesis HProd : forall l, Forall P l -> P (ValSetProd l).

    Hypothesis HLpm : forall nbits value, P (ValSetLpm nbits value).

    Hypothesis HValueSet :
      forall size members sets,
        Forall (Forall P) members -> Forall P sets -> P (ValSetValueSet size members sets).

    Fixpoint custom_ValueSet_ind (v : ValueSet) : P v :=
      let fix list_ind (vs : list ValueSet) : Forall P vs :=
        match vs with
        | v :: vs => Forall_cons _ (custom_ValueSet_ind v) (list_ind vs)
        | [] => Forall_nil _
        end
      in
      let fix nested_list_ind (vs : list (list ValueSet)) : Forall (Forall P) vs :=
        match vs with
        | v :: vs => Forall_cons _ (list_ind v) (nested_list_ind vs)
        | [] => Forall_nil _
        end
      in
      match v with
      | ValSetSingleton value => HSingleton value
      | ValSetUniversal => HUniversal
      | ValSetMask value mask => HMask value mask
      | ValSetRange lo hi => HRange lo hi
      | ValSetProd l => HProd _ (list_ind l)
      | ValSetLpm nbits value => HLpm nbits value
      | ValSetValueSet _ members sets =>
        HValueSet _ _ _ (nested_list_ind members) (list_ind sets)
      end.

  End ValueSetInd.

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

  Inductive signal : Type :=
 | SContinue : signal
 | SReturn : (@ValueBase bool) -> signal
 | SExit
 (* parser's states include accept and reject *)
 | SReject : string -> signal.

  Definition SReturnNull := SReturn ValBaseNull.

End Value.

Lemma list_bit_eqb_refl:
  forall {bit} (bit_eqb: bit -> bit -> bool),
    (forall b, bit_eqb b b = true) ->
    forall v: list bit, list_bit_eqb bit_eqb v v = true.
Proof.
  intros bit bit_eqb H v. induction v as [| v l]; simpl; auto.
  rewrite H, IHl. reflexivity.
Qed.

Lemma val_eqb_refl:
  forall {bit} (bit_eqb: bit -> bit -> bool),
    (forall b, bit_eqb b b = true) ->
    forall v: ValueBase, val_eqb bit_eqb v v = true.
Proof.
  intros bit bit_eqb Hbrefl.
  induction v using custom_ValueBase_ind; simpl;
    rewrite ?Z.eqb_refl, ?list_bit_eqb_refl, ?String.eqb_refl,
    ?BinNat.N.eqb_refl; auto.
  - induction vs; auto. rewrite Forall_cons_iff in H. destruct H as [Hs Hr].
    rewrite Hs, IHvs; easy.
  - induction vs; auto. rewrite Forall_cons_iff in H. destruct H as [Hs Hr].
    destruct a as [k v]. rewrite String.eqb_refl, Hs, IHvs; easy.
  - rewrite Hbrefl, Bool.andb_true_r.
    induction vs; auto. rewrite Forall_cons_iff in H. destruct H as [Hs Hr].
    destruct a as [k v]. rewrite String.eqb_refl, Hs, IHvs; auto.
  - induction vs; auto. rewrite Forall_cons_iff in H. destruct H as [Hs Hr].
    destruct a as [k v]. rewrite String.eqb_refl, Hs, IHvs; easy.
  - rewrite Bool.andb_true_r.
    induction vs; auto. rewrite Forall_cons_iff in H. destruct H as [Hs Hr].
    rewrite Hs, IHvs; easy.
Qed.

Lemma list_bit_eqb_eq:
  forall {bit} (bit_eqb: bit -> bit -> bool),
    (forall b1 b2, bit_eqb b1 b2 = true -> b1 = b2) ->
    forall v1 v2: list bit, list_bit_eqb bit_eqb v1 v2 = true -> v1 = v2.
Proof.
  intros bit bit_eqb Hbrefl v1.
  induction v1 as [|v l]; intros []; intros; simpl in *; try discriminate.
  - reflexivity.
  - rewrite Bool.andb_true_iff in H. destruct H.
    apply Hbrefl in H. apply IHl in H0. subst. reflexivity.
Qed.

Lemma val_eqb_eq:
  forall {bit} (bit_eqb: bit -> bit -> bool),
    (forall b1 b2, bit_eqb b1 b2 = true -> b1 = b2) ->
    forall v1 v2: ValueBase, val_eqb bit_eqb v1 v2 = true -> v1 = v2.
Proof.
  intros bit bit_eqb Hbrefl v1.
  induction v1 using custom_ValueBase_ind;
    intros []; intros; simpl in *; try discriminate;
  repeat match goal with
    | H: String.eqb _ _ = true |- _ => rewrite String.eqb_eq in H; subst
    | H: bit_eqb _ _ = true |- _ => apply Hbrefl in H
    | H: Z.eqb _ _ = true |- _ => rewrite Z.eqb_eq in H
    | H: andb _ _ = true |- _ => rewrite Bool.andb_true_iff in H; destruct H
    | H: BinNat.N.eqb _ _ = true |- _ => rewrite BinNat.N.eqb_eq in H
    | H: list_bit_eqb bit_eqb _ _ = true |- _ => apply list_bit_eqb_eq in H; auto
    | IH: Forall _ ?ts1, H: _ ?ts1 ?ts2 = true
      |- _ ?ts1 = _ ?ts2 =>
        generalize dependent ts2; induction ts1; intros []; intros; try discriminate
    | IH: Forall _ ?ts1, H: _ ?ts1 ?ts2 = true
      |- _ ?ts1 _ = _ ?ts2 _ =>
        generalize dependent ts2; induction ts1; intros []; intros; try discriminate
    | H: (let (_, _) := ?a in false) = true |- _ => destruct a; discriminate
    | H: (let (_, _) := ?a in _) = true |- _ => destruct a
    | H: Forall _ (_ :: _) |- _ => rewrite Forall_cons_iff in H; destruct H
    | H1: Forall ?P ?v, H2: Forall ?P ?v -> _ |- _ => specialize (H2 H1)
    | [H1 : forall v2 : ValueBase, val_eqb bit_eqb ?v v2 = true -> ?v = v2,
         H2: val_eqb bit_eqb ?v _ = true |- _ ] => apply H1 in H2; subst
  end; try (subst; reflexivity).
  - apply IHvs in H1. inversion H1. reflexivity.
  - apply IHvs in H1. inversion H1. reflexivity.
  - apply IHvs in H2. inversion H2. reflexivity.
  - apply IHvs in H1. inversion H1. reflexivity.
  - apply IHvs in H2. inversion H2. reflexivity.
Qed.
