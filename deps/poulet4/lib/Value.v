Require Import Coq.ZArith.BinInt Coq.Lists.List Poulet4.Utils.
Import ListNotations.
Require Poulet4.P4String Poulet4.P4Int Poulet4.Syntax Poulet4.Typed.

Section Value.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  (* little-endian *)
  Inductive ValueBase {bit : Type} :=
  | ValBaseNull
  | ValBaseBool (_: bit)
  | ValBaseInteger (_: Z)
  | ValBaseBit (value: list bit)
  | ValBaseInt (value: list bit)
  | ValBaseVarbit (max: N) (value: list bit)
  | ValBaseString (_: P4String)
  | ValBaseTuple (_: list (@ValueBase bit))
  | ValBaseRecord (_: P4String.AList tags_t (@ValueBase bit))
  | ValBaseError (_: P4String)
  | ValBaseMatchKind (_: P4String)
  | ValBaseStruct (fields: P4String.AList tags_t (@ValueBase bit))
  | ValBaseHeader (fields: P4String.AList tags_t (@ValueBase bit)) (is_valid: bit)
  | ValBaseUnion (fields: P4String.AList tags_t (@ValueBase bit))
  | ValBaseStack (headers: list (@ValueBase bit)) (size: N) (next: N)
  | ValBaseEnumField (typ_name: P4String) (enum_name: P4String)
  | ValBaseSenumField (typ_name: P4String) (enum_name: P4String) (value: (@ValueBase bit))
  (*| ValBaseSenum (_: P4String.AList tags_t (@ValueBase bit))*).

  Inductive ValueSet:=
  | ValSetSingleton (value: (@ValueBase bool))
  | ValSetUniversal
  | ValSetMask (value: (@ValueBase bool)) (mask: (@ValueBase bool))
  | ValSetRange (lo: (@ValueBase bool)) (hi: (@ValueBase bool))
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (nbits: N) (value: (@ValueBase bool))
  | ValSetValueSet (size: N) (members: list (list (@Syntax.Match tags_t))) (sets: list ValueSet).

  Definition ValueLoc := P4String.

  Inductive ValueTable :=
  | MkValTable (name: P4String) (keys: list (@Syntax.TableKey tags_t))
               (actions: list (@Syntax.TableActionRef tags_t))
               (default_action: @Syntax.TableActionRef tags_t)
               (const_entries: list (@Syntax.TableEntry tags_t)).


  Definition Env_env binding := list (P4String.AList tags_t binding).

  Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env (@Typed.P4Type tags_t)) (namespace: P4String).
  Inductive ValuePreLvalue :=
  | ValLeftName (name: @Typed.name tags_t) (loc: (@Syntax.Locator tags_t))
  | ValLeftMember (expr: ValueLvalue) (name: P4String)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: N) (lsb: N)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: N)
  with ValueLvalue :=
  | MkValueLvalue (lvalue: ValuePreLvalue) (typ: @Typed.P4Type tags_t).

  Inductive ValueFunctionImplementation :=
  | ValFuncImplUser (scope: Env_EvalEnv) (body: (@Syntax.Block tags_t))
  | ValFuncImplExtern (name: P4String) (caller: option (ValueLoc * P4String))
  | ValFuncImplBuiltin (name: P4String) (caller: ValueLvalue).

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
  | ValObjPackage (args: P4String.AList tags_t ValueLoc)
  | ValObjRuntime (loc: ValueLoc) (obj_name: P4String)
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
  | ValConsPackage (params: list (@Typed.P4Parameter tags_t)) (args: P4String.AList tags_t ValueLoc)
  | ValConsExternObj (_: P4String.AList tags_t (list (@Typed.P4Parameter tags_t))).

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
    Hypothesis HRecord : forall vs,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseRecord vs).
    Hypothesis HError : forall err, P (ValBaseError err).
    Hypothesis HMatchKind : forall mk, P (ValBaseMatchKind mk).
    Hypothesis HStruct : forall vs,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseStruct vs).
    Hypothesis HHeader : forall vs b,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseHeader vs b).
    Hypothesis HUnion : forall vs,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseUnion vs).
    Hypothesis HStack : forall vs n i,
        Forall P vs -> P (ValBaseStack vs n i).
    Hypothesis HEnumField : forall t x, P (ValBaseEnumField t x).
    Hypothesis HSenumField : forall t x v,
        P v -> P (ValBaseSenumField t x v).
    (*Hypothesis HSenum : forall vs,
        Forall (fun '(_,v) => P v) vs -> P (ValBaseSenum vs).*)
    
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
        | ValBaseRecord vs        => HRecord _ (alind vs)
        | ValBaseError err        => HError err
        | ValBaseMatchKind mk     => HMatchKind mk
        | ValBaseStruct vs        => HStruct _ (alind vs)
        | ValBaseHeader vs b      => HHeader _ b (alind vs)
        | ValBaseUnion vs         => HUnion _ (alind vs)
        | ValBaseStack vs n i     => HStack _ n i (lind vs)
        | ValBaseEnumField t x    => HEnumField t x
        | ValBaseSenumField t x v => HSenumField t x _ (vind v)
        (*| ValBaseSenum vs         => HSenum _ (alind vs)*)
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
      | ValBaseRecord vs    =>
        ValBaseRecord (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseStruct vs    =>
        ValBaseStruct (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseHeader vs a  =>
        ValBaseHeader (map (fun '(x,v) => (x, ValueBaseMap v)) vs) (f a)
      | ValBaseUnion vs     =>
        ValBaseUnion (map (fun '(x,v) => (x, ValueBaseMap v)) vs)
      | ValBaseStack vs n i =>
        ValBaseStack (map ValueBaseMap vs) n i
      | ValBaseEnumField t x => ValBaseEnumField t x
      | ValBaseSenumField t x v => ValBaseSenumField t x (ValueBaseMap v)
      (*| ValBaseSenum vs =>
        ValBaseSenum (map (fun '(x,v) => (x, ValueBaseMap v)) vs)*)
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
