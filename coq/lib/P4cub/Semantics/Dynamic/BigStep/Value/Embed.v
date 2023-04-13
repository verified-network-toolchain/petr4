Require Export Coq.Strings.String
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4light.Syntax.Value
        Poulet4.P4light.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
        Poulet4.Utils.ForallMap
        Poulet4.Utils.Utils Poulet4.Utils.P4Arith
        Poulet4.Monads.Monad.
Require Poulet4.P4light.Syntax.P4String.
Require Import Poulet4.P4cub.Syntax.CubNotations.
Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat PeanoNat.
Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.Utils.AListUtil.
Local Open Scope string_scope.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Context {tags_t: Type}. 
  Context {dummy_tags: tags_t}. 
  Context {string_list: list string}.
  Notation VAL := (@ValueBase bool).
  Notation EXP := (@Expression tags_t).
  Notation C_P4Type := Typ.t. 
  Notation P_P4Type := (@P4Type tags_t). 

  Definition emb_string (s : string) : P4String.t tags_t := 
  {| P4String.str := s; P4String.tags := dummy_tags |}. 

  Fixpoint string_to_int (s: string) (index : nat) (s_l: list string): option nat := 
    match s_l with 
    | [] => None
    | h::t => 
      if h == s then Some index 
      else (string_to_int s (index+1) t)
    end. 

  Definition get_int (o : option nat) : nat := 
    match o with 
    | None => 0
    | Some s => s
    end.

  Fixpoint string_of_index (n : nat) : string := 
    match n with 
    | 0%nat => "0"
    | S n => "0" ++ string_of_index (n)
    end. 
  
  Fixpoint make_assoc_list {A : Type} (index : nat) (l : list A) : list (string * A) := 
  match l with 
    | [] => []
    | h::t => ((string_of_index index), h) :: make_assoc_list (S index) t
  end.

  Fixpoint keys_valid (index : nat) (keys : list string) : bool :=
    match keys with
    | [] => true
    | k :: keys => (string_of_index index =? k) && keys_valid (S index) keys
    end.

  Definition values_of_fields {A : Type} (index : nat) (fields : list (string * A)) : option (list A) :=
    let (keys, values) := List.split fields in
    guard (keys_valid index keys) ;;
    mret values.

  Lemma id_fields :
    forall (A : Type) index (values : list A) fields,
      values_of_fields index fields = Some values -> make_assoc_list index values = fields.
  Proof.
    intros. generalize dependent index. generalize dependent values.
    induction fields; intros.
    - cbn in *. some_inv. reflexivity.
    - unravel in *. destruct a. unfold values_of_fields in *. unravel in *.
      destruct (split fields). destruct (keys_valid index (s :: l)) eqn:Evalid; try discriminate.
      cbn in *. apply andb_prop in Evalid as [? ?]. rewrite String.eqb_eq in H0.
      subst. some_inv. cbn. f_equal. auto.
      apply IHfields. rewrite H1. reflexivity.
  Qed.

  Lemma values_of_fields_map_snd :
    forall (A : Type) index (values : list A) fields,
      values_of_fields index fields = Some values -> values = map snd fields.
  Proof.
    unfold values_of_fields. intros.
    unravel in *. rewrite split_map in H.
    match_some_inv. some_inv. reflexivity.
  Qed.

  Lemma map_snd_make_assoc_list_idem : forall (A : Type) (l : list A) i,
      map snd (make_assoc_list i l) = l.
  Proof.
    intros A l; induction l as [| a l ih]; intro i;
      cbn in *; f_equal; auto.
  Qed.

  Fixpoint make_list_from_assoc_list {A : Type} (l : list (string * A)) : list A := 
  match l with 
    | [] => []
    | (_, h) ::t => h :: make_list_from_assoc_list t
  end.

  Inductive P4Cub_to_P4Light : C_P4Type -> P_P4Type -> Prop := 
  | TBool : P4Cub_to_P4Light Typ.Bool TypBool      
  | TBit (width : N) : P4Cub_to_P4Light (Typ.Bit width) (TypBit width)
  | TInt (width : positive) : P4Cub_to_P4Light (Typ.Int width) (TypInt (Npos width))
  | TError : P4Cub_to_P4Light Typ.Error TypError   
  | TStruct_not_header (types : list Typ.t) (light_types : list P_P4Type) : 
    Forall2 P4Cub_to_P4Light types light_types -> 
    P4Cub_to_P4Light
      (Typ.Struct false types)
      (TypStruct (List.map (prod_map_l emb_string) (make_assoc_list 0 light_types)))
  | TStruct_header (types : list Typ.t) (light_types : list P_P4Type) : 
    Forall2 P4Cub_to_P4Light types light_types -> 
    P4Cub_to_P4Light
      (Typ.Struct true types)
      (TypHeader (List.map (prod_map_l emb_string) (make_assoc_list 0 light_types)))
  | TArray n t t' :
    P4Cub_to_P4Light t t' ->
    P4Cub_to_P4Light
      (Typ.Array n t)
      (TypArray t' n)
  | TVar (type_name : string) :
    (* if (string_to_int type_name 0 string_list) == None
       then P4Cub_to_P4Light Typ.Error TypError
    else  *)
    P4Cub_to_P4Light
      (Typ.Var (get_int (string_to_int type_name 0 string_list)))
      (TypTypeName (emb_string type_name)).

    (* embed *)
  Fixpoint P4Cub_to_P4Light_fun (c : C_P4Type) : P_P4Type:= 
    match c with
    | Typ.Bool => TypBool       
    | Typ.Bit (width) => TypBit width
    | Typ.Int (width) => TypInt (Npos width)
    | Typ.VarBit (width) => TypVarBit width
    | Typ.Error => TypError
    | Typ.Array n t =>
        TypArray (P4Cub_to_P4Light_fun t) n
    | Typ.Struct true types =>
        TypStruct
          (List.map
             (prod_map_l emb_string)
             (make_assoc_list 0 (List.map P4Cub_to_P4Light_fun types)))
    | Typ.Struct false types =>
        TypHeader
          (List.map
             (prod_map_l emb_string)
             (make_assoc_list 0 (List.map P4Cub_to_P4Light_fun types)))
    | Typ.Var (type_name) => TypTypeName (emb_string (nth type_name string_list ""))
    end.

  (* project *)
  Fixpoint P4Light_to_P4Cub_fun (p : P_P4Type) : result string C_P4Type := 
    match p with
    | TypBool => Result.ok Typ.Bool
    | TypString => Result.error "TypString has no mapping in C_P4Type"
    | TypInteger => Result.error "TypInteger has no mapping in C_P4Type"
    | TypInt (width) => Result.ok (Typ.Int (SyntaxUtil.pos_of_N width))
    | TypBit (width) => Result.ok (Typ.Bit (width))
    | TypVarBit (width) => Result.error "TypVarBit has no mapping in C_P4Type"
    | TypArray typ size =>
        P4Light_to_P4Cub_fun typ >>| Typ.Array size
    | TypTuple types => 
        sequence
          (List.map P4Light_to_P4Cub_fun types)
          >>| Typ.Struct false
    | TypList (types) => Result.error "TypList has no mapping in C_P4Type"
    | TypRecord (fields) => Result.error "TypRecord has no mapping in C_P4Type"
    | TypSet (elt_type) => Result.error "TypSet has no mapping in C_P4Type"
    | TypError => Result.ok Typ.Error
    | TypMatchKind => Result.error "TypMatchKind has no mapping in C_P4Type"
    | TypVoid => Result.error "TypVoid has no mapping in C_P4Type"
    | TypHeader (fields) => Result.error "Headers to be removed"
    | TypHeaderUnion (fields) => Result.error "TypHeaderUnion to be removed"
    | TypStruct (fields) => Result.error "TypStruct to be removed"
    | TypEnum (name) (typ) (members) => Result.error "TypEnum has no mapping in C_P4Type"
    | TypTypeName (name) => Result.ok (Typ.Var (get_int (string_to_int (P4String.str name) 0 string_list))) 
    | TypNewType (name) (typ) => Result.error "TypNewType has no mapping in C_P4Type"
    | TypControl (c) => Result.error "TypControl has no mapping in C_P4Type"
    | TypParser (c) => Result.error "TypParser has no mapping in C_P4Type"
    | TypExtern (extern_name) => Result.error "TypExtern has no mapping in C_P4Type"
    | TypFunction (_) => Result.error "TypFunction has no mapping in C_P4Type"
    | TypAction (data_params) (ctrl_params) => Result.error "TypAction has no mapping in C_P4Type"
    | TypTable (result_typ_name) => Result.error "TypTable has no mapping in C_P4Type"
    | TypPackage (type_params) (wildcard_params) (parameters) => Result.error "TypPackage has no mapping in C_P4Type"
    | TypSpecializedType (base) (args) => Result.error "TypSpecializedType has no mapping in C_P4Type"
    | TypConstructor (type_params) (wildcard_params) (parameters) (ret) => Result.error "TypConstructor has no mapping in C_P4Type"
    end.

  Inductive Embed : Val.t -> VAL -> Prop :=
  | Embed_bool b :
      Embed (Val.Bool b) (ValBaseBool b)
  | Embed_bit w n :
      Embed (Val.Bit w n) (ValBaseBit (to_lbool w n))
  | Embed_int w z :
      Embed (Val.Int w z) (ValBaseInt (to_lbool (Npos w) z))
  | Embed_varbit m w n :
      Embed (Val.VarBit m w n) (ValBaseVarbit m (to_lbool w n))
  | Embed_tuple vs vs' :
      Forall2 Embed vs vs' ->
      Embed
        (Val.Lists Lst.Struct vs)
        (ValBaseStruct (make_assoc_list 0 vs'))
  | Embed_header vs vs' b :
      Forall2 Embed vs vs' ->
      Embed
        (Val.Lists (Lst.Header b) vs)
        (ValBaseHeader (make_assoc_list 0 vs') b)
  | Embed_array t vs vs' :
    Forall2 Embed vs vs' ->
    Embed
      (Val.Lists (Lst.Array t) vs)
      (ValBaseStack vs' 0%N)
  | Embed_error er :
    Embed (Val.Error er) (ValBaseError er).

  Fixpoint embed (v : Val.t) : VAL :=
    match v with
    | Val.Bool b => ValBaseBool b
    | Val.Bit w n => ValBaseBit $ to_lbool w n
    | Val.Int w z  => ValBaseInt $ to_lbool (Npos w) z
    | Val.VarBit m w n => ValBaseVarbit m $ to_lbool w n
    | Val.Lists (Lst.Header b) vs =>
        ValBaseHeader (make_assoc_list 0 (List.map embed vs)) b
    | Val.Lists Lst.Struct vs =>
        ValBaseStruct (make_assoc_list 0 (List.map embed vs))
    | Val.Lists (Lst.Array _) vs =>
        ValBaseStack (List.map embed vs) 0%N
    | Val.Error v  => ValBaseError v
    end.

  Fixpoint project (v : VAL) : option Val.t :=
    let project_field_values fields :=
      let* fields' := map_monad_values project fields in
      values_of_fields O fields'
    in
    match v with
    | ValBaseBool b => mret $ Val.Bool b
    | ValBaseBit bits => mret $ uncurry Val.Bit $ BitArith.from_lbool bits
    | ValBaseInt bits =>
      let (w, n) := BitArith.from_lbool bits in
      match w with
      | Npos w => mret $ Val.Int w n
      | N0 => None (* Fail on zero width *)
      end
    | ValBaseVarbit m bits => mret $ uncurry (Val.VarBit m) $ BitArith.from_lbool bits
    | ValBaseHeader fields b =>
      let^ field_values := project_field_values fields in
      Val.Lists (Lst.Header b) field_values
    | ValBaseStruct fields =>
      let^ field_values := project_field_values fields in
      Val.Lists Lst.Struct field_values
    | ValBaseStack entries 0%N =>
      let* entries' := map_monad project entries in
      let^ type := typ_of_val <$> hd_error entries' in
      Val.Lists (Lst.Array type) entries'
    | ValBaseError err => mret $ Val.Error err
    | _ => None
    end.

  Section ProjectFieldsSound.

    Definition project_field_values fields :=
      let* fields' := map_monad_values project fields in
      values_of_fields O fields'.

    Variable fields : list (string * VAL).

    Hypothesis IH : Forall (fun '(_, v) => forall v', project v = Some v' -> Embed v' v) fields.
    
    Lemma project_fields_sound :
      forall vs, map_monad_values project fields = Some vs -> Forall2 Embed (map snd vs) (map snd fields).
    Proof.
      intros. rewrite sublist.Forall2_map. unfold map_monad_values in *.
      unravel in *. apply map_monad_some in H.
      generalize dependent vs. induction fields; intros.
      - inv IH. inv H. constructor.
      - inv IH. inv H. destruct a. match_some_inv. some_inv. auto.
    Qed.

    Lemma project_field_values_sound vs :
        project_field_values fields = Some vs ->
          Forall2 Embed vs (map snd fields) /\ make_assoc_list O (map snd fields) = fields.
    Proof.
      cbn. unravel. intros. match_some_inv. split.
      - apply project_fields_sound in Heqo. apply id_fields in H. subst.
        rewrite map_snd_make_assoc_list_idem in Heqo. assumption.
      - unfold values_of_fields in *. destruct (split a) eqn:Esplit.
        rewrite split_map in Esplit. inv Esplit.
        destruct (keys_valid 0 (map fst a)) eqn:Evalid; try discriminate.
        cbn in *. some_inv. apply map_monad_values_keys in Heqo.
        assert (values_of_fields O fields = Some (map snd fields)).
        { unfold values_of_fields. rewrite split_map. cbn. unravel.
          rewrite Heqo. rewrite Evalid. reflexivity. }
        apply id_fields. assumption.
    Qed.

  End ProjectFieldsSound.

  Lemma project_sound v v' : project v = Some v' -> Embed v' v.
  Proof.
    intros. generalize dependent v'.
    induction v using custom_ValueBase_ind; try discriminate; unravel in *; intros.
    - some_inv. constructor.
    - some_inv.
      replace (ValBaseBit n) with (ValBaseBit (uncurry to_lbool (BitArith.from_lbool n)))
        by (f_equal; apply bit_to_from_bool).
      unravel. constructor.
    - destruct (Z.to_N (Zcomplements.Zlength z)) eqn:E; try discriminate. some_inv. 
      replace (ValBaseInt z) with (ValBaseInt (uncurry to_lbool (BitArith.from_lbool z)))
        by (f_equal; apply bit_to_from_bool).
      unravel. rewrite E. constructor.
    - some_inv.
      replace (ValBaseVarbit w n) with (ValBaseVarbit w (uncurry to_lbool (BitArith.from_lbool n)))
        by (f_equal; apply bit_to_from_bool).
      unravel. constructor.
    - some_inv. constructor.
    - match_some_inv.
      apply project_field_values_sound in Heqo as [Hembed Hassoc]; auto. some_inv.
      rewrite <- Hassoc. constructor. assumption.
    - match_some_inv.
      apply project_field_values_sound in Heqo as [Hembed Hassoc]; auto. some_inv.
      rewrite <- Hassoc. constructor. assumption.
    - destruct i; try discriminate. repeat match_some_inv. repeat some_inv.
      clear Heqo1. constructor. rewrite map_monad_some in Heqo. induction Heqo.
      + constructor.
      + inv H. constructor; auto.
  Qed.

  Definition project_values := map_monad project.

  Definition project_values_sound :
    forall vs vs',
      project_values vs = Some vs' -> Forall2 Embed vs' vs.
  Proof.
    intros. unfold project_values in *. rewrite map_monad_some in H.
    induction H; constructor; auto. apply project_sound. assumption.
  Qed.
  
  Inductive embed_exp : Exp.t -> EXP -> Prop :=
  | embed_MkExpression e e' i t d :
    embed_pre_exp e e' ->
    embed_exp e (MkExpression i e' t d)
  with embed_pre_exp : Exp.t -> ExpressionPreT (tags_t:=tags_t) -> Prop :=
  | embed_ebool b :
    embed_pre_exp (Exp.Bool b) (ExpBool b)
  | embed_ebit w n i :
    embed_pre_exp
      (w `W n)%exp
      (ExpInt
         {| P4Int.tags:=i; P4Int.value:=n; P4Int.width_signed:=Some (w,false) |})
  | embed_eint w z i :
    embed_pre_exp
      (w `S z)%exp
      (ExpInt
         {| P4Int.tags:=i; P4Int.value:=z; P4Int.width_signed:=Some (Npos w,true) |}).
  
  Definition interpret_embed_pre_exp (e : Exp.t) : option ExpressionPreT :=
    match e with 
    | Exp.Bool b => mret (ExpBool b)
    | (w `W n)%exp =>
      mret (ExpInt {|
        P4Int.tags := dummy_tags;
        P4Int.value := n;
        P4Int.width_signed := Some (w, false) 
      |})
    | (w `S z)%exp =>
      mret (ExpInt {|
        P4Int.tags := dummy_tags; 
        P4Int.value := z; 
        P4Int.width_signed := Some (Npos w, true)
      |})
    | _ => None
    end.

  Definition interpret_embed_exp (e : Exp.t) : option EXP :=
    let^ e := interpret_embed_pre_exp e in
    (* garbage values for tags, type, and direction *)
    MkExpression dummy_tags e TypBool Directionless.

  Lemma interpret_embed_exp_sound :
    forall e e', interpret_embed_exp e = Some e' -> embed_exp e e'.
  Proof.
    intros. destruct e; try discriminate; inv H; constructor; constructor.
  Qed.

  Lemma interpret_embed_exp_complete :
    forall e, interpret_embed_exp e = None -> ~exists e', embed_exp e e'.
  Proof.
    unfold "~". intros. destruct e; inv H; inv H0; inv H; inv H0.
  Qed.

  Definition unembed_exp (e : EXP) : option Exp.t :=
    let 'MkExpression _ e _ _ := e in
    match e with
    | ExpBool b => mret (Exp.Bool b)
    | ExpInt {| P4Int.value := n; P4Int.width_signed := Some (w, false) |} => mret (w `W n)%exp
    | ExpInt {| P4Int.value := z; P4Int.width_signed := Some (Npos w, true)|} => mret (w `S z)%exp
    | _ => None
    end.

  Lemma unembed_exp_sound :
    forall e e', unembed_exp e' = Some e -> embed_exp e e'.
  Proof.
    unfold unembed_exp. intros. destruct e', expr; try discriminate.
    - constructor. inv H. constructor.
    - destruct t, width_signed; try discriminate.
      destruct p, b, n; try discriminate; 
      inv H; do 2 constructor.
  Qed.

  Lemma unembed_exp_complete :
    forall e e', embed_exp e e' -> unembed_exp e' = Some e.
  Proof.
    intros. inv H. inv H0; auto.
    destruct w; constructor.
  Qed.

  Lemma unembed_exp_adequate :
    forall e e', unembed_exp e' = Some e <-> embed_exp e e'.
  Proof.
    split.
    - apply unembed_exp_sound.
    - apply unembed_exp_complete.
  Qed.

  Inductive embed_pat_valset : Pat.t -> ValueSet -> Prop :=
  | embed_pat_wild :
    embed_pat_valset Pat.Wild ValSetUniversal
  | embed_pat_bit w n :
    embed_pat_valset
      (w PW n)%pat (ValSetSingleton (ValBaseBit (to_lbool w n)))
  | embed_pat_int w z :
    embed_pat_valset
      (w PS z)%pat (ValSetSingleton (ValBaseInt (to_lbool (Npos w) z)))
  | embed_pat_range p₁ p₂ v₁ v₂ :
    embed_pat_valset p₁ (ValSetSingleton v₁) ->
    embed_pat_valset p₂ (ValSetSingleton v₂) ->
    embed_pat_valset (Pat.Range p₁ p₂) (ValSetRange v₁ v₂)
  | embed_pat_mask p₁ p₂ v₁ v₂ :
    embed_pat_valset p₁ (ValSetSingleton v₁) ->
    embed_pat_valset p₂ (ValSetSingleton v₂) ->
    embed_pat_valset (Pat.Mask p₁ p₂) (ValSetMask v₁ v₂)
  | embed_pat_lists ps vss :
    Forall2 embed_pat_valset ps vss ->
    embed_pat_valset (Pat.Lists ps) (ValSetProd vss).

  Definition unembed_valset_singleton (v : @ValueBase bool) : option Pat.t :=
    match v with
    | ValBaseBit bits => mret $ uncurry Pat.Bit $ BitArith.from_lbool bits
    | ValBaseInt bits =>
      let (w, z) := BitArith.from_lbool bits in
      match w with
      | N0 => None
      | Npos w => mret $ Pat.Int w z
      end
    | _ => None
    end.

  Lemma unembed_valset_singleton_sound :
    forall v pat,
      unembed_valset_singleton v = Some pat ->
        embed_pat_valset pat (ValSetSingleton v).
  Proof.
    intros. destruct v; try discriminate.
    - inv H. cbn.
      replace (ValBaseBit value) with (ValBaseBit (to_lbool (Z.to_N (Zcomplements.Zlength value)) (BitArith.lbool_to_val value 1 0))).
      * constructor.
      * f_equal. apply to_lbool_lbool_to_val.
    - inv H. destruct (Z.to_N _) eqn:?; try discriminate. inv H1.
      replace (ValBaseInt value) with (ValBaseInt (to_lbool (Z.to_N (Zcomplements.Zlength value)) (BitArith.lbool_to_val value 1 0))).
      * rewrite Heqn. constructor.
      * f_equal. apply to_lbool_lbool_to_val.
    Qed.

  Fixpoint unembed_valset (val : ValueSet) : option Pat.t :=
    match val with
    | ValSetUniversal => mret Pat.Wild
    | ValSetSingleton v => unembed_valset_singleton v
    | ValSetRange v₁ v₂ =>
      let* p₁ := unembed_valset_singleton v₁ in
      let^ p₂ := unembed_valset_singleton v₂ in
      Pat.Range p₁ p₂
    | ValSetMask v₁ v₂ =>
      let* p₁ := unembed_valset_singleton v₁ in
      let^ p₂ := unembed_valset_singleton v₂ in
      Pat.Mask p₁ p₂
    | ValSetProd vss => map_monad unembed_valset vss >>| Pat.Lists
    | _ => None
    end.

  Lemma unembed_valset_sound :
    forall val pat, unembed_valset val = Some pat -> embed_pat_valset pat val.
  Proof.
    induction val using custom_ValueSet_ind; intros; try discriminate.
    - cbn in H. apply unembed_valset_singleton_sound. assumption.
    - inv H. constructor.
    - cbn in H. unfold option_bind in *.
      destruct (unembed_valset_singleton value) eqn:Hvalue; try discriminate.
      apply unembed_valset_singleton_sound in Hvalue.
      destruct (unembed_valset_singleton mask) eqn:Hmask; try discriminate.
      inv H. apply unembed_valset_singleton_sound in Hmask.
      constructor; auto.
    - cbn in H. unfold option_bind in *.
      destruct (unembed_valset_singleton lo) eqn:Hlo; try discriminate.
      apply unembed_valset_singleton_sound in Hlo.
      destruct (unembed_valset_singleton hi) eqn:Hhi; try discriminate.
      inv H. apply unembed_valset_singleton_sound in Hhi.
      constructor; auto.
    - cbn in *. unfold option_bind in *.
      destruct (map_monad unembed_valset l) eqn:HSome; try discriminate. inv H0.
      constructor. rewrite map_monad_some in HSome.
      generalize dependent l0. induction l; intros.
      + inv HSome. constructor.
      + inv H. inv HSome. constructor; auto.
  Qed.

  Definition unembed_valsets : list ValueSet -> option (list Pat.t) := map_monad unembed_valset.

  Lemma unembed_valsets_sound :
    forall vss pats,
      unembed_valsets vss = Some pats -> Forall2 embed_pat_valset pats vss.
  Proof.
    unfold unembed_valsets. intros. rewrite map_monad_some in H.
    generalize dependent pats. induction vss; intros.
    - inv H. constructor.
    - inv H. constructor; auto. apply unembed_valset_sound. assumption.
  Qed.
  
  Definition get_singleton (val : ValueSet) : option (@ValueBase bool) :=
    match val with
    | ValSetSingleton b => mret b
    | _ => None
    end.

  Fixpoint embed_pat (pat : Pat.t) : option ValueSet :=
    match pat with
    | Pat.Wild => mret ValSetUniversal
    | (w PW n)%pat => mret $ ValSetSingleton $ ValBaseBit $ to_lbool w n
    | (w PS z)%pat => mret $ ValSetSingleton $ ValBaseInt $ to_lbool (Npos w) z
    | Pat.Range p₁ p₂ =>
      let* v₁ := get_singleton =<< embed_pat p₁ in
      let^ v₂ := get_singleton =<< embed_pat p₂ in
      ValSetRange v₁ v₂
    | Pat.Mask p₁ p₂ =>
      let* v₁ := get_singleton =<< embed_pat p₁ in
      let^ v₂ := get_singleton =<< embed_pat p₂ in
      ValSetMask v₁ v₂
    | Pat.Lists ps => map_monad embed_pat ps >>| ValSetProd
    end.

    Lemma embed_pat_sound :
      forall pat val, embed_pat pat = Some val -> embed_pat_valset pat val.
    Proof.
      induction pat using custom_pat_ind; cbn; intros.
      - inv H. constructor.
      - unfold option_bind in *.
        destruct (embed_pat pat1) eqn:?; try discriminate.
        destruct v; try discriminate. cbn in *.
        destruct (embed_pat pat2); try discriminate.
        destruct v; try discriminate. cbn in *. inv H.
        constructor; auto.
      - unfold option_bind in *.
        destruct (embed_pat pat1) eqn:?; try discriminate.
        destruct v; try discriminate. cbn in *.
        destruct (embed_pat pat2); try discriminate.
        destruct v; try discriminate. cbn in *. inv H.
        constructor; auto.
      - inv H. constructor.
      - inv H. constructor.
      - unfold option_bind in *. destruct (map_monad embed_pat ps) eqn:?; try discriminate.
        inv H0. apply map_monad_some in Heqo. generalize dependent l.
        induction ps; intros.
        + inv Heqo. repeat constructor.
        + inv Heqo. inv H. repeat constructor; auto.
          eapply IHps in H5; eauto. inv H5. assumption.
    Qed.

    Lemma embed_pat_complete :
      forall pat val, embed_pat_valset pat val -> embed_pat pat = Some val.
    Proof.
      induction pat using custom_pat_ind.
      - intros. inv H. reflexivity.
      - intros. inv H. cbn. unfold option_bind. erewrite IHpat1, IHpat2; eauto. reflexivity.
      - intros. inv H. cbn. unfold option_bind. erewrite IHpat1, IHpat2; eauto. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - cbn. unfold option_bind.
        assert (forall vss, embed_pat_valset (Pat.Lists ps) (ValSetProd vss) -> map_monad embed_pat ps = Some vss).
        { induction ps; intros.
          - inv H0. inv H3. reflexivity.
          - inv H. inv H0. inv H2. cbn. unfold option_bind.
            apply H3 in H1. rewrite H1. apply IHps with (vss := l') in H4.
            + unfold map_monad, "∘" in *. rewrite H4. reflexivity.
            + constructor. assumption.
        }
        intros. inv H1. erewrite H0; eauto. constructor. assumption.
    Qed.

  Fixpoint snd_map {A : Type} {B : Type} (func : A -> B) (l : list (string * A)) :=
    match l with 
    | [] => []
    | (_, h)::t => func h :: snd_map func t
    end.

  Fixpoint proj (v : VAL) : result string Val.t :=
    match v with
    | ValBaseBool b => Result.ok (Val.Bool b)
    | ValBaseInt lb =>
        let (w, n) := IntArith.from_lbool lb in 
        Result.ok (Val.Int (SyntaxUtil.pos_of_N w) n) 
    | ValBaseNull => Result.error "no null"
    | ValBaseBit lb =>
        let (w, n) := BitArith.from_lbool lb in 
        Result.ok(Val.Bit w n) 
    | ValBaseVarbit w lb =>
        let (w', n) := BitArith.from_lbool lb in 
        if N.leb w' w
        then Result.ok(Val.VarBit w w' n) 
        else Result.error("varbit too wide")
    | ValBaseStruct s =>
        sequence
          (map (fun '(_,v) => proj v) s)
          >>| Val.Lists Lst.Struct
    | ValBaseHeader s b =>
        sequence
          (map (fun '(_,v) => proj v) s)
          >>| Val.Lists (Lst.Header b)
    | ValBaseStack vs _ =>
        let* vs := sequence (map proj vs) in
        let^ t :=
          Result.from_opt
            (List.head vs >>| typ_of_val)
            "Empty array" in
        Val.Lists (Lst.Array t) vs
    | ValBaseError e => Result.ok (Val.Error e)
    | ValBaseInteger _ => Result.error("No mapping for ValBaseInteger exists")
    | ValBaseString _ => Result.error("No mapping for ValBaseString exists")
    | ValBaseTuple _ => Result.error("No mapping for ValBaseTuple exists")
    | ValBaseMatchKind _ => Result.error("No mapping for ValBaseMatchKind exists")
    | ValBaseUnion _ => Result.error("No mapping for ValBaseUnion exists")
    | ValBaseEnumField _ _ => Result.error("No mapping for ValBaseEnumField exists")
    | ValBaseSenumField _ _ => Result.error("No mapping for ValBaseSenumField exists")
    end.

  Local Hint Constructors Embed : core.
  
  Lemma embed_Embed : forall v, Embed v (embed v).
  Proof.
    intro v; induction v using custom_val_ind;
      unravel in *; auto.
    apply Forall_map_Forall2 in H.
    destruct ls; eauto.
  Qed.

  Infix "^" := Z.pow.

  Lemma embed_project_ok : forall v t, type_val v t -> proj (embed v) = Result.ok v.
  Proof.
    intro v; intro t; intro H; induction H using custom_type_val_ind; 
      unravel in *; auto.
    - rewrite -> Zlength_to_lbool. 
      rewrite -> Znat.N2Z.id.
      rewrite -> bit_to_lbool_back. 
      unfold BitArith.bound in H.
      destruct H. f_equal. f_equal.
      unfold BitArith.mod_bound.
      remember (BitArith.upper_bound w).
      rewrite -> Zdiv.Zmod_small.
      + reflexivity.
      + lia.
    - f_equal.
      rewrite -> Zlength_to_lbool. 
      rewrite -> Znat.N2Z.id.
      simpl. f_equal.
      rewrite -> int_to_lbool_back.
      simpl. 
      unfold IntArith.bound in H.
      destruct H. 
      unfold IntArith.mod_bound.
      destruct (list_solver.Z_le_lt_dec 0 z) as [hz0 | hz0].
      + unfold IntArith.maxZ in H0.
        unfold IntArith.mod_amt.
        unfold IntArith.upper_bound in H0.
        rewrite Zdiv.Zmod_small.
        * unfold IntArith.upper_bound.
          assert (hz: (z <? Z.pow 2 (Z.pos w - 1))%Z = true).
          { rewrite <- Zbool.Zlt_is_lt_bool. lia. }
          rewrite hz; reflexivity.
        * split; try lia.
          enough (hduh : Z.pow 2 (Z.pos w - 1) < Z.pow 2 (Z.pos w)) by lia.
          apply Z.pow_lt_mono_r; lia.
      + (* TODO: stuck :(.
      Check Zdiv.Zmod_small.
        Search (_ <  -> _ mod _ = _).
        Search (_ mod _).
          Search (_ <= _ - _).
          rewrite <- Z.le_add_le_sub_l in H0.
          
      rewrite IntArith.mod_amt_2_upper_bound.
      unfold IntArith.minZ,IntArith.maxZ in *.
      unfold IntArith.upper_bound at 1 2.
      Search (_ mod _).
      Locate "mod". Print Z.modulo.
      Search (_ mod _ < _).
      Search (_ mod (2 * _)).
      rewrite <- div_2_mod_2_pow by lia.
      Search ((_ / _) mod _).
      pose proof Zdiv.Z_mod_lt z _ (IntArith.mod_amt_gt_0 w) as h.
      destruct h as [h1 h2].
      Print IntArith.mod_amt.
      Print IntArith.upper_bound.
      Search (?x < ?y <-> ?x <? ?y = true).
      rewrite Zbool.Zlt_is_lt_bool in h2.
      unfold IntArith.mod_amt, IntArith.upper_bound in *.
      Search IntArith.mod_amt.
      destruct (z mod IntArith.mod_amt w <? IntArith.upper_bound w)
               eqn:eqz.
      + Search (_ <? _ = true).
        rewrite Z.ltb_lt in eqz.
        
        unfold IntArith.mod_amt in *.
        unfold IntArith.upper_bound in eqz.
        Search (_ mod _).
      Search (_ mod _ - _).
      
      unfold IntArith.minZ, IntArith.maxZ in *.
      unfold IntArith.mod_amt.
      unfold IntArith.upper_bound in *.
      Locate "_ ^ _".
      Search (_ mod (Z.pow _ _)%Z).
      rewrite <- Z.land_ones at 1 by lia.
      Search (Z.land _ (Z.ones
      remember (IntArith.mod_amt w).
      remember (IntArith.upper_bound w).
      unfold IntArith.mod_amt in Heqz0.
      unfold IntArith.upper_bound in Heqz1.
      unfold IntArith.maxZ in H0.
      unfold IntArith.upper_bound in H0.
      rewrite -> Zdiv.Zmod_small.
      unfold IntArith.maxZ in H0.
      rewrite <- Heqz1 in H0.
      assert (z < z1). 
        * lia.
        * unfold IntArith.mod_amt in Heqz0.
        unfold IntArith.upper_bound in Heqz1. 
        
        (* destruct_with_eqn (z <? z1) . 
          -- auto. *)
          -- lia.
        * unfold IntArith.maxZ in H0.
        unfold IntArith.upper_bound in H0.
        unfold IntArith.mod_amt in Heqz0.
        assert (IntArith.minZ w <= 0).
          -- unfold IntArith.minZ. 
            unfold IntArith.upper_bound. 
            remember (Z.pow 2 (Z.pos w - 1)).
            induction z2.
              ** reflexivity.
              ** lia.
              ** admit.
          -- admit. *) admit.   
    - admit. (* varbit case *)
    - apply Forall2_only_l_Forall in H1.
      pose proof Forall_map_Forall2
           _ _ (fun v v' => proj v' = Result.ok v) embed _ H1 as h.
      pose proof Forall2_map_both
           _ _ _ _ (fun v v' => v' = v) Result.ok proj as h'.
      rewrite h', Forall2_flip, Forall2_eq in h; clear h'.
      clear dependent ts. clear dependent t.
      clear H1.
      destruct ls; cbn in *;
        try rewrite map_pat_both,
        <- map_map,map_snd_make_assoc_list_idem;
        induction vs as [| v vs ih];
        unravel in *; inv h; auto;
        try match goal with
            | H: proj (embed ?v) = Result.ok ?v,
                h: map proj (map embed ?vs) = map Result.ok ?vs
              |- _ => rewrite H, h,
                Result.sequence_map_Result_ok; unravel; try reflexivity
            end.
      + (* TODO: impossible. *) admit.
      + repeat f_equal. (* TODO: problem. *)
  Admitted.

End Embed.
