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
Require Import BinPos BinInt BinNat Pnat Nnat.
Require Import PeanoNat.
Import AllCubNotations Val.ValueNotations.
Import Poulet4.P4light.Syntax.Typed.
Local Open Scope string_scope.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Context {tags_t: Type}. 
  Context {dummy_tags: tags_t}. 
  Context {string_list: list string}.
  Notation VAL := (@ValueBase bool).
  Notation EXPR := (@Expression tags_t).
  Notation C_P4Type := Expr.t. 
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
  | TBool : P4Cub_to_P4Light Expr.TBool TypBool      
  | TBit (width : N) : P4Cub_to_P4Light (Expr.TBit width) (TypBit width)
  | TInt (width : positive) : P4Cub_to_P4Light (Expr.TInt width) (TypInt (Npos width))
  | TError : P4Cub_to_P4Light Expr.TError TypError   
  | TStruct_not_header (types : list Expr.t) (light_types : list P_P4Type) : 
    Forall2 P4Cub_to_P4Light types light_types -> 
    P4Cub_to_P4Light
      (Expr.TStruct false types)
      (TypStruct (List.map (prod_map_l emb_string) (make_assoc_list 0 light_types)))
  | TStruct_header (types : list Expr.t) (light_types : list P_P4Type) : 
    Forall2 P4Cub_to_P4Light types light_types -> 
    P4Cub_to_P4Light
      (Expr.TStruct true types)
      (TypHeader (List.map (prod_map_l emb_string) (make_assoc_list 0 light_types)))
  | TArray n t t' :
    P4Cub_to_P4Light t t' ->
    P4Cub_to_P4Light
      (Expr.TArray n t)
      (TypArray t' n)
  | TVar (type_name : string) :
    (* if (string_to_int type_name 0 string_list) == None
       then P4Cub_to_P4Light Expr.TError TypError
    else  *)
    P4Cub_to_P4Light
      (Expr.TVar (get_int (string_to_int type_name 0 string_list)))
      (TypTypeName (emb_string type_name)).

    (* embed *)
  Fixpoint P4Cub_to_P4Light_fun (c : C_P4Type) : P_P4Type:= 
    match c with
    | Expr.TBool => TypBool       
    | Expr.TBit (width) => TypBit width
    | Expr.TInt (width) => TypInt (Npos width)
    | Expr.TVarBit (width) => TypVarBit width
    | Expr.TError => TypError
    | Expr.TArray n t =>
        TypArray (P4Cub_to_P4Light_fun t) n
    | Expr.TStruct true types =>
        TypStruct
          (List.map
             (prod_map_l emb_string)
             (make_assoc_list 0 (List.map P4Cub_to_P4Light_fun types)))
    | Expr.TStruct false types =>
        TypHeader
          (List.map
             (prod_map_l emb_string)
             (make_assoc_list 0 (List.map P4Cub_to_P4Light_fun types)))
    | Expr.TVar (type_name) => TypTypeName (emb_string (nth type_name string_list ""))
    end.

  (* project *)
  Fixpoint P4Light_to_P4Cub_fun (p : P_P4Type) : result string C_P4Type := 
    match p with
    | TypBool => Result.ok Expr.TBool
    | TypString => Result.error "TypString has no mapping in C_P4Type"
    | TypInteger => Result.error "TypInteger has no mapping in C_P4Type"
    | TypInt (width) => Result.ok (Expr.TInt (SyntaxUtil.pos_of_N width))
    | TypBit (width) => Result.ok (Expr.TBit (width))
    | TypVarBit (width) => Result.error "TypVarBit has no mapping in C_P4Type"
    | TypArray typ size =>
        P4Light_to_P4Cub_fun typ >>| Expr.TArray size
    | TypTuple types => 
        sequence
          (List.map P4Light_to_P4Cub_fun types)
          >>| Expr.TStruct false
    | TypList (types) => Result.error "TypList has no mapping in C_P4Type"
    | TypRecord (fields) => Result.error "TypRecord has no mapping in C_P4Type"
    | TypSet (elt_type) => Result.error "TypSet has no mapping in C_P4Type"
    | TypError => Result.ok Expr.TError
    | TypMatchKind => Result.error "TypMatchKind has no mapping in C_P4Type"
    | TypVoid => Result.error "TypVoid has no mapping in C_P4Type"
    | TypHeader (fields) => Result.error "Headers to be removed"
    | TypHeaderUnion (fields) => Result.error "TypHeaderUnion to be removed"
    | TypStruct (fields) => Result.error "TypStruct to be removed"
    | TypEnum (name) (typ) (members) => Result.error "TypEnum has no mapping in C_P4Type"
    | TypTypeName (name) => Result.ok (Expr.TVar (get_int (string_to_int (P4String.str name) 0 string_list))) 
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

  Inductive Embed : Val.v -> VAL -> Prop :=
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
        (Val.Lists Expr.lists_struct vs)
        (ValBaseStruct (make_assoc_list 0 vs'))
  | Embed_header vs vs' b :
      Forall2 Embed vs vs' ->
      Embed
        (Val.Lists (Expr.lists_header b) vs)
        (ValBaseHeader (make_assoc_list 0 vs') b)
  | Embed_array t vs vs' :
    Forall2 Embed vs vs' ->
    Embed
      (Val.Lists (Expr.lists_array t) vs)
      (ValBaseStack vs' 0%N)
  | Embed_error er :
    Embed (Val.Error er) (ValBaseError er).

  Fixpoint embed (v : Val.v) : VAL :=
    match v with
    | Val.Bool b => ValBaseBool b
    | Val.Bit w n => ValBaseBit $ to_lbool w n
    | Val.Int w z  => ValBaseInt $ to_lbool (Npos w) z
    | Val.VarBit m w n => ValBaseVarbit m $ to_lbool w n
    | Val.Lists (Expr.lists_header b) vs =>
        ValBaseHeader (make_assoc_list 0 (List.map embed vs)) b
    | Val.Lists Expr.lists_struct vs =>
        ValBaseStruct (make_assoc_list 0 (List.map embed vs))
    | Val.Lists (Expr.lists_array _) vs =>
        ValBaseStack (List.map embed vs) 0%N
    | Val.Error v  => ValBaseError v
    end.
  
  Inductive embed_expr : Expr.e -> EXPR -> Prop :=
  | embed_MkExpression e e' i t d :
    embed_pre_expr e e' ->
    embed_expr e (MkExpression i e' t d)
  with embed_pre_expr : Expr.e -> ExpressionPreT (tags_t:=tags_t) -> Prop :=
  | embed_ebool b :
    embed_pre_expr (Expr.Bool b) (ExpBool b)
  | embed_ebit w n i :
    embed_pre_expr
      (w `W n)%expr
      (ExpInt
         {| P4Int.tags:=i; P4Int.value:=n; P4Int.width_signed:=Some (w,false) |})
  | embed_eint w z i :
    embed_pre_expr
      (w `S z)%expr
      (ExpInt
         {| P4Int.tags:=i; P4Int.value:=z; P4Int.width_signed:=Some (Npos w,true) |}).
  
  Definition interpret_embed_pre_expr (e : Expr.e) : option ExpressionPreT :=
    match e with 
    | Expr.Bool b => mret (ExpBool b)
    | (w `W n)%expr =>
      mret (ExpInt {|
        P4Int.tags := dummy_tags;
        P4Int.value := n;
        P4Int.width_signed := Some (w, false) 
      |})
    | (w `S z)%expr =>
      mret (ExpInt {|
        P4Int.tags := dummy_tags; 
        P4Int.value := z; 
        P4Int.width_signed := Some (Npos w, true)
      |})
    | _ => None
    end.

  Definition interpret_embed_expr (e : Expr.e) : option EXPR :=
    let^ e := interpret_embed_pre_expr e in
    (* garbage values for tags, type, and direction *)
    MkExpression dummy_tags e TypBool Directionless.

  Lemma interpret_embed_expr_sound :
    forall e e', interpret_embed_expr e = Some e' -> embed_expr e e'.
  Proof.
    intros. destruct e; try discriminate; inv H; constructor; constructor.
  Qed.

  Lemma interpret_embed_expr_complete :
    forall e, interpret_embed_expr e = None -> ~exists e', embed_expr e e'.
  Proof.
    unfold "~". intros. destruct e; inv H; inv H0; inv H; inv H0.
  Qed.

  Definition unembed_expr (e : EXPR) : option Expr.e :=
    let 'MkExpression _ e _ _ := e in
    match e with
    | ExpBool b => mret (Expr.Bool b)
    | ExpInt {| P4Int.value := n; P4Int.width_signed := Some (w, false) |} => mret (w `W n)%expr
    | ExpInt {| P4Int.value := z; P4Int.width_signed := Some (Npos w, true)|} => mret (w `S z)%expr
    | _ => None
    end.

  Lemma unembed_expr_sound :
    forall e e', unembed_expr e' = Some e -> embed_expr e e'.
  Proof.
    unfold unembed_expr. intros. destruct e', expr; try discriminate.
    - constructor. inv H. constructor.
    - destruct t, width_signed; try discriminate.
      destruct p, b, n; try discriminate; 
      inv H; do 2 constructor.
  Qed.

  Lemma unembed_expr_complete :
    forall e e', embed_expr e e' -> unembed_expr e' = Some e.
  Proof.
    intros. inv H. inv H0; auto.
    destruct w; constructor.
  Qed.

  Lemma unembed_expr_adequate :
    forall e e', unembed_expr e' = Some e <-> embed_expr e e'.
  Proof.
    split.
    - apply unembed_expr_sound.
    - apply unembed_expr_complete.
  Qed.

  Inductive embed_pat_valset : Parser.pat -> ValueSet (tags_t:=tags_t) -> Prop :=
  | embed_pat_wild :
    embed_pat_valset Parser.Wild ValSetUniversal
  | embed_pat_bit w n :
    embed_pat_valset
      (w PW n)%pat (ValSetSingleton (ValBaseBit (to_lbool w n)))
  | embed_pat_int w z :
    embed_pat_valset
      (w PS z)%pat (ValSetSingleton (ValBaseInt (to_lbool (Npos w) z)))
  | embed_pat_range p₁ p₂ v₁ v₂ :
    embed_pat_valset p₁ (ValSetSingleton v₁) ->
    embed_pat_valset p₂ (ValSetSingleton v₂) ->
    embed_pat_valset (Parser.Range p₁ p₂) (ValSetRange v₁ v₂)
  | embed_pat_mask p₁ p₂ v₁ v₂ :
    embed_pat_valset p₁ (ValSetSingleton v₁) ->
    embed_pat_valset p₂ (ValSetSingleton v₂) ->
    embed_pat_valset (Parser.Mask p₁ p₂) (ValSetMask v₁ v₂)
  | embed_pat_lists ps vss :
    Forall2 embed_pat_valset ps vss ->
    embed_pat_valset (Parser.Lists ps) (ValSetProd vss).
  
  Fixpoint snd_map {A : Type} {B : Type} (func : A -> B) (l : list (string * A)) :=
    match l with 
    | [] => []
    | (_, h)::t => func h :: snd_map func t
    end.

  Fixpoint proj (v : VAL) : result string Val.v :=
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
          >>| Val.Lists Expr.lists_struct
    | ValBaseHeader s b =>
        sequence
          (map (fun '(_,v) => proj v) s)
          >>| Val.Lists (Expr.lists_header b)
    | ValBaseStack vs _ =>
        let* vs := sequence (map proj vs) in
        let^ t :=
          Result.from_opt
            (List.head vs >>| t_of_v)
            "Empty array" in
        Val.Lists (Expr.lists_array t) vs
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
    intro v; induction v using custom_v_ind;
      unravel in *; auto.
    apply Forall_map_Forall2 in H.
    destruct ls; eauto.
  Qed.

  Infix "^" := Z.pow.

  Lemma embed_project_ok : forall v t, type_value v t -> proj (embed v) = Result.ok v.
  Proof.
    intro v; intro t; intro H; induction H using custom_type_value_ind; 
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
