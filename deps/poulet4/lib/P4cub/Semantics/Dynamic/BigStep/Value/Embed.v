Require Export Coq.Strings.String
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4light.Syntax.Value
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        Poulet4.Utils.ForallMap
        Poulet4.Utils.Utils Poulet4.Utils.P4Arith
        Poulet4.Monads.Monad.
Require Poulet4.P4light.Syntax.P4String.
Require Import Poulet4.P4cub.Syntax.CubNotations.
Import AllCubNotations Val.ValueNotations.
Import Poulet4.P4light.Syntax.Typed.
Local Open Scope string_scope.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Context {tags_t: Type}. 
  Context {dummy_tags: tags_t}. 
  Notation VAL := (@ValueBase bool).
  Notation C_P4Type := Expr.t. 
  Notation P_P4Type := (@P4Type tags_t). 

  Definition emb_string (s : string) : P4String.t tags_t := 
  {| P4String.str := s; P4String.tags := dummy_tags |}. 

  (* not needed for now *)
  (* Inductive emb_kv : string * C_P4Type -> P4String.t tags_t * P_P4Type -> Prop := *) 

  Inductive P4Cub_to_P4Light : C_P4Type -> P_P4Type -> Prop := 
  | TBool : P4Cub_to_P4Light Expr.TBool TypBool      
  | TBit (width : N) : P4Cub_to_P4Light (Expr.TBit width) (TypBit width)
  | TInt (width : positive) : P4Cub_to_P4Light (Expr.TInt width) (TypInt (Npos width))
  | TError : P4Cub_to_P4Light Expr.TError TypError   
  | TTuple (types : list Expr.t) (light_types : list P_P4Type) : 
    Forall2 P4Cub_to_P4Light (types) (light_types) -> 
    P4Cub_to_P4Light (Expr.TTuple types) (TypTuple (light_types))
  | TVar (type_name : string) :
    P4Cub_to_P4Light (Expr.TVar type_name) (TypTypeName (emb_string type_name)). 

    (* embed *)
  Fixpoint P4Cub_to_P4Light_fun (c : C_P4Type) : P_P4Type:= 
    match c with
    | Expr.TBool => TypBool       
    | Expr.TBit (width) => TypBit width
    | Expr.TInt (width) => TypInt (Npos width)
    | Expr.TError => TypError   
    | Expr.TTuple (types) => TypTuple (List.map P4Cub_to_P4Light_fun types)
    | Expr.TVar (type_name) => TypTypeName (emb_string type_name)
    | _ => TypBool 
    end.

    (* project *)
  Fixpoint P4Light_to_P4Cub_fun (p : P_P4Type) : Result.result C_P4Type := 
    match p with
    | TypBool => Result.ok Expr.TBool
    | TypString => Result.error "TypString has no mapping in C_P4Type"
    | TypInteger => Result.error "TypInteger has no mapping in C_P4Type"
    | TypInt (width) => Result.ok (Expr.TInt (SyntaxUtil.pos_of_N width))
    | TypBit (width) => Result.ok (Expr.TBit (width))
    | TypVarBit (width) => Result.error "TypVarBit has no mapping in C_P4Type"
    | TypArray (typ) (size) => Result.error "TypArray has no mapping in C_P4Type"
    | TypTuple (types) => 
        let lst := sequence (List.map P4Light_to_P4Cub_fun types) in 
        Result.map Expr.TTuple lst
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
    | TypTypeName (name) => Result.ok (Expr.TVar (P4String.str name))
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
