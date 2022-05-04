Require Export Coq.Strings.String
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4light.Syntax.Value
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
        Poulet4.Utils.ForallMap
        Poulet4.Utils.Utils Poulet4.Utils.P4Arith
        Poulet4.Monads.Monad.
Require Poulet4.P4light.Syntax.P4String.
Require Import Poulet4.P4cub.Syntax.CubNotations.
Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.
Import AllCubNotations Val.ValueNotations.
Import Poulet4.P4light.Syntax.Typed.
Local Open Scope string_scope.

(** Embeding [p4cub] values in [p4light] values. *)
Section Embed.
  Context {tags_t: Type}. 
  Context {dummy_tags: tags_t}. 
  Context {string_list: list string}.
  Notation VAL := (@ValueBase bool).
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
    | h::t => ((string_of_index index), h) :: make_assoc_list index t
  end.

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
    Forall2 P4Cub_to_P4Light (types) (light_types) -> 
    P4Cub_to_P4Light (Expr.TStruct types false) (TypStruct (List.map (prod_map_l emb_string) (make_assoc_list 0 light_types)))
  | TStruct_header (types : list Expr.t) (light_types : list P_P4Type) : 
    Forall2 P4Cub_to_P4Light types light_types -> 
    P4Cub_to_P4Light (Expr.TStruct types true) (TypHeader (List.map (prod_map_l emb_string) (make_assoc_list 0 light_types))) 
  | TVar (type_name : string) :
    (* if (string_to_int type_name 0 string_list) == None then P4Cub_to_P4Light Expr.TError TypError
    else  *)
    P4Cub_to_P4Light (Expr.TVar (get_int (string_to_int type_name 0 string_list))) (TypTypeName (emb_string type_name)). 

    (* embed *)
  Fixpoint P4Cub_to_P4Light_fun (c : C_P4Type) : P_P4Type:= 
    match c with
    | Expr.TBool => TypBool       
    | Expr.TBit (width) => TypBit width
    | Expr.TInt (width) => TypInt (Npos width)
    | Expr.TError => TypError   
    | Expr.TStruct types true => TypStruct (List.map (prod_map_l emb_string) (make_assoc_list 0 (List.map P4Cub_to_P4Light_fun types)))
    | Expr.TStruct types false => TypHeader (List.map (prod_map_l emb_string) (make_assoc_list 0 (List.map P4Cub_to_P4Light_fun types)))
    | Expr.TVar (type_name) => TypTypeName (emb_string (nth type_name string_list ""))
    end.


    (* project *)
  Fixpoint P4Light_to_P4Cub_fun (p : P_P4Type) : Result.result string C_P4Type := 
    match p with
    | TypBool => Result.ok Expr.TBool
    | TypString => Result.error "TypString has no mapping in C_P4Type"
    | TypInteger => Result.error "TypInteger has no mapping in C_P4Type"
    | TypInt (width) => Result.ok (Expr.TInt (SyntaxUtil.pos_of_N width))
    | TypBit (width) => Result.ok (Expr.TBit (width))
    | TypVarBit (width) => Result.error "TypVarBit has no mapping in C_P4Type"
    | TypArray (typ) (size) => Result.error "TypArray has no mapping in C_P4Type"
    | TypTuple (types) => 
        let^ lst := sequence (List.map P4Light_to_P4Cub_fun types) in 
        Expr.TStruct lst false
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
  | Embed_tuple vs vs' :
      Forall2 Embed vs vs' ->
      Embed (Val.Struct vs None) (ValBaseTuple vs')
  | Embed_header vs vs' b :
      Forall2 Embed vs (map snd vs') ->
      Embed (Val.Struct (vs) (Some b)) (ValBaseHeader vs' b)
  | Embed_error eo er :
      match eo with
      | Some err => err 
      | None     => "no error"%string
      end = er ->
      Embed (Val.Error eo) (ValBaseError er).

  Fixpoint embed (v : Val.v) : VAL :=
    match v with
    | Val.Bool b => ValBaseBool b
    | Val.Bit w n => ValBaseBit $ to_lbool w n
    | Val.Int w z  => ValBaseInt $ to_lbool (Npos w) z
    | Val.Struct (vs) (Some b)     => ValBaseHeader (make_assoc_list 0 (List.map embed vs)) b
    | Val.Struct (vs) (None)     => ValBaseStruct (make_assoc_list 0 (List.map embed vs))
    | Val.Error (Some v)  => ValBaseError v
    | Val.Error (None) => ValBaseError "no error"
    (* why does val error have an option - why None option? *)
    end.

    Fixpoint snd_map {A : Type} {B : Type} (func : A -> B) (l : list (string * A)) :=
      match l with 
      | [] => []
      | (_, h)::t => func h :: snd_map func t
      end.

    Fixpoint proj (v : VAL) : Val.v :=
      match v with
      | ValBaseBool b => Val.Bool b
      | ValBaseInt lb => let (w, n) := IntArith.from_lbool lb in 
        Val.Int (Z.to_pos n) (Z.of_N w) 
      | ValBaseNull => Val.Error (None)
      | ValBaseBit lb => let (w, n) := IntArith.from_lbool lb in 
        Val.Bit w n 
      | ValBaseStruct s => Val.Struct (map (fun '(_,v) => proj v) s) None
      | ValBaseHeader s b => Val.Struct (map (fun '(_,v) => proj v) s) (Some b)
      | ValBaseError e => Val.Error (Some e)
      | ValBaseInteger _ => Val.Error (Some ("No mapping for ValBaseInteger exists"))
      | ValBaseVarbit _ _ => Val.Error (Some ("No mapping for ValBaseVarbit exists"))
      | ValBaseString _ => Val.Error (Some ("No mapping for ValBaseString exists"))
      | ValBaseTuple _ => Val.Error (Some ("No mapping for ValBaseTuple exists"))
      | ValBaseMatchKind _ => Val.Error (Some ("No mapping for ValBaseMatchKind exists"))
      | ValBaseUnion _ => Val.Error (Some ("No mapping for ValBaseUnion exists"))
      | ValBaseStack _ _ => Val.Error (Some ("No mapping for ValBaseStack exists"))
      | ValBaseEnumField _ _ => Val.Error (Some ("No mapping for ValBaseEnumField exists"))
      | ValBaseSenumField _ _ => Val.Error (Some ("No mapping for ValBaseSenumField exists"))
      end.
      (* add back result.ok and result.errro *)

  Local Hint Constructors Embed : core.
  
  Lemma embed_Embed : forall v, Embed v (embed v).
  Proof.
    intro v; induction v using custom_v_ind;
      unravel in *; auto.
    - destruct ob. 
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

(* E2E proof for types 
Forall (t : p4cub_type), p4light_to_p4cub (p4cub_to_p4light t) = Some t. 

E2E proof for values  *)

(* In Semantics.v In bigstep, we will use these functions *)

(* proof for embed -> project you get OK and it's the identity *)

(* project -> embed 
projectable v ==> proj v = ok c and embed c = v *)

(* issueL project embed proof fails because of the picture -- needs to sort to fix this issue. 
can prove project embed is ok, but can't't prove that it is identity  *)