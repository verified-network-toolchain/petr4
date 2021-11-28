Require Import Poulet4.Typed Poulet4.Syntax Poulet4.Maps Coq.Lists.List.
Require Poulet4.P4String.
Import List.ListNotations.

(* TODO: inline type-declarations in p4light programs. *)

Context {tags_t : Type}.
Notation typ := (@P4Type tags_t).
Notation parameter := (@P4Parameter tags_t).
Notation lmap := map.
Notation almap := AList.map_values.
Notation omap := option_map.

Declare Scope sub_scope.
Delimit Scope sub_scope with sub.
Open Scope sub_scope.

(* TODO: how do [name]s in type names work
   with bare or qualifieds? *)
Notation substitution := (IdentMap.t typ).

Definition
  sub_default
  (σ : substitution) (X : String.string) (τ : typ) : typ :=
  match IdentMap.get X σ with
  | Some τ => τ
  | None   => τ
  end.

(** Removing names. *)
Notation "σ '∖' Xs"
  := (IdentMap.removes Xs σ)
       (at level 10, left associativity) : sub_scope.

(** [P4Type] substition. *)
Reserved Notation "σ '†t'" (at level 11, right associativity).
(** [ControlType] substitution. *)
Reserved Notation "σ '†ct'" (at level 11, right associativity).
(** [FunctionType] substition. *)
Reserved Notation "σ '†ft'" (at level 11, right associativity).
(** [P4Parameter] substitution. *)
Reserved Notation "σ '†p'" (at level 11, right associativity).
  
Fixpoint sub_typs_P4Type (σ : substitution) (τ : typ) : typ :=
  match τ with
  | TypBool
  | TypString
  | TypInteger
  | TypInt _
  | TypBit _
  | TypVarBit _
  | TypError
  | TypMatchKind
  | TypVoid
  | TypTable _              => τ
  | TypArray τ n            => TypArray (σ †t τ) n
  | TypTuple τs             => TypTuple (lmap (σ †t) τs)
  | TypList τs              => TypList  (lmap (σ †t) τs)
  | TypRecord τs            => TypRecord (almap (σ †t) τs)
  | TypStruct τs            => TypStruct (almap (σ †t) τs)
  | TypSet τ                => TypSet (σ †t τ)
  | TypHeader τs            => TypHeader (almap (σ †t) τs)
  | TypHeaderUnion τs       => TypHeaderUnion (almap (σ †t) τs)
  | TypEnum x τ mems        => TypEnum x (omap (σ †t) τ) mems
  (* TODO: correct? *)
  | TypTypeName
      (BareName T
      | QualifiedName _ T)  => sub_default σ (P4String.str T) τ
  | TypNewType x τ          => TypNewType x (σ †t τ)
  | TypControl ct           => TypControl (σ †ct ct)
  | TypParser  ct           => TypParser  (σ †ct ct)
  | TypExtern T             => sub_default σ (P4String.str T) τ
  | TypFunction ft          => TypFunction (σ †ft ft)
  | TypAction cps ps        => TypAction (lmap (σ †p) cps) (lmap (σ †p) ps)
  | TypSpecializedType τ τs => TypSpecializedType (σ †t τ) (lmap (σ †t) τs)
  | TypPackage Xs ws params
    => TypPackage Xs ws (lmap (σ ∖ (lmap P4String.str Xs) †p) params)
  | TypConstructor Xs ws ps τ
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      TypConstructor Xs ws (lmap (σ' †p) ps) (σ' †t τ)
  end
where "σ '†t'" := (sub_typs_P4Type σ) : sub_scope with
sub_typs_ControlType
  (σ : substitution) (ctrltype : ControlType) : ControlType :=
  match ctrltype with
  | MkControlType Xs params
    => MkControlType Xs (lmap (σ ∖ (lmap P4String.str Xs) †p) params)
  end
where "σ '†ct'" := (sub_typs_ControlType σ) : sub_scope with
sub_typs_FunctionType
  (σ : substitution) (functype : FunctionType) : FunctionType :=
  match functype with
  | MkFunctionType Xs params kind ret
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      MkFunctionType Xs (lmap (σ' †p) params) kind (σ' †t ret)
  end
where "σ '†ft'" := (sub_typs_FunctionType σ) : sub_scope with
sub_typs_P4Parameter
  (σ : substitution) (param : parameter) : parameter :=
  match param with
  | MkParameter b d τ def x => MkParameter b d (σ †t τ) def x
  end
where "σ '†p'" := (sub_typs_P4Parameter σ) : sub_scope.

(** [Expression] substitution. *)
Reserved Notation "σ '†e'" (at level 11, right associativity).
(** [ExpressionPreT] substitution. *)
Reserved Notation "σ '†e_pre'" (at level 11, right associativity).

Fixpoint
  sub_typs_Expression
  (σ : substitution) (e : Expression) : Expression :=
    match e with
    | MkExpression i e τ d => MkExpression i (σ †e_pre e) (σ †t τ) d
    end
where  "σ '†e'" := (sub_typs_Expression σ) with
sub_typs_ExpressionPreT
  (σ : substitution) (e : ExpressionPreT) : ExpressionPreT :=
  match e with
    | ExpBool _
    | ExpInt _
    | ExpString _
    | ExpName _ _
    | ExpTypeMember _ _ (* TODO: correct? *)
    | ExpErrorMember _
    | ExpDontCare                => e
    | ExpBitStringAccess e lo hi => ExpBitStringAccess (σ †e e) lo hi
    | ExpArrayAccess e₁ e₂       => ExpArrayAccess (σ †e e₁) (σ †e e₂)
    | ExpList es                 => ExpList (lmap (σ †e) es)
    | ExpRecord es               => ExpRecord (almap (σ †e) es)
    | ExpUnaryOp op e            => ExpUnaryOp op (σ †e e)
    | ExpBinaryOp op (e₁,e₂)     => ExpBinaryOp op (σ †e e₁, σ †e e₂)
    | ExpCast τ e                => ExpCast (σ †t τ) (σ †e e)
    | ExpExpressionMember e x    => ExpExpressionMember (σ †e e) x
    | ExpTernary e₁ e₂ e₃        => ExpTernary (σ †e e₁) (σ †e e₂) (σ †e e₃)
    | ExpFunctionCall e τs es
      => ExpFunctionCall (σ †e e) (lmap (σ †t) τs) (lmap (omap (σ †e)) es)
    | ExpNamelessInstantiation τ es
      => ExpNamelessInstantiation (σ †t τ) (lmap (σ †e) es)
  end
where  "σ '†e_pre'" := (sub_typs_ExpressionPreT σ).

Definition
  sub_typs_MethodPrototype
  (σ : substitution) (mp : MethodPrototype) : MethodPrototype :=
  match mp with
  | ProtoConstructor i x ps => ProtoConstructor i x (lmap (σ †p) ps)
  | ProtoAbstractMethod i τ x Xs ps
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      ProtoAbstractMethod i (σ' †t τ) x Xs (lmap (σ' †p) ps)
  | ProtoMethod i τ x Xs ps
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      ProtoMethod i (σ' †t τ) x Xs (lmap (σ' †p) ps)
  end.

Notation "σ '†mp'"
  := (sub_typs_MethodPrototype σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_MatchPreT
  (σ : substitution) (m : MatchPreT) : MatchPreT :=
  match m with
  | MatchDontCare    => MatchDontCare
  | MatchMask  e₁ e₂ => MatchMask  (σ †e e₁) (σ †e e₂)
  | MatchRange e₁ e₂ => MatchRange (σ †e e₁) (σ †e e₂)
  | MatchCast  τ  e  => MatchCast  (σ †t τ)  (σ †e e)
  end.

Notation "σ '†match_pre'"
  := (sub_typs_MatchPreT σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_Match
  (σ : substitution) '(MkMatch i m τ : Match) : Match :=
  MkMatch i (σ †match_pre m) (σ †t τ).

Notation "σ '†match'"
  := (sub_typs_Match σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_TablePreActionRef
  (σ : substitution)
  '(MkTablePreActionRef x es : TablePreActionRef)
  : TablePreActionRef := MkTablePreActionRef x (lmap (omap (σ †e)) es).

Notation "σ '†tar_pre'"
  := (sub_typs_TablePreActionRef σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_TableActionRef
  (σ : substitution)
  '(MkTableActionRef i ar τ : TableActionRef)
  : TableActionRef := MkTableActionRef i (σ †tar_pre ar) (σ †t τ).

Notation "σ '†tar'"
  := (sub_typs_TableActionRef σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_TableKey
  (σ : substitution) '(MkTableKey i k mk : TableKey)
  : TableKey := MkTableKey i (σ †e k) mk.

Notation "σ '†tk'"
  := (sub_typs_TableKey σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_TableEntry
  (σ : substitution) '(MkTableEntry i ms tar : TableEntry)
  : TableEntry := MkTableEntry i (lmap (σ †match) ms) (σ †tar tar).

Notation "σ '†te'"
  := (sub_typs_TableEntry σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_TableProperty
  (σ : substitution) '(MkTableProperty i b x e : TableProperty)
  : TableProperty := MkTableProperty i b x (σ †e e).

Notation "σ '†tp'"
  := (sub_typs_TableProperty σ)
       (at level 11, right associativity) : sub_scope.

(** [Statement] substitution. *)
Reserved Notation "σ '†s'" (at level 11, right associativity).
(** [StatementPreT] substitution. *)
Reserved Notation "σ '†s_pre'" (at level 11, right associativity).
(** [Block] substitution. *)
Reserved Notation "σ '†blk'" (at level 11, right associativity).
(** [StatementSwitchCase] substition. *)
Reserved Notation "σ '†switch'" (at level 11, right associativity).
(** [Initializer] substition. *)
Reserved Notation "σ '†init'" (at level 11, right associativity).

Fixpoint
  sub_typs_Statement
  (σ : substitution) (s : Statement) : Statement :=
  match s with
  | MkStatement i s τ => MkStatement i (σ †s_pre s) τ
  end
where "σ '†s'" := (sub_typs_Statement σ) with
sub_typs_StatementPreT
  (σ : substitution) (s : StatementPreT) : StatementPreT :=
  match s with
  | StatExit
  | StatEmpty               => s
  | StatAssignment e₁ e₂    => StatAssignment (σ †e e₁) (σ †e e₂)
  | StatBlock blk           => StatBlock (σ †blk blk)
  | StatReturn e            => StatReturn (omap (σ †e) e)
  | StatSwitch e scs        => StatSwitch (σ †e e) (lmap (σ †switch) scs)
  | StatConstant τ x e l    => StatConstant (σ †t τ) x (σ †e e) l
  | StatVariable τ x e l    => StatVariable (σ †t τ) x (omap (σ †e) e) l
  | StatConditional e s₁ s₂ => StatConditional (σ †e e) (σ †s s₁) (omap (σ †s) s₂)
  | StatInstantiation τ es x init
    => StatInstantiation (σ †t τ) (lmap (σ †e) es) x (lmap (σ †init) init)
  | StatDirectApplication τ es
    => StatDirectApplication (σ †t τ) (lmap (σ †e) es)
  | StatMethodCall e τs es
    => StatMethodCall (σ †e e) (lmap (σ †t) τs) (lmap (omap (σ †e)) es)
  end
where "σ '†s_pre'" := (sub_typs_StatementPreT σ) with
sub_typs_Block
  (σ : substitution) (blk : Block) : Block :=
  match blk with
  | BlockEmpty _    => blk
  | BlockCons s blk => BlockCons (σ †s s) (σ †blk blk)
  end
where "σ '†blk'" := (sub_typs_Block σ) with
sub_typs_StatementSwitchCase
  (σ : substitution)
  (sc : StatementSwitchCase) : StatementSwitchCase :=
  match sc with
  | StatSwCaseFallThrough _ _  => sc
  | StatSwCaseAction i lbl blk => StatSwCaseAction i lbl (σ †blk blk)
  end
where "σ '†switch'" := (sub_typs_StatementSwitchCase σ) with
sub_typs_Initializer
  (σ : substitution) (init : Initializer) : Initializer :=
  match init with
  | InitFunction i τ x Xs ps blk
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      InitFunction i (σ' †t τ) x Xs (lmap (σ' †p) ps) (σ' †blk blk)
  | InitInstantiation i τ es x init
    => InitInstantiation
        i (σ †t τ) (lmap (σ †e) es)
        x (lmap (σ †init) init)
  end
where "σ '†init'" := (sub_typs_Initializer σ).

Definition
  sub_typs_ParserCase
  (σ : substitution) '(MkParserCase i ms x : ParserCase)
  : ParserCase := MkParserCase i (lmap (σ †match) ms) x.

Notation "σ '†pc'"
  := (sub_typs_ParserCase σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_ParserTransition
  (σ : substitution) (pt : ParserTransition) : ParserTransition :=
  match pt with
  | ParserDirect _ _      => pt
  | ParserSelect i es pcs => ParserSelect i (lmap (σ †e) es) (lmap (σ †pc) pcs)
  end.

Notation "σ '†pt'"
  := (sub_typs_ParserTransition σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_ParserState
  (σ : substitution) '(MkParserState i x ss pt : ParserState)
  : ParserState := MkParserState i x (lmap (σ †s) ss) (σ †pt pt).

Notation "σ '†ps'"
  := (sub_typs_ParserState σ)
       (at level 11, right associativity) : sub_scope.

Definition
  sub_typs_DeclarationField
  (σ : substitution) '(MkDeclarationField i τ x : DeclarationField)
  : DeclarationField := MkDeclarationField i (σ †t τ) x.

Notation "σ '†df'"
  := (sub_typs_DeclarationField σ)
       (at level 11, right associativity) : sub_scope.

(** Inline type declarations. *)
Fixpoint
  inline_typ_decl
  (σ : substitution) (d : Declaration) {struct d}
  : substitution * option Declaration :=
  let fix itds σ ds
      : substitution * list Declaration :=
      match ds with
      | [] => (σ, [])
      | d :: ds
        => let '(σ',dio) := inline_typ_decl σ d in
          let (σ'', ds') := itds σ' ds in
          (σ'', match dio with
                | Some d' => [d']
                | None    => []
                end ++ ds')
      end in
  match d with
  | DeclConstant i τ x e => (σ, Some (DeclConstant i (σ †t τ) x (σ †e e)))
  | DeclInstantiation i τ es x ds
    => (* TODO: Are type declarations in [ds] in scope? *)
    let '(σ', ds') := itds σ ds in
    (σ', Some (DeclInstantiation i (σ †t τ) (lmap (σ †e) es) x ds'))
  | DeclParser i x [] ps cps ds states
    => let '(σ', ds') := itds σ ds in
      (σ,
       Some
         (DeclParser
            i x [] (lmap (σ †p) ps)
            (lmap (σ †p) cps) ds' (lmap (σ †ps) states)))
  | DeclControl i x [] ps cps ds blk
    => let '(σ', ds') := itds σ ds in
      (σ,
       Some
         (DeclControl
            i x [] (lmap (σ †p) ps)
            (lmap (σ †p) cps) ds' (σ' †blk blk)))
  | DeclFunction i τ x Xs ps blk
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      (σ,
       Some
         (DeclFunction
            i (σ' †t τ) x Xs (lmap (σ' †p) ps) (σ' †blk blk)))
  | DeclExternFunction i τ x Xs ps
    => let σ' := σ ∖ (lmap P4String.str Xs) in
      (σ,
       Some
         (DeclExternFunction
            i (σ' †t τ) x Xs (lmap (σ' †p) ps)))
  | DeclVariable i τ x e
    => (σ, Some (DeclVariable i (σ †t τ) x (omap (σ †e) e)))
  | DeclValueSet i τ n x
    => (σ, Some (DeclValueSet i (σ †t τ) n x))
  | DeclAction i x ps cps blk
    => (σ,
       Some
         (DeclAction
            i x (lmap (σ †p) ps) (lmap (σ †p) ps) (σ †blk blk)))
  | DeclTable i x k tars tes dtar n tps
    => (σ,
       Some
         (DeclTable
            i x (lmap (σ †tk) k) (lmap (σ †tar) tars)
            (omap (lmap (σ †te)) tes)
            (omap (σ †tar) dtar) n (lmap (σ †tp) tps)))
  | _ => (σ, None)
  end.
