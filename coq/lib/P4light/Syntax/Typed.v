From Coq Require Import Numbers.BinNums Classes.EquivDec.
From Poulet4.P4light.Syntax Require P4String P4Int.

Section Typed.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).

  Inductive name :=
  | BareName (name: P4String)
  | QualifiedName (namespaces: list P4String) (name: P4String).

  Inductive direction :=
  | In
  | Out
  | InOut
  | Directionless.

  Definition eq_dir (d1 d2: direction) :=
    match d1, d2 with
    | In, In
    | Out, Out
    | InOut, InOut
    | Directionless, Directionless => true
    | _, _ => false
    end.

  Inductive FunctionKind :=
  | FunParser
  | FunControl
  | FunExtern
  | FunTable
  | FunAction
  | FunFunction
  | FunBuiltin.

  Inductive P4Type :=
  | TypBool
  | TypString
  | TypInteger
  | TypInt (width: N)
  | TypBit (width: N)
  | TypVarBit (width: N)
  | TypArray (typ: P4Type) (size: N)
  | TypTuple (types: list P4Type)
  | TypList (types: list P4Type)
  | TypRecord (fields: P4String.AList tags_t P4Type)
  | TypSet (elt_type: P4Type)
  | TypError
  | TypMatchKind
  | TypVoid
  | TypHeader (fields: P4String.AList tags_t P4Type)
  | TypHeaderUnion (fields: P4String.AList tags_t P4Type)
  | TypStruct (fields: P4String.AList tags_t P4Type)
  | TypEnum (name: P4String) (typ: option P4Type) (members: list P4String)
  | TypTypeName (name: P4String)
  | TypNewType (name: P4String) (typ: P4Type)
  | TypControl (_: ControlType)
  | TypParser (_: ControlType)
  | TypExtern (extern_name: P4String)
  | TypFunction (fn: FunctionType)
  | TypAction (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
  | TypTable (result_typ_name: P4String)
  | TypPackage (type_params: list P4String) (wildcard_params: list P4String)
               (parameters: list P4Parameter)
  | TypSpecializedType (base: P4Type) (args: list P4Type)
  | TypConstructor (type_params: list P4String) (wildcard_params: list P4String)
                   (parameters: list P4Parameter) (ret: P4Type)
  with ControlType :=
  | MkControlType (type_params: list P4String) (parameters: list P4Parameter)
  with FunctionType :=
  | MkFunctionType (type_params: list P4String) (parameters: list P4Parameter)
                   (kind: FunctionKind) (ret: P4Type)
  with P4Parameter :=
  | MkParameter (opt: bool) (direction: direction) (typ: P4Type) (default_arg_id: option N) (variable: P4String).

  Inductive StmType :=
  | StmUnit
  | StmVoid.

  Inductive StmtContext :=
  | StmtCxMethod (ret: P4Type)
  | StmtCxFunction (ret: P4Type)
  | StmtCxAction
  | StmtCxParserState
  | StmtCxApplyBlock.

  Inductive DeclContext :=
  | DeclCxTopLevel
  | DeclCxNested
  | DeclCxStatement (_: StmtContext).

  Inductive ParamContextDeclaration :=
  | ParamCxDeclParser
  | ParamCxDeclControl
  | ParamCxDeclMethod
  | ParamCxDeclAction
  | ParamCxDeclFunction
  | ParamCxDeclPackage.

  Inductive ParamContext :=
  | ParamCxRuntime (_: ParamContextDeclaration)
  | ParamCxConstructor (_: ParamContextDeclaration).

  Inductive ExprContext :=
  | ExprCxParserState
  | ExprCxApplyBlock
  | ExprCxDeclLocals
  | ExprCxTableAction
  | ExprCxAction
  | ExprCxMethod
  | ExprCxFunction
  | ExprCxConstant.

End Typed.

Require Import Coq.Lists.List.
Import ListNotations.
Require Poulet4.Utils.Util.EquivUtil.

Section P4TypeInd.
  Variable tags_t : Type.

  Notation typ := (@P4Type tags_t).
  Notation ctrltyp := (@ControlType tags_t).
  Notation funtyp := (@FunctionType tags_t).
  Notation param := (@P4Parameter tags_t).

  Variables (P : typ -> Prop) (Q : ctrltyp -> Prop) (R : funtyp -> Prop) (S : param -> Prop).
  
  Hypothesis HBool : P TypBool.
  Hypothesis HStr : P TypString.
  Hypothesis HInteger : P TypInteger.
  Hypothesis HInt : forall w, P (TypInt w).
  Hypothesis HBit : forall w, P (TypBit w).
  Hypothesis HVarbit : forall w, P (TypVarBit w).
  Hypothesis HArray : forall t n, P t -> P (TypArray t n).
  Hypothesis HTuple : forall ts,
      Forall P ts -> P (TypTuple ts).
  Hypothesis HList : forall ts,
      Forall P ts -> P (TypList ts).
  Hypothesis HRecord : forall xts,
      Forall (fun xt => P (snd xt)) xts -> P (TypRecord xts).
  Hypothesis HSet : forall t, P t -> P (TypSet t).
  Hypothesis HError : P TypError.
  Hypothesis HMatchkind : P TypMatchKind.
  Hypothesis HVoid : P TypVoid.
  Hypothesis HHeader : forall xts,
      Forall (fun xt => P (snd xt)) xts -> P (TypHeader xts).
  Hypothesis HUnion : forall xts,
      Forall (fun xt => P (snd xt)) xts -> P (TypHeaderUnion xts).
  Hypothesis HStruct : forall xts,
      Forall (fun xt => P (snd xt)) xts -> P (TypStruct xts).
  Hypothesis HEnum : forall X t ms,
      EquivUtil.predop P t -> P (TypEnum X t ms).
  Hypothesis HName : forall X, P (TypTypeName X).
  Hypothesis HNew : forall X t,
      P t -> P (TypNewType X t).
  Hypothesis HControl : forall ct, Q ct -> P (TypControl ct).
  Hypothesis HParser : forall ct, Q ct -> P (TypParser ct).
  Hypothesis HExtern : forall X, P (TypExtern X).
  Hypothesis HFunction : forall ft,
      R ft -> P (TypFunction ft).
  Hypothesis HAction : forall ds cs,
      Forall S ds -> Forall S cs -> P (TypAction ds cs).
  Hypothesis HTable : forall X, P (TypTable X).
  Hypothesis HPackage : forall Xs ws ps,
      Forall S ps -> P (TypPackage Xs ws ps).
  Hypothesis HSpecialized : forall t ts,
      Forall P ts -> P t -> P (TypSpecializedType t ts).
  Hypothesis HConstructor : forall Xs ws ps t,
      Forall S ps -> P t -> P (TypConstructor Xs ws ps t).
  Hypothesis HControlType : forall Xs ps,
      Forall S ps -> Q (MkControlType Xs ps).
  Hypothesis HFunctionType : forall Xs ps k t,
      Forall S ps -> P t -> R (MkFunctionType Xs ps k t).
  Hypothesis HParam : forall b d t n x,
      P t -> S (MkParameter b d t n x).

  Fixpoint my_P4Type_ind (t : typ) : P t :=
    let fix L ts : Forall P ts :=
        match ts with
        | []     => Forall_nil _
        | t :: ts => Forall_cons t (my_P4Type_ind t) (L ts)
        end in
    let fix AL xts : Forall (fun xt => P (snd xt)) xts :=
        match xts with
        | []                  => Forall_nil _
        | ((_,t) as xt) :: xts => Forall_cons xt (my_P4Type_ind t) (AL xts)
        end in
    let PO to : EquivUtil.predop P to :=
        match to with
        | Some t => EquivUtil.predop_some _ t (my_P4Type_ind t)
        | None   => EquivUtil.predop_none _
        end in
    let fix PL ps : Forall S ps :=
        match ps with
        | []     => Forall_nil _
        | p :: ps => Forall_cons p (my_P4Parameter_ind p) (PL ps)
        end in
    match t with
    | TypBool      => HBool
    | TypString    => HStr
    | TypInteger   => HInteger
    | TypInt w     => HInt w
    | TypBit w     => HBit w
    | TypVarBit w  => HVarbit w
    | TypArray t n => HArray t n (my_P4Type_ind t)
    | TypTuple ts  => HTuple ts (L ts)
    | TypList  ts  => HList  ts (L ts)
    | TypSet t     => HSet t (my_P4Type_ind t)
    | TypError     => HError
    | TypVoid      => HVoid
    | TypMatchKind => HMatchkind
    | TypRecord      ts => HRecord ts (AL ts)
    | TypHeader      ts => HHeader ts (AL ts)
    | TypHeaderUnion ts => HUnion  ts (AL ts)
    | TypStruct      ts => HStruct ts (AL ts)
    | TypEnum X t ms    => HEnum X t ms (PO t)
    | TypTypeName X     => HName X
    | TypNewType  X t   => HNew X t (my_P4Type_ind t)
    | TypControl ct     => HControl ct (my_ControlType_ind ct)
    | TypParser  ct     => HParser  ct (my_ControlType_ind ct)
    | TypExtern  X      => HExtern X
    | TypFunction ft    => HFunction ft (my_FunctionType_ind ft)
    | TypAction ds cs   => HAction ds cs (PL ds) (PL cs)
    | TypTable X        => HTable X
    | TypPackage Xs ws ps       => HPackage Xs ws ps (PL ps)
    | TypSpecializedType t ts   => HSpecialized t ts (L ts) (my_P4Type_ind t)
    | TypConstructor Xs ws ps t => HConstructor Xs ws ps t (PL ps) (my_P4Type_ind t)
    end
  with my_ControlType_ind (ct : ctrltyp) : Q ct :=
         let fix PL ps : Forall S ps :=
             match ps with
             | []     => Forall_nil _
             | p :: ps => Forall_cons p (my_P4Parameter_ind p) (PL ps)
             end in
         match ct with
         | MkControlType Xs ps => HControlType Xs ps (PL ps)
         end
  with my_FunctionType_ind (ft : funtyp) : R ft :=
         let fix PL ps : Forall S ps :=
             match ps with
             | []     => Forall_nil _
             | p :: ps => Forall_cons p (my_P4Parameter_ind p) (PL ps)
             end in
         match ft with
         | MkFunctionType Xs ps k t
           => HFunctionType Xs ps k t (PL ps) (my_P4Type_ind t)
         end
  with my_P4Parameter_ind (p : param) : S p :=
         match p with
         | MkParameter b d t n x => HParam b d t n x (my_P4Type_ind t)
         end.
End P4TypeInd.
