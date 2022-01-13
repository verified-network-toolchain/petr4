Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Require Import Poulet4.Info.
Require Import Poulet4.Typed.
Require Poulet4.P4String.
Require Poulet4.P4Int.
Require Import Poulet4.Utils.
Require Import Poulet4.Syntax.

Inductive OptForall {A: Type} (P: A -> Prop): list (option A) -> Prop :=
| OptForall_nil: OptForall P nil
| OptForall_cons_None: forall (l: list (option A)),
    OptForall P l -> OptForall P (None :: l)
| OptForall_cons_Some: forall (x: A) (l: list (option A)),
    P x -> OptForall P l -> OptForall P (Some x :: l).

Section ExprInd.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation Expression := (@Expression tags_t).
  Notation ExpressionPreT := (@ExpressionPreT tags_t).

  Variable Pe: Expression -> Prop.
  Variable Pt: ExpressionPreT -> Prop.

  Hypothesis HExpression: forall t exp typ dir,
      Pt exp -> Pe (MkExpression t exp typ dir).
  Hypothesis HBool: forall b, Pt (ExpBool b).
  Hypothesis HInt: forall i, Pt (ExpInt i).
  Hypothesis HString: forall s, Pt (ExpString s).
  Hypothesis HName: forall n l, Pt (ExpName n l).
  Hypothesis HArrayAccess:
    forall ary idx, Pe ary -> Pe idx -> Pt (ExpArrayAccess ary idx).
  Hypothesis HBitStringAccess:
    forall bits lo hi, Pe bits -> Pt (ExpBitStringAccess bits lo hi).
  Hypothesis HList: forall vs, Forall Pe vs -> Pt (ExpList vs).
  Hypothesis HRecord: forall es, Forall (fun '(_,v) => Pe v) es -> Pt (ExpRecord es).
  Hypothesis HUnaryOp: forall op arg, Pe arg -> Pt (ExpUnaryOp op arg).
  Hypothesis HBinaryOp: forall op args,
      Pe (fst args) -> Pe (snd args) -> Pt (ExpBinaryOp op args).
  Hypothesis HCast: forall typ expr, Pe expr -> Pt (ExpCast typ expr).
  Hypothesis HTypeMember: forall typ name, Pt (ExpTypeMember typ name).
  Hypothesis HErrorMember: forall n, Pt (ExpErrorMember n).
  Hypothesis HExpressionMember: forall exp name,
      Pe exp -> Pt (ExpExpressionMember exp name).
  Hypothesis HTernary: forall cond tru fls,
      Pe cond -> Pe tru -> Pe fls -> Pt (ExpTernary cond tru fls).
  Hypothesis HFunctionCall: forall func type_args args,
      Pe func -> OptForall Pe args -> Pt (ExpFunctionCall func type_args args).
  Hypothesis HNamelessInstantiation: forall typ args,
      Forall Pe args -> Pt (ExpNamelessInstantiation typ args).
  Hypothesis HDontCare: Pt ExpDontCare.

  Fixpoint custom_ExpressionPreT_ind (e: ExpressionPreT): Pt e :=
    let fix lind (vs: list Expression): Forall Pe vs :=
      match vs with
      | nil => Forall_nil _
      | v :: rest => Forall_cons _ (custom_Expression_ind v) (lind rest)
      end in
    let fix alind (vs: P4String.AList tags_t Expression):
      Forall (fun '(_, v)=> Pe v) vs :=
      match vs with
      | nil => Forall_nil _
      | (_, v) as xv :: rest => Forall_cons xv (custom_Expression_ind v) (alind rest)
      end in
    let fix olind (vs: list (option Expression)): OptForall Pe vs :=
      match vs with
      | nil => OptForall_nil _
      | None :: rest => OptForall_cons_None _ _ (olind rest)
      | Some x :: rest => OptForall_cons_Some _ _ _ (custom_Expression_ind x)
                                              (olind rest)
      end in
    match e with
    | ExpBool b => HBool b
    | ExpInt i => HInt i
    | ExpString s => HString s
    | ExpName n l => HName n l
    | ExpArrayAccess ary idx =>
        HArrayAccess ary idx (custom_Expression_ind ary) (custom_Expression_ind idx)
    | ExpBitStringAccess bits lo hi =>
        HBitStringAccess bits lo hi (custom_Expression_ind bits)
    | ExpList vs => HList vs (lind vs)
    | ExpRecord es => HRecord es (alind es)
    | ExpUnaryOp op e => HUnaryOp op e (custom_Expression_ind e)
    | ExpBinaryOp op args => HBinaryOp op args (custom_Expression_ind (fst args))
                                       (custom_Expression_ind (snd args))
    | ExpCast typ exp => HCast typ exp (custom_Expression_ind exp)
    | ExpTypeMember s1 s2 => HTypeMember s1 s2
    | ExpErrorMember s => HErrorMember s
    | ExpExpressionMember exp s => HExpressionMember exp s (custom_Expression_ind exp)
    | ExpTernary cond tru fls => HTernary cond tru fls
                                          (custom_Expression_ind cond)
                                          (custom_Expression_ind tru)
                                          (custom_Expression_ind fls)
    | ExpFunctionCall func type_args args =>
        HFunctionCall func type_args args (custom_Expression_ind func) (olind args)
    | ExpNamelessInstantiation typ args =>
        HNamelessInstantiation typ args (lind args)
    | ExpDontCare => HDontCare
    end
    with
    custom_Expression_ind (e: Expression) : Pe e :=
      match e with
      | MkExpression t exp typ dir =>
          HExpression t exp typ dir (custom_ExpressionPreT_ind exp)
      end.

End ExprInd.
