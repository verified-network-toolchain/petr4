Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations.
Import String.

(** Custom induction principle for [t]. *)
Section TypeInduction.
  Import Expr ExprNotations.
  Local Open Scope ty_scope.
  
  (** An arbitrary property. *)
  Variable P : t -> Prop.

  Hypothesis HTVar : forall X : nat, P X.
  
  Hypothesis HTBool : P TBool.
  
  Hypothesis HTBit : forall w, P (TBit w).
  
  Hypothesis HTInt : forall w, P (TInt w).

  Hypothesis HTVarBit : forall w, P (TVarBit w).
  
  Hypothesis HTError : P TError.

  Hypothesis HTArray : forall n typ, P typ -> P (TArray n typ).
  
  Hypothesis HTStruct : forall b ts,
      Forall P ts -> P (TStruct b ts).

  (** A custom induction principle.
      Do [induction ?t using custom_t_ind]. *)
  Definition custom_t_ind : forall ty : t, P ty :=
    fix custom_t_ind (type : t) : P type :=
      let fix list_ind ts :
            Forall P ts :=
        match ts with
        | []     => Forall_nil _
        | h :: ts => Forall_cons _ (custom_t_ind h) (list_ind ts)
        end in
      match type with
      | TVar X       => HTVar X
      | TBool        => HTBool
      | TBit w       => HTBit w
      | TInt w       => HTInt w
      | TVarBit w    => HTVarBit w
      | TError       => HTError
      | TArray n typ => HTArray n _ (custom_t_ind typ)
      | TStruct b ts => HTStruct b ts (list_ind ts)
      end.
  (**[]*)
End TypeInduction.

(** A custom induction principle for [e]. *)
Section ExprInduction.
  Import Expr ExprNotations.
  Local Open Scope expr_scope.
  
  (** An arbitrary predicate. *)
  Variable P : e -> Prop.
  
  Hypothesis HBool : forall b : bool, P b.
  
  Hypothesis HBit : forall w n, P (w `W n).
  
  Hypothesis HInt : forall w n, P (w `S n).

  Hypothesis HVarBit : forall m w n, P (VarBit m w n).
  
  Hypothesis HVar : forall ty og x, P (Var ty og x).
  
  Hypothesis HSlice : forall hi lo n, P n -> P (Slice hi lo n).
  
  Hypothesis HCast : forall τ exp, P exp -> P (Cast τ exp).
  
  Hypothesis HUop : forall rt op exp, P exp -> P (Uop rt op exp).
  
  Hypothesis HBop : forall rt op lhs rhs,
      P lhs -> P rhs -> P (Bop rt op lhs rhs).

  Hypothesis HLists : forall l exps,
      Forall P exps -> P (Lists l exps).

  Hypothesis HIndex : forall typ arr index,
      P arr -> P index -> P (Index typ arr index).
  
  Hypothesis HMember : forall rt x exp,
      P exp -> P (Member rt x exp).
  
  Hypothesis HError : forall err, P (Error err).
    
  (** A custom induction principle.
      Do [induction ?e using custom_e_ind]. *)
  Definition custom_e_ind : forall exp : e, P exp :=
    fix eind (expr : e) : P expr :=
      let fix list_ind (es : list e) : Forall P es :=
          match es with
          | []        => Forall_nil P
          | exp :: ees => Forall_cons exp (eind exp) (list_ind ees)
          end in
      match expr with
      | Bool b       => HBool b
      | w `W n       => HBit w n
      | w `S n       => HInt w n
      | VarBit m w n => HVarBit m w n
      | Var ty og x  => HVar ty og x
      | Slice h l n  => HSlice h l n (eind n)
      | Cast τ exp   => HCast τ exp (eind exp)
      | Uop τ op exp => HUop τ op exp (eind exp)
      | Bop τ op lhs rhs
        => HBop τ op lhs rhs (eind lhs) (eind rhs)
      | Lists l exps => HLists l exps (list_ind exps)
      | Index typ arr index => HIndex typ _ _ (eind arr) (eind index)
      | Member rt x exp => HMember rt x exp (eind exp)
      | Error err       => HError err
      end.
End ExprInduction.

(** A custom induction principle for select patterns. *)
Section PatternInduction.
  Import Parser ParserNotations.
  Local Open Scope pat_scope.
  
  Variable P : pat -> Prop.
      
  Hypothesis HWild : P Wild.
  
  Hypothesis HMask : forall p1 p2,
      P p1 -> P p2 -> P (Mask p1 p2).
  
  Hypothesis HRange : forall p1 p2,
      P p1 -> P p2 -> P (Range p1 p2).
  
  Hypothesis HBit : forall w n, P (w PW n).
  
  Hypothesis HInt : forall w n, P (w PS n).
  
  Hypothesis HLists : forall ps,
      Forall P ps -> P (Lists ps).
  
  (** A custom induction principle,
      do [induction ?H using custom_pat_ind]. *)
  Definition custom_pat_ind : forall (p : pat), P p :=
    fix pind (p : pat) : P p :=
      let fix lind (ps : list pat) : Forall P ps :=
        match ps with
        | []   => Forall_nil _
        | p::ps => Forall_cons p (pind p) (lind ps)
        end in
      match p with
      | Wild        => HWild
      | Mask p1 p2  => HMask p1 p2 (pind p1) (pind p2)
      | Range p1 p2 => HRange p1 p2 (pind p1) (pind p2)
      | w PW n      => HBit w n
      | w PS z      => HInt w z
      | Lists ps    => HLists ps (lind ps)
      end.
End PatternInduction.
