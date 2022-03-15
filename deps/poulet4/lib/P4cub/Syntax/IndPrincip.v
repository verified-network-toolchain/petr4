Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations.
Import String Expr ExprNotations.

(** Custom induction principle for [t]. *)
Section TypeInduction.
  Local Open Scope ty_scope.
  
  (** An arbitrary property. *)
  Variable P : t -> Prop.

  Hypothesis HTVar : forall X : nat, P X.
  
  Hypothesis HTBool : P TBool.
  
  Hypothesis HTBit : forall w, P (TBit w).
  
  Hypothesis HTInt : forall w, P (TInt w).
  
  Hypothesis HTError : P TError.
  
  Hypothesis HTStruct : forall ts b,
      Forall P ts -> P (TStruct ts b).

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
      | TError       => HTError
      | TStruct ts b => HTStruct ts b (list_ind ts)
      end.
  (**[]*)
End TypeInduction.

(** A custom induction principle for [e]. *)
Section ExprInduction.
  Local Open Scope expr_scope.
  
  (** An arbitrary predicate. *)
  Variable P : e -> Prop.
  
  Hypothesis HEBool : forall b : bool, P b.
  
  Hypothesis HEBit : forall w n, P (w `W n).
  
  Hypothesis HEInt : forall w n, P (w `S n).
  
  Hypothesis HEVar : forall ty x, P (EVar ty x).
  
  Hypothesis HESlice : forall n hi lo, P n -> P (ESlice n hi lo).
  
  Hypothesis HECast : forall τ exp, P exp -> P (ECast τ exp).
  
  Hypothesis HEUop : forall rt op exp, P exp -> P (EUop rt op exp).
  
  Hypothesis HEBop : forall rt op lhs rhs,
      P lhs -> P rhs -> P (EBop rt op lhs rhs).
  
  Hypothesis HEStruct : forall fields valid,
      Forall P fields -> predop P valid -> P (EStruct fields valid).
  
  Hypothesis HEExprMember : forall rt x exp,
      P exp -> P (EMember rt x exp).
  
  Hypothesis HEError : forall err, P (EError err).
    
  (** A custom induction principle.
      Do [induction ?e using custom_e_ind]. *)
  Definition custom_e_ind : forall exp : e, P exp :=
    fix eind (expr : e) : P expr :=
      let fix list_ind (es : list e) : Forall P es :=
          match es with
          | []        => Forall_nil P
          | exp :: ees => Forall_cons exp (eind exp) (list_ind ees)
          end in
      let opind (o : option e) : predop P o :=
        match o with
        | Some exp => predop_some _ _ (eind exp)
        | None     => predop_none _
        end in
      match expr with
      | EBool b       => HEBool b
      | w `W n        => HEBit w n
      | w `S n        => HEInt w n
      | EVar ty x     => HEVar ty x
      | ESlice n h l  => HESlice n h l (eind n)
      | ECast τ exp   => HECast τ exp (eind exp)
      | EUop τ op exp => HEUop τ op exp (eind exp)
      | EBop τ op lhs rhs
        => HEBop τ op lhs rhs (eind lhs) (eind rhs)
      | EStruct fields valid
        => HEStruct fields valid (list_ind fields) (opind valid)
      | EMember rt x exp => HEExprMember rt x exp (eind exp)
      | EError err       => HEError err
      end.
  (**[]*)
End ExprInduction.

Import Parser ParserNotations.

(** A custom induction principle for select patterns. *)
Section PatternInduction.
  Local Open Scope pat_scope.
  
  Variable P : pat -> Prop.
      
  Hypothesis HWild : P PATWild.
  
  Hypothesis HMask : forall p1 p2,
      P p1 -> P p2 -> P (PATMask p1 p2).
  
  Hypothesis HRange : forall p1 p2,
      P p1 -> P p2 -> P (PATRange p1 p2).
  
  Hypothesis HBit : forall w n, P (w PW n).
  
  Hypothesis HInt : forall w n, P (w PS n).
  
  Hypothesis HStruct : forall ps,
      Forall P ps -> P (PATStruct ps).
  
  (** A customnduction principle,
      do [induction ?H using custom_pat_ind]. *)
  Definition custom_pat_ind : forall (p : pat), P p :=
    fix pind (p : pat) : P p :=
      let fix lind (ps : list pat) : Forall P ps :=
        match ps with
        | []   => Forall_nil _
        | p::ps => Forall_cons p (pind p) (lind ps)
        end in
      match p with
      | PATWild        => HWild
      | PATMask p1 p2  => HMask p1 p2 (pind p1) (pind p2)
      | PATRange p1 p2 => HRange p1 p2 (pind p1) (pind p2)
      | w PW n         => HBit w n
      | w PS z         => HInt w z
      | PATStruct ps   => HStruct ps (lind ps)
      end.
  (**[]*)
End PatternInduction.

(** A customnduction principle for parser expressions. *)
Section ParserExprInduction.
  (** An arbitrary predicate. *)
  Variable P : e -> Prop.
  
  Hypothesis HState : forall st, P (PGoto st).
  
  Hypothesis HSelect : forall exp st cases,
      Field.predfs_data P cases -> P st -> 
      P (PSelect exp st cases).
  
  (** A customnduction principle,
      do [induction ?H using pe_ind] *)
  Definition pe_ind : forall pe : e, P pe :=
    fix peind pe : P pe :=
      let fix fsind {A : Set} (es : Field.fs A e)
        : Field.predfs_data P es :=
          match es with
          | [] => Forall_nil _
          | (_,pe) as epe :: es =>
            Forall_cons epe (peind pe) (fsind es)
          end in
      match pe with
      | PGoto st => HState st
      | PSelect exp st cases
        => HSelect exp st _ (fsind cases) (peind st)
      end.
  (**[]*)
End ParserExprInduction.
