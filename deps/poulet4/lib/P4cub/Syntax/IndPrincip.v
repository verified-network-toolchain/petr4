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
  Import Expr ExprNotations.
  Local Open Scope expr_scope.
  
  (** An arbitrary predicate. *)
  Variable P : e -> Prop.
  
  Hypothesis HBool : forall b : bool, P b.
  
  Hypothesis HBit : forall w n, P (w `W n).
  
  Hypothesis HInt : forall w n, P (w `S n).
  
  Hypothesis HVar : forall ty x, P (Var ty x).
  
  Hypothesis HSlice : forall n hi lo, P n -> P (Slice n hi lo).
  
  Hypothesis HCast : forall τ exp, P exp -> P (Cast τ exp).
  
  Hypothesis HUop : forall rt op exp, P exp -> P (Uop rt op exp).
  
  Hypothesis HBop : forall rt op lhs rhs,
      P lhs -> P rhs -> P (Bop rt op lhs rhs).
  
  Hypothesis HStruct : forall fields valid,
      Forall P fields -> P (Struct fields valid).
  
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
      | Var ty x     => HVar ty x
      | Slice n h l  => HSlice n h l (eind n)
      | Cast τ exp   => HCast τ exp (eind exp)
      | Uop τ op exp => HUop τ op exp (eind exp)
      | Bop τ op lhs rhs
        => HBop τ op lhs rhs (eind lhs) (eind rhs)
      | Struct fields valid
        => HStruct fields valid (list_ind fields)
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
  
  Hypothesis HStruct : forall ps,
      Forall P ps -> P (Struct ps).
  
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
      | Struct ps   => HStruct ps (lind ps)
      end.
End PatternInduction.
