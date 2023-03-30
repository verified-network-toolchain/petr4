Require Import Coq.PArith.BinPosDef Coq.PArith.BinPos
        Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Import Poulet4.P4cub.Syntax.AST
        Poulet4.P4cub.Syntax.CubNotations.
Import String.

(** Custom induction principle for [Typ.t]. *)
Section TypInduction.
  Import Typ.
  Local Open Scope typ_scope.
  
  (** An arbitrary property. *)
  Variable P : t -> Prop.

  Hypothesis HVar : forall X : nat, P (Var X).
  
  Hypothesis HBool : P Bool.
  
  Hypothesis HBit : forall w, P (Bit w).
  
  Hypothesis HInt : forall w, P (Int w).

  Hypothesis HVarBit : forall w, P (VarBit w).
  
  Hypothesis HError : P Error.

  Hypothesis HArray : forall n typ, P typ -> P (Array n typ).
  
  Hypothesis HStruct : forall b ts,
      Forall P ts -> P (Struct b ts).

  (** A custom induction principle.
      Do [induction ?t using custom_typ_ind]. *)
  Definition custom_typ_ind : forall τ : t, P τ :=
    fix tind (τ : t) : P τ :=
      match τ with
      | Var X       => HVar X
      | Bool        => HBool
      | Bit w       => HBit w
      | Int w       => HInt w
      | VarBit w    => HVarBit w
      | Error       => HError
      | Array n typ => HArray n _ (tind typ)
      | Struct b ts =>
          HStruct b ts
            (list_ind
               (Forall P) (Forall_nil _)
               (fun τ _ => Forall_cons _ (tind τ)) ts)
      end.
End TypInduction.

(** A custom induction principle for [Exp.t]. *)
Section ExpInduction.
  Import Exp.
  Local Open Scope exp_scope.
  
  (** An arbitrary predicate. *)
  Variable P : t -> Prop.
  
  Hypothesis HBool : forall b : bool, P (Bool b).
  
  Hypothesis HBit : forall w n, P (w `W n).
  
  Hypothesis HInt : forall w n, P (w `S n).

  Hypothesis HVarBit : forall m w n, P (VarBit m w n).
  
  Hypothesis HVar : forall ty og x, P (Var ty og x).
  
  Hypothesis HSlice : forall hi lo n, P n -> P (Slice hi lo n).
  
  Hypothesis HCast : forall τ e, P e -> P (Cast τ e).
  
  Hypothesis HUop : forall rt op e, P e -> P (Uop rt op e).
  
  Hypothesis HBop : forall rt op lhs rhs,
      P lhs -> P rhs -> P (Bop rt op lhs rhs).

  Hypothesis HLists : forall l es,
      Forall P es -> P (Lists l es).

  Hypothesis HIndex : forall typ arr index,
      P arr -> P index -> P (Index typ arr index).
  
  Hypothesis HMember : forall rt x e,
      P e -> P (Member rt x e).
  
  Hypothesis HError : forall err, P (Error err).
    
  (** A custom induction principle.
      Do [induction ?e using custom_exp_ind]. *)
  Definition custom_exp_ind : forall e : t, P e :=
    fix eind (e : t) : P e :=
      match e with
      | Bool b       => HBool b
      | w `W n       => HBit w n
      | w `S n       => HInt w n
      | VarBit m w n => HVarBit m w n
      | Var ty og x  => HVar ty og x
      | Slice h l n  => HSlice h l n (eind n)
      | Cast τ e     => HCast τ e (eind e)
      | Uop τ op e   => HUop τ op e (eind e)
      | Bop τ op lhs rhs
        => HBop τ op lhs rhs (eind lhs) (eind rhs)
      | Lists l es
        => HLists
            l es
            (list_ind
               (Forall P)
               (Forall_nil _)
               (fun e _ => Forall_cons _ (eind e)) es)
      | Index typ arr index => HIndex typ _ _ (eind arr) (eind index)
      | Member rt x e => HMember rt x e (eind e)
      | Error err     => HError err
      end.
End ExpInduction.

(** A custom induction principle for select patterns. *)
Section PatternInduction.
  Import Pat.
  Local Open Scope pat_scope.
  
  Variable P : t -> Prop.
      
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
  Definition custom_pat_ind : forall (p : t), P p :=
    fix pind (p : t) : P p :=
      match p with
      | Wild        => HWild
      | Mask p1 p2  => HMask p1 p2 (pind p1) (pind p2)
      | Range p1 p2 => HRange p1 p2 (pind p1) (pind p2)
      | w PW n      => HBit w n
      | w PS z      => HInt w z
      | Lists ps    =>
          HLists
            ps
            (list_ind
               (Forall P)
               (Forall_nil _)
               (fun p _ => Forall_cons _ (pind p)) ps)
      end.
End PatternInduction.
