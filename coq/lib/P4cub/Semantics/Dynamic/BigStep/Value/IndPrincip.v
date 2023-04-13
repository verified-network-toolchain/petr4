From Poulet4 Require Import
     P4cub.Semantics.Dynamic.BigStep.Value.Syntax
     P4cub.Syntax.CubNotations.

(** A custom induction principle for value. *)
Section ValueInduction.
  Import Val.
  Local Open Scope val_scope.
  
  Variable P : t -> Prop.
  
  Hypothesis HVBool : forall b, P (Bool b).
  
  Hypothesis HVBit : forall w n, P (w VW n).

  Hypothesis HVInt : forall w n, P (w VS n).

  Hypothesis HVVarBit : forall m w n, P (VarBit m w n).
  
  Hypothesis HVLists : forall ls vs,
      Forall P vs -> P (Lists ls vs).
  
  Hypothesis HVError : forall err, P (Error err).
  
  Definition custom_val_ind : forall v' : Val.t, P v' :=
    fix custom_val_ind (val : Val.t) : P val :=
      match val with
      | Bool b      => HVBool b
      | w VS n      => HVInt w n
      | w VW n      => HVBit w n
      | VarBit m w n  => HVVarBit m w n
      | Error err   => HVError err
      | Lists ls vs
        => HVLists ls vs
            $ list_ind
            (Forall P) (Forall_nil _)
            (fun v _ => Forall_cons _ (custom_val_ind v)) vs
      end.
End ValueInduction.
