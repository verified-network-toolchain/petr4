From Poulet4 Require Import
     P4cub.Semantics.Dynamic.BigStep.Value.Syntax
     P4cub.Syntax.CubNotations.
Import Val ValueNotations.

(** A custom induction principle for value. *)
Section ValueInduction.
  Local Open Scope value_scope.
  
  Variable P : v -> Prop.
  
  Hypothesis HVBool : forall b, P (Bool b).
  
  Hypothesis HVBit : forall w n, P (w VW n).
  
  Hypothesis HVInt : forall w n, P (w VS n).
  
  Hypothesis HVStruct : forall vs ob,
      Forall P vs -> P (Struct vs ob).
  
  Hypothesis HVError : forall err, P (Error err).
  
  Definition custom_v_ind : forall v' : v, P v' :=
    fix custom_v_ind (val : v) : P val :=
      let fix lind (vs : list v) : Forall P vs :=
          match vs with
          | [] => Forall_nil _
          | hv :: vs => Forall_cons _ (custom_v_ind hv) (lind vs)
          end in
      match val with
      | Bool b       => HVBool b
      | w VS n       => HVInt w n
      | w VW n       => HVBit w n
      | Struct vs ob => HVStruct vs ob (lind vs)
      | Error err    => HVError err
      end.
End ValueInduction.
