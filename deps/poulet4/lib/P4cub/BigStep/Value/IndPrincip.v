Require Import Poulet4.P4cub.BigStep.Value.Syntax.
Import Val.

(** A custom induction principle for value. *)
Section ValueInduction.
  Variable P : v -> Prop.
  
  Hypothesis HVBool : forall b, P (VBool b).
  
  Hypothesis HVBit : forall w n, P (VBit w n).
  
  Hypothesis HVInt : forall w n, P (VInt w n).
  
  Hypothesis HVTuple : forall vs,
      Forall P vs -> P (VTuple vs).
  
  Hypothesis HVStruct : forall fs,
      Field.predfs_data P fs -> P (VStruct fs).
  
  Hypothesis HVHeader : forall fs b,
      Field.predfs_data P fs -> P (VHeader fs b).
  
  Hypothesis HVError : forall err, P (VError err).
  
  Hypothesis HVMatchKind : forall mk, P (VMatchKind mk).
  
  Hypothesis HVHeaderStack : forall ts hs size ni,
      Forall (Field.predfs_data P ∘ snd) hs -> P (VHeaderStack ts hs size ni).
  
  Definition custom_value_ind : forall v' : v, P v' :=
    fix custom_value_ind (val : v) : P val :=
      let fix lind (vs : list v) : Forall P vs :=
          match vs with
          | [] => Forall_nil _
          | hv :: vs => Forall_cons _ (custom_value_ind hv) (lind vs)
          end in
      let fix fields_ind
              (flds : F.fs string v) : Field.predfs_data P flds :=
          match flds as fs return Field.predfs_data P fs with
          | [] => Forall_nil (Field.predf_data P)
          | (_, hfv) as hf :: tf =>
            Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
          end in
      let fix ffind
              (fflds : list (bool * Field.fs string v))
          : Forall (Field.predfs_data P ∘ snd) fflds :=
          match fflds as ffs
                return Forall (Field.predfs_data P ∘ snd) ffs with
          | [] => Forall_nil (Field.predfs_data P ∘ snd)
          | (_, vs) as bv :: ffs => Forall_cons bv (fields_ind vs) (ffind ffs)
          end in
      match val as v' return P v' with
      | VBool b  => HVBool b
      | VInt w n => HVInt w n
      | VBit w n => HVBit w n
      | VTuple vs      => HVTuple vs (lind vs)
      | VStruct vs     => HVStruct vs (fields_ind vs)
      | VHeader vs b   => HVHeader vs b (fields_ind vs)
      | VError err     => HVError err
      | VMatchKind mk  => HVMatchKind mk
      | VHeaderStack ts hs size ni => HVHeaderStack ts hs size ni (ffind hs)
      end.
End ValueInduction.
