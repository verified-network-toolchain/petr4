Require Import Syntax.
Require Import BabyIP.
Require Import SimpleIPv4.
Require Import P4defs.
Require Import Step.
Require Import P4String.

Require Import Environment.Environment.
Require Import Petr4.Monads.Monad.
Require Import Petr4.Monads.P4Monad.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Open Scope nat_scope.
Open Scope monad_scope.

Definition MkP4String s := {| tags := NoInfo; str := s |}.

Definition eval_parser' pkt parser :=
  match parser with
  | DeclParser _ _ _ params constructor_params locals states =>
    let env := {|
          env_fresh := 0;
          env_stack := MStr.empty loc :: nil;
          env_heap := MNat.empty (@Value P4defs.Info);
        |} in
    let scope := MkEnv_EvalEnv nil nil (MkP4String "dummy") in
    let parser := ValObjParser scope params constructor_params locals states in
    let packet := ValObj (ValObjPacket pkt) in
    let stepper := step_trans _ NoInfo parser 2 (MkP4String "start") in
    Some ((env_insert P4defs.Info "packet" packet ;;
           env_insert P4defs.Info "hdr" (ValBase (ValBaseHeader ((MkP4String "ip", ValBaseHeader ((MkP4String "src", ValBaseBit 8 0) :: (MkP4String "dst", ValBaseBit 8 0) :: (MkP4String "proto", ValBaseBit 4 0) :: nil) false) :: (MkP4String "t_or_u", ValBaseUnion ((MkP4String "udp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: nil) false) :: (MkP4String "tcp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: (MkP4String "seq", ValBaseBit 8 0) :: nil) false) :: nil)) :: nil) false)) ;; stepper) env)
  | _ => None
  end
.

Definition eval_parser pkt parser : option (Value * list bool) :=
  match eval_parser' pkt parser with
  | Some (inl _, env) =>
    let get_pkt_and_hdr :=
        let* pkt_val := env_str_lookup P4defs.Info (MkP4String "packet") in
        let* hdr_val := env_str_lookup P4defs.Info (MkP4String "hdr") in
        mret (hdr_val, pkt_val)
    in
    match get_pkt_and_hdr env  with
    | (inl (hdr, (ValObj (ValObjPacket pkt))), env) =>
      Some (hdr, pkt)
    | _ => None
    end
  | Some (inr _, _)
  | None => None
  end.

Definition bits_repr (n: nat) (bs: bits n) (v: @ValueBase P4defs.Info) : Prop :=
  match v with
  | ValBaseBit n' z => n = n' /\ Some z = bits2Z bs
  | _ => False
  end.

Inductive val_repr: forall (t: Type), t -> @ValueBase P4defs.Info -> Prop :=
| VRBits: forall n u v,
    bits_repr n u v ->
    val_repr (bits n) u v.

(* I wrote this by using tactics and then hand-simplifying the
   resulting term. - Ryan *)
Definition header_repr (fields: list (string * Type)) (rec: HAList.t fields)
  : list (P4String.t P4defs.Info * @ValueBase P4defs.Info) -> Prop :=
  HAList.t_rect
    (fun fields (t1 : HAList.t fields) => forall rec0, rec0 = t1 -> list (t Info * ValueBase) -> Prop)
    (fun _ _ v =>
       v = [])
    (fun (k: string) (typ: Type) _ (rec_val: typ) rec' header_repr _ _ v =>
       match v with
       | [] => False
       | (field_name, field_val) :: v' =>
         field_name.(str) = k /\
         val_repr typ rec_val field_val /\
         header_repr rec' eq_refl v'
       end)
    fields rec rec eq_refl.
Arguments header_repr {_%list_scope} _ _%list_scope.

Definition value_repr {fields} (rec: HAList.t fields) (val: @Value P4defs.Info): Prop :=
  match val with
  | ValBase (ValBaseHeader hdr true) => header_repr rec hdr
  | _ => False
  end.

Notation P4String := (P4String.t Info).

Fixpoint assoc_get {A: Type} (map: list (P4String * A)) (key: P4String) : option A :=
  match map with
  | nil => None
  | (k, v) :: map' =>
    if eqb k.(str) key.(str) then Some v else assoc_get map' key
  end
.

Inductive bits_pos_equiv : positive -> {n: nat & bits n} -> Prop :=
| bits_pos_equiv_base: bits_pos_equiv xH (existT bits 1 (true, tt))
(* TODO: Sensible way to implement this comparison; note that bits are given msb to lsb *)
.

Inductive bits_Z_equiv : Z -> {n: nat & bits n} -> Prop :=
| bits_Z_equiv_zero : forall n, bits_Z_equiv Z0 (existT bits n zero_bits)
(* TODO: A way to make the stuff below typecheck. *)
(* | bits_Z_equiv_pos: forall n p b, bits_pos_equiv p b -> bits_Z_equiv (Zpos p) (existT bits (S n) (false, projT2 b)) *)
.

Definition bits_equiv_header (val: list (P4String * @ValueBase P4defs.Info)) (key: string) (n: nat) (other: option (bits n)) :=
  match assoc_get val (MkP4String key), other with
  | Some (ValBaseBit n' b), Some other' =>
    n = n' /\ bits_Z_equiv b (existT bits n other')
  | _, _ => False
  end
.

Theorem parser_grammar_sound :
  forall p p' hdr hdr_rec parser_state,
    eval_parser p MyParser = Some (hdr, p') ->
    State.run_with_state (init_state p) Headers_p = (inl hdr_rec, parser_state) ->
    value_repr hdr_rec hdr /\
    p' = parser_state.(pkt).
Proof.
  intros.
Admitted.
