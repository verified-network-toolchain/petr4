Require Import Poulet4.Syntax.
Require Import Poulet4.P4defs.
Require Import Poulet4.Step.
Require Import Poulet4.P4String.
Require Import Poulet4.Environment.
Require Import Poulet4.Monads.Monad.

Require Import Poulet4.Examples.SimpleIPv4Monadic.
Require Import Poulet4.Examples.BabyIP.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Definition tag_t := Info.
Definition tag := NoInfo.

Notation P4String := (P4String.t tag_t).

Definition MkP4String (s: string) : P4String := {| P4String.tags := tag; P4String.str := s |}.

Open Scope nat_scope.
Open Scope monad_scope.

Definition eval_parser' pkt parser :=
  match parser with
  | DeclParser _ _ _ params constructor_params locals states =>
    let env := {|
          env_fresh := 0;
          env_stack := MStr.empty loc :: nil;
          env_heap := MNat.empty (@Value Info);
        |} in
    let scope := MkEnv_EvalEnv nil nil (MkP4String "dummy") in
    let parser := ValObjParser scope params constructor_params locals states in
    let packet := ValObj (ValObjPacket pkt) in
    let stepper := step_trans _ NoInfo parser 2 (MkP4String "start") in
    Some ((env_insert Info "packet" packet ;;
           env_insert Info "hdr" (ValBase (ValBaseHeader ((MkP4String "ip", ValBaseHeader ((MkP4String "src", ValBaseBit 8 0) :: (MkP4String "dst", ValBaseBit 8 0) :: (MkP4String "proto", ValBaseBit 4 0) :: nil) false) :: (MkP4String "t_or_u", ValBaseUnion ((MkP4String "udp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: nil) false) :: (MkP4String "tcp", ValBaseHeader ((MkP4String "sport", ValBaseBit 8 0) :: (MkP4String "dport", ValBaseBit 8 0) :: (MkP4String "flags", ValBaseBit 4 0) :: (MkP4String "seq", ValBaseBit 8 0) :: nil) false) :: nil)) :: nil) false)) ;; stepper) env)
  | _ => None
  end
.

Definition eval_parser pkt parser : option (Value * list bool) :=
  match eval_parser' pkt parser with
  | Some (inl _, env) =>
    let get_pkt_and_hdr :=
        let* pkt_val := env_str_lookup Info (MkP4String "packet") in
        let* hdr_val := env_str_lookup Info (MkP4String "hdr") in
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

Inductive header_repr: @Value Info -> Headers -> Prop :=
.

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

Definition bits_equiv_header (val: list (P4String * @ValueBase Info)) (key: string) (n: nat) (other: option (bits n)) :=
  match assoc_get val (MkP4String key), other with
  | Some (ValBaseBit n' b), Some other' =>
    n = n' /\ bits_Z_equiv b (existT bits n other')
  | _, _ => False
  end
.

Definition ip_header_equiv (val: @ValueBase Info) (hdrs: IPHeader) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    bits_equiv_header val' "src" 8 hdrs.(src) /\
    bits_equiv_header val' "dst" 8 hdrs.(dest) /\
    bits_equiv_header val' "proto" 4 hdrs.(proto)
  | _ => False
  end
.

Definition tcp_header_equiv (val: @ValueBase Info) (hdrs: TCP) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    bits_equiv_header val' "sport" 8 hdrs.(sport_t) /\
    bits_equiv_header val' "dport" 8 hdrs.(dport_t) /\
    bits_equiv_header val' "flags" 4 hdrs.(flags_t) /\
    bits_equiv_header val' "seq" 8 hdrs.(SimpleIPv4Monadic.seq)
  | _ => False
  end
.

Definition udp_header_equiv (val: @ValueBase Info) (hdrs: UDP) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    bits_equiv_header val' "sport" 8 hdrs.(sport_u) /\
    bits_equiv_header val' "dport" 8 hdrs.(dport_u) /\
    bits_equiv_header val' "flags" 4 hdrs.(flags_u)
  | _ => False
  end
.

Definition t_or_u_header_equiv (val: @ValueBase Info) (hdrs: TCP + UDP) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    match hdrs with
    | inl tcp_hdrs =>
      assoc_get val' (MkP4String "udp") = None /\
      match assoc_get val' (MkP4String "tcp") with
      | Some val'' =>
        tcp_header_equiv val'' tcp_hdrs
      | None => False
      end
    | inr udp_hdrs =>
      assoc_get val' (MkP4String "tcp") = None /\
      match assoc_get val' (MkP4String "udp") with
      | Some val'' =>
        udp_header_equiv val'' udp_hdrs
      | None => False
      end
    end
  | _ => False
  end
.

Definition header_equiv (val: @Value Info) (hdrs: Headers) : Prop :=
  match val with
  | ValBase (ValBaseHeader val' true) =>
    match assoc_get val' (MkP4String "ip") with
    | Some ip_val => ip_header_equiv ip_val hdrs.(ip)
    | None => False
    end /\
    match assoc_get val' (MkP4String "t_or_u") with
    | Some t_or_u_val => t_or_u_header_equiv t_or_u_val hdrs.(transport)
    | None => False
    end
  | _ => False
  end
.

Theorem parser_grammar_sound :
  forall p p' hdr hdr_rec parser_state,
    eval_parser p MyParser = Some (hdr, p') ->
    State.run_with_state (init_state p) Headers_p = (inl hdr_rec, parser_state) ->
    header_equiv hdr hdr_rec /\
    p' = parser_state.(pkt).
Proof.
  intros.
Admitted.
