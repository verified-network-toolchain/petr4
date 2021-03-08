Require Import Syntax.
Require Import BabyIP.
Require Import SimpleIPv4Monadic.
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

Inductive bits_repr (n: nat) : bits n -> @ValueBase P4defs.Info -> Prop :=
.

Definition get_header_field (v: @Value P4defs.Info) (field: string) : option (@ValueBase P4defs.Info).
Admitted.

Inductive type_repr: forall (t: Type), t -> @ValueBase P4defs.Info -> Prop :=
| BitsRepr: forall n u v,
    bits_repr n u v ->
    type_repr (bits n) u v.

Fixpoint header_repr  (fields: list (string * Type)) (v: @Value P4defs.Info) (rec: HAList.t _ fields) {struct fields}: Prop.
  revert rec.
  refine (match fields as f return HAList.t _ f -> Prop with
          | [] => fun rec => True
          | (field_name, type) :: rest => _
          end).
  intro rec.
  refine (exists field_val,
             get_header_field v field_name = Some field_val /\
             type_repr type _ field_val /\
             header_repr rest v (snd rec)).
  refine (let field_valid := (_ : @HAList.valid_key _ _ StrEqDec _ ((field_name, type) :: rest)) in _).
  Unshelve.
  all:swap 1 2.
  {
    unfold HAList.valid_key.
    exists field_name.
    cbn.
    destruct (StrEqDec field_name field_name); try congruence.
    exact I.
  }
  


    

  

Inductive header_repr_ip: @Value P4defs.Info -> IPHeader -> Prop :=
| IPRepr: forall src_v dest_v proto_v src_b dest_b proto_b,
    bits_repr 8 src_b src_v ->
    bits_repr 8 dest_b dest_v ->
    bits_repr 4 proto_b proto_v ->
    header_repr_ip (ValBase (ValBaseHeader [(MkP4String "src", src_v);
                                            (MkP4String "dst", dest_v);
                                            (MkP4String "proto", proto_v)] true))
                   {|src:=Some src_b; dest:=Some dest_b; proto:=Some proto_b|}.

Inductive header_repr_tcp: @Value P4defs.Info -> TCP -> Prop :=
| TCPRepr: forall sport_v dport_v flags_v seq_v sport_b dport_b flags_b seq_b,
    bits_repr 8 sport_b sport_v ->
    bits_repr 8 dport_b dport_v ->
    bits_repr 4 flags_b flags_v ->
    bits_repr 8 seq_b seq_v ->
    header_repr_tcp (ValBase (ValBaseHeader [(MkP4String "sport", sport_v);
                                            (MkP4String "dport", dport_v);
                                            (MkP4String "flags", flags_v);
                                            (MkP4String "seq", seq_v)] true))
                    {|sport_t:=Some sport_b;
                      dport_t:=Some dport_b;
                      flags_t:=Some flags_b;
                      SimpleIPv4Monadic.seq:=Some seq_b|}.

Inductive header_repr_udp: @Value P4defs.Info -> UDP -> Prop :=
| UDPRepr: forall sport_v dport_v flags_v seq_v sport_b dport_b flags_b seq_b,
    bits_repr 8 sport_b sport_v ->
    bits_repr 8 dport_b dport_v ->
    bits_repr 4 flags_b flags_v ->
    bits_repr 8 seq_b seq_v ->
    header_repr_udp (ValBase (ValBaseHeader [(MkP4String "sport", sport_v);
                                            (MkP4String "dport", dport_v);
                                            (MkP4String "flags", flags_v);
                                            (MkP4String "seq", seq_v)] true))
                    {|sport_u:=Some sport_b;
                      dport_u:=Some dport_b;
                      flags_u:=Some flags_b|}.

Inductive header_repr: @Value P4defs.Info -> Headers -> Prop :=
.

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

Definition ip_header_equiv (val: @ValueBase P4defs.Info) (hdrs: IPHeader) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    bits_equiv_header val' "src" 8 hdrs.(src) /\
    bits_equiv_header val' "dst" 8 hdrs.(dest) /\
    bits_equiv_header val' "proto" 4 hdrs.(proto)
  | _ => False
  end
.

Definition tcp_header_equiv (val: @ValueBase P4defs.Info) (hdrs: TCP) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    bits_equiv_header val' "sport" 8 hdrs.(sport_t) /\
    bits_equiv_header val' "dport" 8 hdrs.(dport_t) /\
    bits_equiv_header val' "flags" 4 hdrs.(flags_t) /\
    bits_equiv_header val' "seq" 8 hdrs.(SimpleIPv4Monadic.seq)
  | _ => False
  end
.

Definition udp_header_equiv (val: @ValueBase P4defs.Info) (hdrs: UDP) : Prop :=
  match val with
  | ValBaseHeader val' true =>
    bits_equiv_header val' "sport" 8 hdrs.(sport_u) /\
    bits_equiv_header val' "dport" 8 hdrs.(dport_u) /\
    bits_equiv_header val' "flags" 4 hdrs.(flags_u)
  | _ => False
  end
.

Definition t_or_u_header_equiv (val: @ValueBase P4defs.Info) (hdrs: TCP + UDP) : Prop :=
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

Definition header_equiv (val: @Value P4defs.Info) (hdrs: Headers) : Prop :=
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
