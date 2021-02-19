Require Import Grammar.
Require Import Lib.
Require Import Binary.
Require Import Bits.

Record IPHeader := {
  src: bits 8;
  dest: bits 8;
  proto: bits 4
}.

Definition IPHeader_p : grammar IPHeader :=
  (
    bits_n 8 >= fun src => 
    bits_n 8 >= fun dest => 
    bits_n 4 >= fun proto => 
      ret {| src := src; dest := dest; proto := proto |}
  ) @ fun x => projT2 (projT2 (projT2 x)).


Record TCP := {
  sport_t: bits 8;
  dport_t: bits 8;
  flags_t: bits 4;
  seq: bits 8
}.

Definition TCP_p : grammar TCP :=
  (
    bits_n 8 >= fun sport_t => 
    bits_n 8 >= fun dport_t => 
    bits_n 4 >= fun flags_t => 
    bits_n 8 >= fun seq =>
      ret {| sport_t := sport_t; dport_t := dport_t; flags_t := flags_t; seq := seq |}
  ) @ fun x => projT2 (projT2 (projT2 (projT2 x))).

Record UDP := {
  sport_u: bits 8;
  dport_u: bits 8;
  flags_u: bits 4
}.

Definition UDP_p : grammar UDP :=
  (
    bits_n 8 >= fun sport_u => 
    bits_n 8 >= fun dport_u => 
    bits_n 4 >= fun flags_u => 
      ret {| sport_u := sport_u; dport_u := dport_u; flags_u := flags_u |}
  ) @ fun x => projT2 (projT2 (projT2 x)).

Record Headers := {
  ip: IPHeader;
  transport: option (TCP + UDP)
}.

Definition babyParser : grammar Headers := 
  (IPHeader_p >= fun iph => 
  match proto iph return grammar (option (TCP + UDP)) with
  | (false, (false, (false, (false, tt)))) => 
    TCP_p @ inl @ Some
  | (false, (false, (false, (true, tt)))) => 
    UDP_p @ inr @ Some
  | _ => ret None
  end)
  @ fun x => let (ip, transport) := x in 
    {| ip := ip; transport := transport |}.


Record StandardMeta := {
  egress_spec : bits 9
}.

Definition init_meta : StandardMeta := {| egress_spec := zero_bits 9 |}.

Definition IngressFunc (Hdrs: Type) (Meta: Type) : Type := 
  (option Hdrs * Meta * StandardMeta) -> (option Hdrs * Meta * StandardMeta).

Definition MyIngress : IngressFunc Headers unit := fun hms =>
  let '(hdrs, m, sm) := hms in 
  match hdrs with 
  | Some _ => (hdrs, m, {| egress_spec := zero_bits 9 |})
  | None   => (hdrs, m, {| egress_spec := one_bits |})
  end.

Definition MyProg (pkt: list bool) : option Headers * unit * StandardMeta :=
  match parse babyParser pkt with
  | res :: nil => MyIngress (Some res, tt, init_meta)
  | _ => MyIngress (None, tt, init_meta)
  end.

Definition ProgOut : Type := option Headers * unit * StandardMeta.

Definition HeaderWF (pkt : list bool) : Prop :=
  (List.nth_error pkt 16 = Some false) /\
  (List.nth_error pkt 17 = Some false) /\
  (List.nth_error pkt 18 = Some false) /\
  ((List.nth_error pkt 19 = Some false /\ length pkt = 40) \/
   (List.nth_error pkt 19 = Some true /\ length pkt = 32)).

Definition IPHeaderIsTCP (pkt : list bool) : Prop :=
  length pkt = 40.

Definition IPHeaderIsUDP (pkt : list bool) : Prop :=
  length pkt = 32.

Definition EgressSpecOne (out : ProgOut) : Prop :=
  egress_spec (snd out) = one_bits.

Definition EgressSpecZero (out : ProgOut) : Prop :=
  egress_spec (snd out) = zero_bits 9.

Definition PacketConsumed (out : ProgOut) : Prop :=
  match fst (fst out) with
  | Some _ => True
  | _ => False
  end.

Lemma WFPacketLength : forall pkt : list bool, HeaderWF pkt ->
                                       length pkt = 32 \/ length pkt = 40.
Proof.
  intros pkt [H16 [H17 [H18 H]]]. destruct H.
  - right. apply H.
  - left. apply H.
Qed.

Theorem ParseTCPCorrect : forall pkt : list bool, HeaderWF pkt -> IPHeaderIsTCP pkt ->
                                          EgressSpecZero (MyProg pkt).
Proof.
  intros pkt Hwf Htcp.
  repeat (destruct pkt; (destruct Hwf as [_ [_ [_ [[ _ H] | [_ H]]]]]; simpl in H; inversion H)).
  - unfold MyProg. simpl.
Admitted.
                                          
Theorem ParseUDPCorrect : forall pkt : list bool, HeaderWF pkt -> IPHeaderIsUDP pkt ->
                                          EgressSpecOne (MyProg pkt).
Admitted.

Theorem ParseComplete : forall pkt : list bool, HeaderWF pkt ->
                                        (IPHeaderIsUDP pkt \/ IPHeaderIsTCP pkt) ->
                                        PacketConsumed (MyProg pkt).
Admitted.
