Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.P4Monad.
Open Scope monad.
Require Import Lists.List.
Import ListNotations.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.

Definition IPHeader :=
  HAList.t _
  [("src", option (bits 8));
   ("dst", option (bits 8));
   ("proto", option (bits 4))].

Definition IPHeader_p : PktParser IPHeader :=
  let* src := extract_n 8 in 
  let* dst := extract_n 8 in 
  let* proto := extract_n 4 in 
  pure (src, (dst, (proto, tt))).

Definition TCP :=
  HAList.t _ 
  [("sport", option (bits 8));
   ("dport", option (bits 8));
   ("flags", option (bits 4));
   ("seq", option (bits 8))].

Definition TCP_p : PktParser TCP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
  let* seq := extract_n 8 in 
    pure (sport, (dport, (flags, (seq, tt)))).

Definition UDP := 
  HAList.t _ 
  [("sport", option (bits 8)); 
   ("dport", option (bits 8));
   ("flags", option (bits 4))].


Definition UDP_p : PktParser UDP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
    pure (sport, (dport, (flags, tt))).

Definition Headers := 
  HAList.t _ 
  [("ip", IPHeader); 
   ("transport", (TCP + UDP)%type)].

Definition Headers_p : PktParser Headers := 
  let* iph := IPHeader_p in 
  let proto_opt := HAList.get _ iph (exist _ "proto" I) in
  let* proto := lift_option proto_opt in 
  match proto with 
  | (false, (false, (false, (false, tt)))) =>
    let* tcp := TCP_p in 
      pure (iph, (inl tcp, tt))
  | (false, (false, (false, (true, tt)))) =>
    let* udp := UDP_p in 
      pure (iph, (inr udp, tt))
  | _ => reject
  end.

Definition TCP_valid (tcp: TCP) : bool :=
  match tcp with 
  | (Some _, (Some _, (Some _, (Some _, tt)))) => true
  | _ => false
  end.

Definition MyIngress (hdr: Headers) : PktParser Headers := 
  match HAList.get _ hdr (exist _ "transport" I) with 
  | inl tcp => 
    if TCP_valid tcp 
    then set_std_meta (fun mt => HAList.set _ mt (exist _ "egress_spec" I) one_bits) ;; pure hdr 
    else set_std_meta (fun mt => HAList.set _ mt (exist _ "egress_spec" I) zero_bits) ;; pure hdr 
  | _ => pure hdr
  end.

Definition MyProg (pkt: list bool) : PktParser Headers :=
  put_state (fun _ => init_state pkt) ;;
  let* hdr := Headers_p in 
    MyIngress hdr.

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

Definition EgressSpecOne (out : @ParserState Meta) : Prop :=
  HAList.get _ (std_meta out) (exist _ "egress_spec" I) = one_bits.

Definition EgressSpecZero (out : @ParserState Meta) : Prop :=
  HAList.get _ (std_meta out) (exist _ "egress_spec" I) = zero_bits.

Definition PacketConsumed (out : @ParserState Meta) : Prop :=
  match pkt out with
  | nil => True
  | _ => False
  end.

Lemma WFPacketLength : forall pkt : list bool, HeaderWF pkt ->
  length pkt = 32 \/ length pkt = 40.
Proof.
  intros pkt [H16 [H17 [H18 H]]]. destruct H.
  - right. apply H.
  - left. apply H.
Qed.

Definition final_state {R} (st: ParserState) (p: PktParser R) := 
  let (_, st') := run_with_state st p in st'.

Definition IPHeader_p_spec : Prop :=
  forall st, (length (pkt st) >= 20 <-> exists bits st', run_with_state st IPHeader_p = (bits, st')
         /\ length (pkt st') = length (pkt st) - 20).

Definition TCP_p_spec : Prop :=
  forall st, (length (pkt st) >= 28 <-> exists bits st', run_with_state st TCP_p = (bits, st')
         /\ length (pkt st') = length (pkt st') - 28).                        

Lemma IPHeader_p_Correct : IPHeader_p_spec.
Admitted.

Lemma TCP_p_Correct : TCP_p_spec.
Admitted.

Theorem ParseTCPCorrect : forall (pckt : list bool) (st: ParserState),
    (pkt st = pckt) -> HeaderWF pckt -> IPHeaderIsTCP pckt ->
    EgressSpecZero (final_state st (MyProg pckt)).
Proof.
  intros pckt st Hdum Hwf Htcp.
  destruct Hwf as [H16 [H17 [H18 H19]]].
  assert (P : length pckt >= 20). {
    destruct H19.
    - destruct H as [_ H]. rewrite H. repeat (right; try reflexivity).
    - destruct H as [_ H]. rewrite H. repeat (right; try reflexivity).
  }  
  rewrite <- Hdum in P. apply IPHeader_p_Correct in P.
  destruct P as [bits [st' [P1 P2]]].
  unfold MyProg. unfold Headers_p.
  (* rewrite P1.
     Error: Found no subterm matching "run_with_state st IPHeader_p" in the current goal. *)
Admitted.

(*
Theorem ParseUDPCorrect : forall pkt : list bool, HeaderWF pkt -> IPHeaderIsUDP pkt ->
     EgressSpecOne (MyProg pkt).
Admitted.

Theorem ParseComplete : forall pkt : list bool, HeaderWF pkt ->
   (IPHeaderIsUDP pkt \/ IPHeaderIsTCP pkt) ->
   PacketConsumed (MyProg pkt).
Admitted.
 *)
