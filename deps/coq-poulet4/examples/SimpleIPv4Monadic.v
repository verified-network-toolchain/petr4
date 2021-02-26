Require Import Monads.Monad.
Require Import Monads.State.
Open Scope monad.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.

Fixpoint prod (T:Set) (n:nat) : Set :=
  match n with
    | 0   => unit
    | S m => T * (prod T m)
  end.

Definition bits (n: nat) : Set := prod bool n.

Fixpoint zero_bits {n: nat} : bits n :=
  match n with
  | 0 => tt
  | S n' => (false, zero_bits)
  end.

Fixpoint one_bits {w: nat} : bits (S w) :=
  match w with
  | 0 => (true, tt)
  | S w' => (false, one_bits)
  end.


Record StandardMeta := mkStandardMeta {
  egress_spec : bits 9
}.

Instance etaStandardMeta : Settable _ := settable! mkStandardMeta <egress_spec>.


Record ParserState {Meta: Type} := mkParserState {
  fuel: nat;
  pkt: list bool;
  usr_meta: Meta;
  std_meta: StandardMeta
}.


Instance etaParserState {M} : Settable _ := settable! mkParserState M <fuel; pkt; usr_meta; std_meta>.

Definition Error := unit.
Definition Meta := unit.


Definition PktParser (Result: Type) := @state_monad (@ParserState Meta) Error Result.

Definition set_std_meta (f: StandardMeta -> StandardMeta) : PktParser unit :=
  put_state (fun st => st <| std_meta ::= f |>).

(* Definition skip : PktParser  *)

Definition pure {R} : R -> PktParser R := state_return.

Definition reject {R} : PktParser R := state_fail tt.


Definition next_bit : PktParser (option bool) := 
  let* st := get_state in 
  match pkt st return PktParser (option bool) with 
  | x :: pkt' => 
    put_state (fun st => st <| pkt := pkt' |>) ;;
    pure (Some x)
  | _ => pure None
  end.
    
Lemma next_bit_nil : forall st, 
  pkt st = nil <-> exists st', run_with_state st next_bit = (inl None, st').
Proof.
  intros.
  split.
  - 
    intros. 
    exists st.
    cbv.
Admitted.
Lemma next_bit_cons : forall st, 
  exists b bs, pkt st = b :: bs <-> exists st', run_with_state st next_bit = (inl (Some b), st').
Admitted.

Fixpoint extract_n (n: nat) : PktParser (option (bits n)) :=
  match n as n' return PktParser (option (bits n')) with
  | 0 => pure (Some tt)
  | S n' => 
    let* bits := extract_n n' in 
    let* bit := next_bit in 
    match (bit, bits) with
    | (Some bit', Some bits') => pure (Some (bit', bits'))
    | _ => pure None
    end
  end.

Record IPHeader := {
  src: option (bits 8);
  dest: option (bits 8);
  proto: option (bits 4)
}.

Definition IPHeader_p : PktParser IPHeader :=
  let* src := extract_n 8 in 
  let* dest := extract_n 8 in 
  let* proto := extract_n 4 in 
    pure {| src := src ; dest := dest; proto := proto |}
  .

Record TCP := {
  sport_t: option (bits 8);
  dport_t: option (bits 8);
  flags_t: option (bits 4);
  seq: option (bits 8)
}.

Definition TCP_p : PktParser TCP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
  let* seq := extract_n 8 in 
    pure {| sport_t := sport ; dport_t := dport; flags_t := flags; seq := seq |}
  .

Record UDP := {
  sport_u: option (bits 8);
  dport_u: option (bits 8);
  flags_u: option (bits 4)
}.

Definition UDP_p : PktParser UDP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
    pure {| sport_u := sport ; dport_u := dport; flags_u := flags|}
  .

Record Headers := {
  ip: IPHeader;
  transport: TCP + UDP
}.

Definition lift_option {A : Type} (x: option A) : PktParser A :=
  match x with 
  | Some y => pure y
  | _ => reject 
  end.

Definition Headers_p : PktParser Headers := 
  let* iph := IPHeader_p in 
  let* proto := lift_option (proto iph) in 
  match proto with 
  | (false, (false, (false, (false, tt)))) =>
    let* tcp := TCP_p in 
      pure {| ip := iph ; transport := inl tcp |}
  | (false, (false, (false, (true, tt)))) =>
      let* udp := UDP_p in 
        pure {| ip := iph ; transport := inr udp |}
  | _ => reject
  end.


Definition TCP_valid (tcp: TCP) : bool :=
  match tcp with 
  | {| sport_t := Some _; dport_t := Some _; flags_t := Some _; seq := Some _ |} => true
  | _ => false
  end.

Definition init_meta : StandardMeta := {| egress_spec := zero_bits |}.

Definition init_state (pkt: list bool) : ParserState := 
  {| fuel := 0; pkt := pkt; usr_meta := tt; std_meta := init_meta |}.

Definition MyIngress (hdr: Headers) : PktParser Headers := 
  match (transport hdr) with 
  | inl tcp => 
    if TCP_valid tcp 
    then set_std_meta (fun mt => mt <| egress_spec := one_bits |>) ;; pure hdr 
    else set_std_meta (fun mt => mt <| egress_spec := zero_bits |>) ;; pure hdr
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
  egress_spec (std_meta out) = one_bits.

Definition EgressSpecZero (out : @ParserState Meta) : Prop :=
  egress_spec (std_meta out) = zero_bits.

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


Theorem ParseTCPCorrect : forall (pkt : list bool) (st: ParserState), HeaderWF pkt -> IPHeaderIsTCP pkt ->
     EgressSpecZero (final_state st (MyProg pkt)).
Proof.
  intros pkt st Hwf Htcp.
  repeat (destruct pkt; (destruct Hwf as [_ [_ [_ [[ _ H] | [_ H]]]]]; simpl in H; inversion H)).
  - cbv.
Admitted.

Theorem ParseUDPCorrect : forall pkt : list bool, HeaderWF pkt -> IPHeaderIsUDP pkt ->
     EgressSpecOne (MyProg pkt).
Admitted.

Theorem ParseComplete : forall pkt : list bool, HeaderWF pkt ->
   (IPHeaderIsUDP pkt \/ IPHeaderIsTCP pkt) ->
   PacketConsumed (MyProg pkt).
Admitted.
