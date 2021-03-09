Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.Hoare.
Require Import Coq.Init.Nat.
Require Import Lia.
Open Scope monad.
Open Scope hoare.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.

Lemma foo {B} : forall x y: nat, @inl _ B x = inl y <-> x = y.
Admitted.

Definition incr_st : @state_monad nat unit nat :=
  x <- get_state ;;
  state_return (x+1).

Lemma incr_weaken : 
  {{ top }} incr_st 
  {{ fun r s s' => 
    exists r', r = inl r' /\ r' > s }}.
Proof.
  refine (hoare_consequence (
    st <-- hoare_get ;; hoare_return (st + 1)
  ) _ _).
  2 : {
    intros.
    destruct H as [st_middle HI].
    destruct HI.
      - destruct H as [a H]. exists (a + 1).
      split. 
        -- destruct H as [_ [H' _]]. exact H'.
        -- 
          destruct H as [[HL1 HL2] [HR1 HR2]].
          assert (a = i).
          eapply foo. exact HL2.
          lia.
      - exfalso.
      destruct H as [e [_ H]].
      discriminate.
  }
  intros. split. auto.
  intros.
  destruct r; auto.
  
Qed.

Definition greater_cond : @state_monad nat unit (option unit) :=
  st <- get_state ;; 
  match st with 
  | 0 => state_return (Some tt)
  | _ => state_return None
  end.

Lemma greater_spec : 
  {{ top }}
  greater_cond 
  {{ fun r s s' => 
    match r with 
    | inl (Some tt) => s = 0
    | (inl _) => s > 0
    | inr _ => False
    end 
  }}.
Admitted.
(* Proof. *)
  (* refine (hoare_consequence (
    st <-- @hoare_get nat unit ;;
    match st as st' with 
    | 0 => @hoare_return nat unit (option unit) (Some tt)
    | _ => @hoare_return nat unit (option unit) None
    end
  ) _ _). *)

Definition Bits (n: nat) : Set := (nat * list bool).

Definition bits2list {n: nat} (bs: Bits n) : list bool := snd bs.

Definition zero_bits {n: nat} : Bits n := (n, repeat false n).

Definition one_bits {w: nat} : Bits (S w) :=
  let (_, bs') := @zero_bits w in (S w, app bs' (true :: nil)).

Record StandardMeta := mkStandardMeta {
  egress_spec : Bits 9
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


Definition next_bit_post {r: option bool} (bo: option bool + Error) (st: @ParserState Meta) (st': @ParserState Meta) : Prop := 
  match (bo, pkt st) with 
  | (inr _, _) => False
  | (inl None, _) => st = st'
  | (inl (Some _), nil) => False (* should not exist *)
  | (inl (Some b), b' :: bits') =>
    b = b' /\
    fuel st = fuel st' /\
    pkt st' = bits' /\ 
    usr_meta st = usr_meta st' /\ 
    std_meta st = std_meta st'
  end.


Lemma next_bit_spec : 
  {{ top }} 
    next_bit
  {{ fun r s s' => 
    match r with 
    | inr _ => False
    | inl (Some b) => 
      match pkt s with
      | nil => False
      | b' :: bits => b = b' /\ s' = s <| pkt := bits |>
      end
    | inl None =>
      match pkt s with
      | nil => s = s'
      | _ :: _ => False
      end
    end
  }}.
Proof.
Admitted.
  (* intros.
  refine (hoare_consequence (
    hoare_bind' 
      (@hoare_get (@ParserState Meta) unit)
      (fun st => 
        hoare_return (Some true)
        match pkt st with 
        | x :: pkt' => @hoare_return (@ParserState Meta) unit (option bool) (Some true)
        | nil => @hoare_return (@ParserState Meta) unit (option bool) (Some true)
        end
      )
  ) _ _).
Admitted. *)

Fixpoint extract_n (n: nat) : PktParser (option (Bits n)) :=
  match n as n' return PktParser (option (Bits n')) with
  | 0 => pure (Some (0, nil))
  | S n' => 
    let* bit := next_bit in 
    let* bits := extract_n n' in 
    match (bit, bits) with
    | (Some bit', Some (w, bits')) => pure (Some (S w, bit' :: bits'))
    | _ => pure None
    end
  end.

Definition extract_n_post (n: nat) (ob: option (Bits n)) (st: @ParserState Meta) (st': @ParserState Meta) : Prop := 
  if leb n (length (pkt st)) 
  then exists pref suff, 
    pref = firstn n (pkt st) /\
    st' = st <| pkt := suff |> /\
    pkt st = pref ++ suff /\
    ob = Some (n, pref)
  else exists pref,
    pref = firstn n (pkt st) /\
    pkt st = pref /\
    st' = st <| pkt := nil |> /\
    ob = None.

(* Lemma extract_n_spec : 
  forall n,
  {{ top }}
    extract_n n
  {{ extract_n_post n }}.
Admitted. *)

Record IPHeader := {
  src: option (Bits 8);
  dest: option (Bits 8);
  proto: option (Bits 4)
}.

Definition IPHeader_p : PktParser IPHeader :=
  let* src := extract_n 8 in 
  let* dest := extract_n 8 in 
  let* proto := extract_n 4 in 
    pure {| src := src ; dest := dest; proto := proto |}
  .

Definition IPHeader_p_post (r: IPHeader) (st: @ParserState Meta) (st': @ParserState Meta) : Prop := 
  length (pkt st') = length (pkt st) - 20 /\
  exists s d p, 
  src r = Some s /\
  dest r = Some d /\
  proto r = Some p.


(* Lemma IPHeader_p_forward :
  {{ fun st => length (pkt st) >= 20 }}
    IPHeader_p
  {{ IPHeader_p_post }}.
Admitted.
  
Lemma IPHeader_p_spec :
  forall st, (length (pkt st) >= 20 <-> exists bits st', run_with_state st IPHeader_p = (inl bits, st')
           /\ length (pkt st') = length (pkt st) - 20).
Proof.
  intros.
  split.
  -
    intros.
    pose proof IPHeader_p_forward.
    specialize (H0 st). 
    simpl in H0.
    specialize (H0 H).
    destruct (IPHeader_p st).
    induction s.
    -- 
      exists a.
      exists p.
      unfold IPHeader_p_post in H0.
Admitted. *)


  
(* Definition TCP_p_spec : Prop :=
    forall st, (length (pkt st) >= 28 <-> exists bits st', run_with_state st TCP_p = (bits, st')
           /\ length (pkt st') = length (pkt st') - 28).     
Record TCP := {
  sport_t: option (bits 8);
  dport_t: option (bits 8);
  flags_t: option (bits 4);
  seq: option (bits 8)
}. *)
(* 
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
Admitted. *)

(*
Theorem ParseUDPCorrect : forall pkt : list bool, HeaderWF pkt -> IPHeaderIsUDP pkt ->
     EgressSpecOne (MyProg pkt).
Admitted.

Theorem ParseComplete : forall pkt : list bool, HeaderWF pkt ->
   (IPHeaderIsUDP pkt \/ IPHeaderIsTCP pkt) ->
   PacketConsumed (MyProg pkt).
Admitted.
 *)
