Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Monads.P4Monad.
Require Import Poulet4.Monads.Hoare.WP.
Require Poulet4.HAList.

Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Plus.

Open Scope monad.

Require Import Coq.Lists.List.
Import ListNotations.

Notation REmp := HAList.REmp.
Notation RCons := HAList.RCons.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.

Definition IPHeader :=
  HAList.t
    [("src", option (bits 8));
     ("dst", option (bits 8));
     ("proto", option (bits 4))].

Definition IPHeader_p : PktParser IPHeader :=
  let* src := extract_n 8 in 
  let* dst := extract_n 8 in 
  let* proto := extract_n 4 in 
  pure (RCons src (RCons dst (RCons proto REmp))).

Definition TCP :=
  HAList.t
  [("sport", option (bits 8));
   ("dport", option (bits 8));
   ("flags", option (bits 4));
   ("seq", option (bits 8))].

Definition TCP_p : PktParser TCP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
  let* seq := extract_n 8 in 
    pure (RCons sport (RCons dport (RCons flags (RCons seq REmp)))).

Definition UDP := 
  HAList.t
  [("sport", option (bits 8)); 
   ("dport", option (bits 8));
   ("flags", option (bits 4))].

Definition UDP_p : PktParser UDP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
    pure (RCons sport (RCons dport (RCons flags REmp))).

Definition Headers := 
  HAList.t
  [("ip", IPHeader); 
   ("transport", (TCP + UDP)%type)].

Definition Headers_p : PktParser Headers := 
  let* iph := IPHeader_p in 
  let proto_opt := HAList.get iph (exist _ "proto" I) in
  let* proto := lift_option proto_opt in 
  match proto with 
  | (false, (false, (false, (false, tt)))) =>
    let* tcp := TCP_p in 
      pure (RCons iph (RCons (inl tcp) REmp))
  | (false, (false, (false, (true, tt)))) =>
    let* udp := UDP_p in 
      pure (RCons iph (RCons (inr udp) REmp))
  | _ => reject
  end.

Equations TCP_valid (tcp: TCP) : bool :=
  {
    TCP_valid (RCons (Some _) (RCons (Some _) (RCons (Some _) (RCons (Some _) _)))) := true;
    TCP_valid _ := false
  }.

Equations IPHeader_valid (ihp: IPHeader) : bool :=
  {
    IPHeader_valid (RCons (Some _) (RCons (Some _) (RCons (Some _) _))) := true;
    IPHeader_valid _ := false
  }.

Definition MyIngress (hdr: Headers) : PktParser Headers := 
  match HAList.get hdr (exist _ "transport" I) with 
  | inl tcp => 
    if TCP_valid tcp 
    then set_std_meta (fun mt => HAList.set mt (exist _ "egress_spec" I) one_bits) ;; pure hdr 
    else set_std_meta (fun mt => HAList.set mt (exist _ "egress_spec" I) zero_bits) ;; pure hdr 
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
  HAList.get (std_meta out) (exist _ "egress_spec" I) = one_bits.

Definition EgressSpecZero (out : @ParserState Meta) : Prop :=
  HAList.get (std_meta out) (exist _ "egress_spec" I) = zero_bits.

Definition PacketConsumed (out : @ParserState Meta) : Prop :=
  match pkt out with
  | nil => True
  | _ => False
  end.

Lemma IPHeader_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 20 >>
    IPHeader_p
  << fun r s' => 
    IPHeader_valid r = true /\ 
    s' = st <| pkt := skipn 20 (pkt st) |> 
  >>.
Admitted.

Lemma TCP_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 28 >>
    IPHeader_p
  << fun r s' => 
    IPHeader_valid r = true /\ 
    s' = st <| pkt := skipn 28 (pkt st) |> 
  >>.
Admitted.

Lemma extract_post st:
  {{ fun s => s = st }}
    next_bit
  {{ fun r s => 
    match (pkt st) with
    | nil => r = inl None /\ s = st
    | b :: bs => r = inl (Some b) /\ s = st <| pkt := bs |>
    end
  }}.
Proof.
  unfold next_bit.
  eapply strengthen_pre_t.
  wp.
  all: swap 2 1.
  intros.
  eapply strengthen_pre_t.
  wp.

  eapply strengthen_pre_t.
  unfold pure.
  wp.
  intros. simpl.
  destruct H as [it eq].
  assert (r = st /\ h = st).
  apply it. 
  simpl in it.
  destruct it as [L R].
  rewrite <- L.
  rewrite eq.
  mysimp.


  eapply strengthen_pre_t.
  wp.

  all: swap 2 1.
  intros.
  eapply strengthen_pre_t.
  unfold pure.
  wp.
  intros. simpl.
  eapply H.
  wp.
  intros.
  eapply H.
  intros. simpl.
  destruct H as [b' [xs' [lhs it]]].
  eapply it.

  intros. eapply H.
  all: swap 2 1.

  intros. eapply H.

  wp.
  intros. simpl.
  mysimp.
  destruct (pkt st).
  mysimp.
  mysimp.
  
  Unshelve.
  exact true.
Qed.

Lemma extract_post_simpl_p st:
  << fun s => s = st >>
    next_bit
  << fun _ s => length (pkt s) = pred (length (pkt st)) >>.
Proof.
  unfold next_bit.
  unfold pure.
  refine ( strengthen_pre_p ( 
    s <-- get_wp_p ;
    (case_list_wp_p (pkt s) _ _ )
  ) _).
  eapply strengthen_pre_p.
  wp.
  intros.
  destruct H as [it eq].
  exact it.

  refine (strengthen_pre_p ( 
    put_wp_p (fun st0 : ParserState => st0 <| pkt := snd (destruct_list' (pkt s) _) |>) ;;;
    return_wp_p (Some (fst (destruct_list' (pkt s) _)))
  ) _ ).
  intros.
  destruct H as [x [xs [eq it]]].
  rewrite eq.
  unfold destruct_list'.
  exact it.

  intros.
  rewrite H.
  destruct st.
  destruct pkt; 
  simpl in *;
  trivial.
  Unshelve.
  exact true.
Qed.


Definition extract_n_post_fixed (n: nat) (ob: option (bits n)) (st: @ParserState Meta) (st': @ParserState Meta) : Prop := 
  if Nat.leb n (length (pkt st)) 
  then exists pref suff bits, 
    pref = firstn n (pkt st) /\
    st' = st <| pkt := suff |> /\
    pkt st = pref ++ suff /\
    ob = Some bits /\
    pref = bits2list bits
  else exists pref,
    pref = firstn n (pkt st) /\
    pkt st = pref /\
    st' = st <| pkt := nil |> /\
    ob = None.

Lemma zero_decr : forall x y, 0 = x - y -> 0 = x - S y.
Proof.
Admitted.
 
Lemma extract_n_simple n st:
  << fun s => s = st /\ length (pkt st) >= n >>
    extract_n n
  << fun _ s' => length (pkt s') = length (pkt st) - n >>.
Proof.
  induction n.
  - unfold extract_n.
    unfold pure.
    eapply strengthen_pre_p. 
    wp.
    mysimp.
  - unfold extract_n. fold extract_n.
    unfold pure.
    eapply strengthen_pre_p.
    wp.
    eapply IHn.
    all: swap 2 1.
    mysimp.

    intros.
    wp.
    all: swap 2 1.
    intros.
    wp.
    eapply strengthen_pre_p.
    wp.
    intros.
    destruct H as [it _].
    exact it.
    eapply strengthen_pre_p.
    wp.
    eapply strengthen_pre_p. wp.
    intros.
    destruct H as [it eq].
    exact it.
    eapply strengthen_pre_p. wp.
    intros.
    unfold destruct_opt.
    destruct H as [x' [eq it]].
    exact it.
    intros.
    destruct H as [x' [eq it]].
    exact it.
    intros.

    unfold next_bit.

    unfold pure.
    refine ( strengthen_pre_p ( 
      s <-- get_wp_p ;
      (case_list_wp_p (pkt s) _ _ )
    ) _).
    eapply strengthen_pre_p.
    wp.
    intros.
    destruct H as [it eq].
    exact it.

    refine (strengthen_pre_p ( 
      put_wp_p (fun st0 : ParserState => st0 <| pkt := snd (destruct_list' (pkt s) _) |>) ;;;
      return_wp_p (Some (fst (destruct_list' (pkt s) _)))
    ) _ ).
    intros.
    destruct H as [x [xs [eq it]]].
    rewrite eq.
    unfold destruct_list'.
    exact it.

    intros.
    destruct h. 
    simpl.
    destruct st.
    destruct pkt; 
    simpl in *;
    trivial.
    eapply zero_decr.
    trivial.

    destruct r; simpl; lia.
    Unshelve.
    exact true.
    exact zero_bits.
    exact true.
Qed.

Definition unwrap_bits {n} (bts: bits n) (default: bool) : (bool * bits (pred n)).
induction n.
  - exact (default, tt).
  - destruct bts.
    exact (b, p).
Defined.


Fixpoint extract_n_post (n: nat) (ob: option (bits n)) (st_initial: @ParserState Meta) (st_final: @ParserState Meta) : Prop :=
  match n as n' with 
  | 0 =>
    exists bits', 
    ob = Some bits' /\
    st_initial = st_final
  | S n' => 
    exists ob' st_mid,
    extract_n_post n' ob' st_mid st_final /\
    match ob' with 
    | Some bts => 
      exists bit bits' pref suff,
      (bit, bits') = unwrap_bits bts false /\
      pkt st_initial = bit :: pref ++ suff /\
      st_mid = st_initial <| pkt := (pref ++ suff) |> /\
      st_final = st_mid <| pkt := suff |> /\
      bits2list bts = bit :: pref
    | None => 
      st_final = st_initial <| pkt := nil |>
    end
  end.




Lemma extract_n_forward n st:
  {{ fun s => s = st }}
    extract_n n
  {{ fun r s' => exists r', r = inl r' /\ extract_n_post n r' st s' }}.
Proof.
  induction n.
  - unfold extract_n.
    unfold extract_n_post.
    eapply strengthen_pre_t.
    unfold pure.
    wp.
    intros.
    mysimp.
    unfold bits.
    simpl.
    exists (Some tt).
    mysimp.
    exists tt.
    mysimp.
  - unfold extract_n.
    fold extract_n.
    unfold extract_n_post.
    fold extract_n_post.
    wp.

    all: swap 3 1.
    intros. apply H.
    intros.
    wp.

    all: swap 3 1.
    intros.
    exact H.
    intros.
    wp.
    eapply strengthen_pre_t.
    unfold pure.
    wp.
    intros.
    simpl.
    exists None.
    split.
    trivial.
    exists None, h.
    destruct H as [it _].
    exact it.
    (* oh boy... *)
Admitted.

Lemma extract_n_length n st: 
  {{ fun s => s = st /\ length (pkt st) >= n }}
    extract_n n 
  {{ Norm (fun r s' => extract_n_post_fixed n r st s') }}.
Admitted.

Lemma extract_n_pre_length n m: 
  << fun s => length (pkt s) = m + n >>
    extract_n n 
  << fun r s' => length (pkt s') = m >>.
Admitted.

Lemma IPHeader_p_body n: 
  << fun s => length (pkt s) = 20 + n >>
    extract_n 8 ;;
    extract_n 8 ;;
    extract_n 4
  << fun r s' => 
    length (pkt s') = n
  >>.
Proof. 
  refine ( strengthen_pre_p
    (
      _ <-- extract_n_pre_length 8 _ ;
      _ <-- extract_n_pre_length 8 _ ;
      extract_n_pre_length 4 _
    ) _
  ).
  intros.  lia.
Qed.

Lemma IPHeader_p_length n: 
  << fun s => length (pkt s) = 20 + n >>
    IPHeader_p
  << fun r s' => 
    length (pkt s') = n
  >>.
Proof.
  unfold IPHeader_p.
  refine ( strengthen_pre_p
    (
      src <-- extract_n_pre_length 8 _ ;
      dst <-- extract_n_pre_length 8 _ ;
      proto <-- extract_n_pre_length 4 _ ;
      return_wp_p (RCons src (RCons dst (RCons proto REmp)))
    ) _
  ).
  intros. lia.
Qed.

Lemma ParseTCPCorrect pckt :
  << fun s => pkt s = pckt /\ HeaderWF (pkt s) /\ IPHeaderIsTCP (pkt s) >>
    MyProg pckt
  << fun _ s => EgressSpecZero s >>.
Admitted.

Lemma ParseUDPCorrect pckt :
  << fun s => pkt s = pckt /\ HeaderWF (pkt s) /\ IPHeaderIsUDP (pkt s) >>
    MyProg pckt
  << fun _ s => EgressSpecOne s >>.
Admitted.

Theorem ParseComplete pckt : 
  << fun s => 
    pkt s = pckt /\ 
    HeaderWF (pkt s) /\ 
    (IPHeaderIsUDP (pkt s) \/ IPHeaderIsTCP (pkt s))
  >>
    MyProg pckt
  << fun _ s' => PacketConsumed s' >>.
Admitted.
