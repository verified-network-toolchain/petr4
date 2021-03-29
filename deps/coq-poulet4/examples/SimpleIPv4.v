Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.P4Monad.
Require Import Monads.Hoare.WP.
Open Scope monad.
Require Import Lists.List.
Import ListNotations.
Require Import Program.

Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Plus.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.
Require Import Equations.Equations.

Notation REmp := HAList.REmp.
Notation RCons := HAList.RCons.

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

(* Set Equations Transparent. *)

Equations TCP_valid (tcp: TCP) : bool :=
  {
    TCP_valid (RCons (Some _) (RCons (Some _) (RCons (Some _) (RCons (Some _) _)))) := true;
    TCP_valid _ := false
  }.

Equations UDP_valid (udp: UDP) : bool :=
  {
    UDP_valid (RCons (Some _) (RCons (Some _) (RCons (Some _) _))) := true;
    UDP_valid _ := false
  }.

Equations IPHeader_valid (ihp: IPHeader) : bool :=
  {
    IPHeader_valid (RCons (Some _) (RCons (Some _) (RCons (Some _) _))) := true;
    IPHeader_valid _ := false
  }.

Lemma IPHeader_valid_destruct (iph: IPHeader) :
  IPHeader_valid iph = true -> 
  exists src dst proto, 
  iph = RCons (Some src) (RCons (Some dst) (RCons (Some proto) REmp)).
Proof.
Admitted.

Lemma Header_destruct (h: Headers) : 
  exists ip trans, h = RCons ip (RCons trans REmp).
Proof.
  unfold Headers in *.
  dependent destruction h.
  dependent destruction h.
  dependent destruction h.
  eauto.
Qed.

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

Ltac app_ex := 
  intros; match goal with 
  | [ H : _ |- _ ] => exact H 
  | [ H : (_ /\ _)%type |- _] => destruct H; app_ex
  | [ H : (exists _, _)%type |- _] => destruct H; app_ex
  end.
Ltac wp_trans :=
  intros; match goal with
  | [ |- << _ >> mbind _ _ << _ >> ] => eapply bind_wp_p; try wp_trans
  | [ |- << _ >> get_state << _ >> ] => eapply get_wp_p || eapply strengthen_pre_p; try eapply get_wp_p
  | [ |- << _ >> put_state ?e << _ >> ] => eapply (put_wp_p e) || eapply strengthen_pre_p; try eapply (put_wp_p e)
  | [ |- << _ >> state_fail ?e << _ >> ] => eapply (fail_wp_p e) || eapply strengthen_pre_p; try eapply (fail_wp_p e)
  | [ |- << _ >> state_return ?e << _ >> ] => eapply (return_wp_p e) || eapply strengthen_pre_p; try eapply (return_wp_p e)
  | [ |- << _ >> if _ then _ else _ << _ >> ] => eapply cond_wp_p; eapply strengthen_pre_p; try wp_trans
  | [ |- << _ >> match ?e with | 0 => _ | S _ => _ end << _ >> ] => eapply (case_nat_wp_p e); eapply strengthen_pre_p; try wp_trans
  | [ |- << _ >> match ?e with | nil => _ | _ :: _ => _ end << _ >> ] => eapply (case_list_wp_p e); eapply strengthen_pre_p; try wp_trans
  | [ |- << _ >> match ?e with | Some _ => _ | None => _ end << _ >> ] => eapply (case_option_wp_p e); eapply strengthen_pre_p; try wp_trans
  end.

(* Lemma extract_2_twice' : 
  << fun s => length (pkt s) >= 2 >> 
    r1 <- extract_n 1 ;;
    r2 <- extract_n 1 ;; 
    state_return (r1, r2)
  << fun r s' => 
    match r with 
    | (Some l, Some r) => True
    | _ => False 
    end
  >>.
Proof.
  unfold extract_n, next_bit, pure.
  wp_trans; try app_ex. 
  intros.
  simpl.
  destruct (pkt h).
  - exfalso. simpl in H. lia.
  - destruct l.
    + exfalso. simpl in H. lia.
    + simpl. trivial.
  Unshelve.
  all: (exact true || exact tt).
Qed. *)

Ltac mylen ls := 
  match ls with 
  | _ :: ?tl => 
    let l' := mylen tl in 
    constr:(S l')
  | _ => 0
  end.

Ltac myinduct l := destruct l; (simpl; try (exfalso; simpl in *; lia)).

Definition hal_get := 
  let foo_t := HAList.t [("field", option bool)] in 
  let foo : foo_t := RCons (Some true) REmp in
  HAList.get foo (exist _ "field" I)
  .
Lemma hg : hal_get = Some true.
Proof. 
  unfold hal_get.
  unfold HAList.get.
  now autorewrite with get_k.
Qed.

(* All three of these functional correctness proofs work in my editor but
 * coqc times out on my laptop, so I've commented out the proof. 
 *)

Lemma IPHeader_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 20 >>
    IPHeader_p
  << fun r s' => 
    IPHeader_valid r = true /\ 
    s' = st <| pkt := skipn 20 (pkt st) |> 
  >>.
(* Proof.
  unfold IPHeader_p, extract_n, next_bit, pure.
  eapply strengthen_pre_p.
  wp_trans.
  all: swap -1 1.
  
  intros. simpl.
  assert (pkt h = pkt st).
  destruct H as [eq _].
  rewrite eq; trivial.
  all: swap -1 1.

  1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20: app_ex.
  all: swap -1 1.

  simpl.
  myinduct (pkt h).
  myinduct l.
  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1.

  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1.

  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 

  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.
  myinduct l.
  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.


  myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3: app_ex.
  all: swap -1 1. 
  simpl.

  2,3,4: app_ex.
  simpl.
  2,3,4: app_ex.
  2,3,4: app_ex.
  2: app_ex.
  simpl.
  myinduct l.
  split.
  apply IPHeader_valid_equation_1.
  rewrite <- H0.
  compute.
  destruct H as [eq _].
  rewrite eq.
  trivial.

  Unshelve.

  all: (
    exact true || 
    exact zero_bits
  ).
Qed. *)
Admitted.

Lemma TCP_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 28 >>
    TCP_p
  << fun r s' => 
    TCP_valid r = true /\ 
    s' = st <| pkt := skipn 28 (pkt st) |> 
  >>.
(* Proof.
  unfold TCP_p, extract_n, next_bit, pure.
  eapply strengthen_pre_p.
  wp_trans.
  all: swap -1 1.
  
  intros. simpl.
  assert (pkt h = pkt st).
  destruct H as [eq _].
  rewrite eq; trivial.
  all: swap -1 1.

  1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20: app_ex.
  all: swap -1 1.

  simpl.
  myinduct (pkt h).
  myinduct l.
  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1.

  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1.

  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 

  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.
  myinduct l.
  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l. myinduct l.

  
  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.
  myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl.
  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  2,3,4: app_ex.
  simpl.
  2,3: app_ex.
  simpl.
  split.
  - apply TCP_valid_equation_1.
  - rewrite <- H0.
    simpl.
    destruct H as [eq _].
    rewrite eq.
    trivial.
  Unshelve.

  all: (
    exact true || 
    exact zero_bits
  ).
Qed. *)
Admitted.

Lemma UDP_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 20 >>
    UDP_p
  << fun r s' => 
    UDP_valid r = true /\ 
    s' = st <| pkt := skipn 20 (pkt st) |> 
  >>.
(* Proof.
  unfold UDP_p, extract_n, next_bit, pure.
  eapply strengthen_pre_p.
  wp_trans.
  all: swap -1 1.
  
  intros. simpl.
  assert (pkt h = pkt st).
  destruct H as [eq _].
  rewrite eq; trivial.
  all: swap -1 1.

  1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20: app_ex.
  all: swap -1 1.

  simpl.
  myinduct (pkt h).
  myinduct l.
  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1.

  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1.

  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 

  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl. myinduct l. myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.

  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.

  myinduct l.
  myinduct l.
  all: swap -1 1.
  1,2,3,4,5,6,7,8,9,10: app_ex.
  all: swap -1 1. 
  simpl.


  myinduct l.

  all: swap -1 1.
  1,2,3,4,5: app_ex.
  all: swap -1 1. 
  simpl. myinduct l.

  all: swap -1 1.
  1,2,3: app_ex.
  all: swap -1 1. 
  simpl.

  2,3,4: app_ex.
  simpl.
  2,3,4: app_ex.
  2,3,4: app_ex.
  2: app_ex.
  simpl.
  myinduct l.
  split.
  - apply UDP_valid_equation_1.
  - rewrite <- H0.
    simpl.
    destruct H as [eq _].
    rewrite eq.
    trivial.

  Unshelve.

  all: (
    exact true || 
    exact zero_bits
  ).
Qed. *)
Admitted.

Lemma ParseTCPCorrect pckt :
  << fun s => pkt s = pckt /\ HeaderWF (pkt s) /\ IPHeaderIsTCP (pkt s) >>
    MyProg pckt
  << fun _ s => EgressSpecZero s >>.
Proof.
  unfold MyProg, Headers_p.
  repeat match goal with
         | |- forall _, _ => intros
         | |- << _ >> IPHeader_p << _ >> => eapply (IPHeader_p_spec (init_state pckt))
         | |- _ => wp
         end.
  - unfold hoare_partial_wp; intros.
    intuition.
    admit.
  - admit.
  - admit.
  - destruct (Header_destruct r0) as [ip [trans pred]].
    unfold EgressSpecZero.
    rewrite pred.
    unfold MyIngress.
    set (k:= HAList.get (RCons ip (RCons trans REmp))
                        (exist (fun k : string => @HAList.alist_In _ _ P4String.StrEqDec _ k [("ip", IPHeader); ("transport", (TCP + UDP)%type)]) "transport" I)).
    replace k with trans by reflexivity.
    destruct trans.
    + admit.
    + admit.
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
