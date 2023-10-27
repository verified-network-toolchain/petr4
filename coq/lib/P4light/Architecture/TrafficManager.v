Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.Utils.Util.FunUtil.
Require Import Poulet4.Utils.AList.
Require Export Poulet4.P4light.Architecture.Queue.

Section TRAFFIC_MANAGER.

  Variable Port: Type.
  Variable Header: Type.
  Variable port_eq_dec: EqDec Port eq.

  Open Scope bool_scope.
  Open Scope Z_scope.

  #[local] Instance ZEqDec: EqDec Z eq := Z.eq_dec.

  Record InputMetadata := {
      in_meta_ucast_egress_port: option Port;
      in_meta_mcast_grp_a: option Z;
      in_meta_mcast_grp_b: option Z;
      in_meta_rid: Z;
      in_meta_level1_exclusion_id: Z;
      in_meta_level2_exclusion_id: Z;
    }.

  Definition IngressPacketDescriptor := (InputMetadata * Header)%type.

  Record OutputMetadata := {
      out_meta_egress_port: Port;
      out_meta_egress_rid: Z;
    }.

  Definition EgressPacketDescriptor := (OutputMetadata * Header)%type.

  Record MulticastLevel1Node := {
      mcast_n1_rid: Z; (* A 16-bit replication id *)
      mcast_l1_xid: Z; (* a 16-bit level 1 exclusion id *)
      mcast_l1_xid_valid: bool; (* a 1-bit field that is 1 if L1_XID is valid *)
      mcast_n1_dev_port_list: list Port; (* A list of individual ports *)
    }.

  Definition L2_exclusion_table := Z -> list Port.

  Definition multicast_group := list MulticastLevel1Node.

  Definition multicast_table := AList Z multicast_group (@eq Z).

  Fixpoint prune_option {A: Type} (l: list (option A)) : list A :=
    match l with
    | nil => nil
    | None :: rest => prune_option rest
    | Some a :: rest => a :: prune_option rest
    end.

  Definition packet_replication
    (mcast_group: multicast_group)
    (excl_table: L2_exclusion_table)
    (input: IngressPacketDescriptor):
    list EgressPacketDescriptor :=
    let (meta, header) := input in
    flat_map
      (fun n1 =>
         if n1.(mcast_l1_xid_valid) &&
              (n1.(mcast_l1_xid) =? meta.(in_meta_level1_exclusion_id))
         then nil
         else prune_option
                (map
                   (fun port =>
                      if (meta.(in_meta_rid) =? n1.(mcast_n1_rid)) &&
                           proj1_sig
                             (Sumbool.bool_of_sumbool
                                (in_dec port_eq_dec port
                                   (excl_table meta.(in_meta_level2_exclusion_id))))
                      then None
                      else Some ({| out_meta_egress_port := port;
                                   out_meta_egress_rid := n1.(mcast_n1_rid); |},
                               header))
                   n1.(mcast_n1_dev_port_list)))
      mcast_group.

  Definition multicast_engine
    (mc_tbl: multicast_table)
    (excl_table: L2_exclusion_table)
    (input: IngressPacketDescriptor):
    queue EgressPacketDescriptor :=
    let (meta, header) := input in
    let dup_packet (grp_idx: option Z): list EgressPacketDescriptor :=
      match grp_idx with
      | None => nil
      | Some grp =>
          match get mc_tbl grp with
          | None => nil
          | Some mcast_grp => packet_replication mcast_grp excl_table input
          end
      end in
    list_enque (dup_packet meta.(in_meta_mcast_grp_b))
      (list_to_queue (dup_packet meta.(in_meta_mcast_grp_a))).

  Definition unicast_engine (input: IngressPacketDescriptor):
    option EgressPacketDescriptor :=
    let (meta, header) := input in
    match meta.(in_meta_ucast_egress_port) with
    | None => None
    | Some port => Some ({| out_meta_egress_port := port;
                          out_meta_egress_rid := 0; |},
                      header)
    end.

  Definition traffic_manager
    (mc_tbl: multicast_table)
    (excl_table: L2_exclusion_table)
    (input: IngressPacketDescriptor):
    queue EgressPacketDescriptor :=
    match unicast_engine input with
    | None => multicast_engine mc_tbl excl_table input
    | Some p => enque p (multicast_engine mc_tbl excl_table input)
    end.

  Ltac destruct_if H := match goal with
                        | H: context [match ?p with | _ => _ end] |- _ => destruct p
                        end.

  Lemma packet_replication_output_snd:
    forall (excl_table : L2_exclusion_table) (output : EgressPacketDescriptor)
      (m : multicast_group) (input : InputMetadata * Header),
      In output (packet_replication m excl_table input) -> snd output = snd input.
  Proof.
    intros. destruct input. simpl in *. induction m; simpl in *. 1: contradiction.
    rewrite in_app_iff in H. destruct H; [clear IHm | apply IHm; assumption].
    destruct_if H; [contradiction |]. remember (mcast_n1_dev_port_list a). clear Heql.
    induction l; try contradiction. remember (fun port: Port => _) as f in H.
    rewrite <- Heqf in IHl. simpl in H. destruct (f a0) eqn:?; [|apply IHl; assumption].
    simpl in H. destruct H; [|apply IHl; assumption]. clear IHl. subst.
    destruct_if Heqo; inversion Heqo. simpl. reflexivity.
  Qed.

  Lemma multicast_engine_output_snd:
    forall (mc_tbl : multicast_table) (excl_table : L2_exclusion_table)
      (input : IngressPacketDescriptor) (output : EgressPacketDescriptor),
      In output (list_rep (multicast_engine mc_tbl excl_table input)) ->
      snd output = snd input.
  Proof.
    intros. unfold multicast_engine in H. destruct input; simpl.
    rewrite list_enque_eq, list_to_queue_eq, in_app_iff in H.
    destruct H; [destruct (in_meta_mcast_grp_a i) | destruct (in_meta_mcast_grp_b i)];
      try contradiction; destruct (get mc_tbl z); try contradiction;
      change h with (snd (i, h)); eapply packet_replication_output_snd; eauto.
  Qed.

  Lemma traffic_manager_output_snd: forall mc_tbl excl_table input output,
      In output (list_rep (traffic_manager mc_tbl excl_table input)) ->
      snd output = snd input.
  Proof.
    intros. unfold traffic_manager in H. destruct (unicast_engine input) eqn:?.
    - rewrite enque_eq, in_app_iff in H. destruct H.
      + apply multicast_engine_output_snd in H. assumption.
      + simpl in H. destruct H; try contradiction. subst e. unfold unicast_engine in Heqo.
        destruct input, (in_meta_ucast_egress_port i); [|discriminate]. inversion Heqo.
        simpl. reflexivity.
    - apply multicast_engine_output_snd in H. assumption.
  Qed.

End TRAFFIC_MANAGER.

Arguments Build_MulticastLevel1Node {_}.
Arguments Build_InputMetadata {_}.
Arguments traffic_manager {_ _ _}.
Arguments out_meta_egress_port {_}.
Arguments out_meta_egress_rid {_}.
