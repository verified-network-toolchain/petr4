Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Poulet4.Utils.Util.FunUtil.
Require Import Poulet4.Utils.AList.

Section TRAFFIC_MANAGER.

  Parameter Port: Type.
  Parameter Header: Type.
  Parameter port_eq_dec: EqDec Port eq.

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

  Definition IngressPacket := (InputMetadata * Header)%type.

  Record OutputMetadata := {
      out_meta_egress_port: Port;
      out_meta_egress_rid: Z;
    }.

  Definition EgressPacket := (OutputMetadata * Header)%type.

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
    (input: IngressPacket):
    list EgressPacket :=
    let (meta, header) := input in
    flat_map
      (fun n1 =>
         if n1.(mcast_l1_xid_valid) &&
              (n1.(mcast_l1_xid) =? meta.(in_meta_level1_exclusion_id))
         then nil
         else prune_option $ map
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
                n1.(mcast_n1_dev_port_list))
      mcast_group.

  Definition multicast_engine
    (mc_tbl: AList Z multicast_group (@eq Z))
    (excl_table: L2_exclusion_table)
    (input: IngressPacket):
    list EgressPacket :=
    let (meta, header) := input in
    let dup_packet (grp_idx: option Z): list EgressPacket :=
      match grp_idx with
      | None => nil
      | Some grp =>
          match get mc_tbl grp with
          | None => nil
          | Some mcast_grp => packet_replication mcast_grp excl_table input
          end
      end in
    (dup_packet meta.(in_meta_mcast_grp_a)) ++
      dup_packet meta.(in_meta_mcast_grp_b).

  Definition unicast_engine (input: IngressPacket): option EgressPacket :=
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
    (input: IngressPacket):
    list EgressPacket :=
    match unicast_engine input with
    | None => multicast_engine mc_tbl excl_table input
    | Some p => p :: multicast_engine mc_tbl excl_table input
    end.

End TRAFFIC_MANAGER.
