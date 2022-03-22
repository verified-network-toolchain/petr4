/petr4/ci-test/type-checking/testdata/p4_16_samples/fabric_20190420/include/header.p4
\n
/*
 * Copyright 2017-present Open Networking Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __HEADER__
#define __HEADER__

#include "define.p4"
#include "int/int_header.p4"

@controller_header("packet_in")
header packet_in_header_t {
    port_num_t ingress_port;
    bit<7> _pad;
}

_PKT_OUT_HDR_ANNOT
@controller_header("packet_out")
header packet_out_header_t {
    port_num_t egress_port;
    bit<7> _pad;
}

header ethernet_t {
    mac_addr_t dst_addr;
    mac_addr_t src_addr;
    bit<16> eth_type;
}

header vlan_tag_t {
    bit<3> pri;
    bit<1> cfi;
    vlan_id_t vlan_id;
    bit<16> eth_type;
}

header mpls_t {
    bit<20> label;
    bit<3> tc;
    bit<1> bos;
    bit<8> ttl;
}

header ipv4_t {
    bit<4> version;
    bit<4> ihl;
    bit<6> dscp;
    bit<2> ecn;
    bit<16> total_len;
    bit<16> identification;
    bit<3> flags;
    bit<13> frag_offset;
    bit<8> ttl;
    bit<8> protocol;
    bit<16> hdr_checksum;
    bit<32> src_addr;
    bit<32> dst_addr;
}

header ipv6_t {
    bit<4> version;
    bit<8> traffic_class;
    bit<20> flow_label;
    bit<16> payload_len;
    bit<8> next_hdr;
    bit<8> hop_limit;
    bit<128> src_addr;
    bit<128> dst_addr;
}

header tcp_t {
    bit<16> sport;
    bit<16> dport;
    bit<32> seq_no;
    bit<32> ack_no;
    bit<4>  data_offset;
    bit<3>  res;
    bit<3>  ecn;
    bit<6>  ctrl;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgent_ptr;
}

header udp_t {
    bit<16> sport;
    bit<16> dport;
    bit<16> len;
    bit<16> checksum;
}

header icmp_t {
    bit<8> icmp_type;
    bit<8> icmp_code;
    bit<16> checksum;
    bit<16> identifier;
    bit<16> sequence_number;
    bit<64> timestamp;
}

#ifdef WITH_SPGW
// GTPU v1
header gtpu_t {
    bit<3>  version;    /* version */
    bit<1>  pt;         /* protocol type */
    bit<1>  spare;      /* reserved */
    bit<1>  ex_flag;    /* next extension hdr present? */
    bit<1>  seq_flag;   /* sequence no. */
    bit<1>  npdu_flag;  /* n-pdn number present ? */
    bit<8>  msgtype;    /* message type */
    bit<16> msglen;     /* message length */
    bit<32> teid;       /* tunnel endpoint id */
}

struct spgw_meta_t {
    direction_t       direction;
    bit<16>           ipv4_len;
    bit<32>           teid;
    bit<32>           s1u_enb_addr;
    bit<32>           s1u_sgw_addr;
#ifdef WITH_SPGW_PCC_GATING
    bit<16>           l4_sport;
    bit<16>           l4_dport;
    pcc_gate_status_t pcc_gate_status;
    sdf_rule_id_t     sdf_rule_id;
    pcc_rule_id_t     pcc_rule_id;
#endif // WITH_SPGW_PCC_GATING
}
#endif // WITH_SPGW

//Custom metadata definition
struct fabric_metadata_t {
    bit<16>       eth_type;
    bit<16>       ip_eth_type;
    vlan_id_t     vlan_id;
    bit<3>        vlan_pri;
    bit<1>        vlan_cfi;
    mpls_label_t  mpls_label;
    bit<8>        mpls_ttl;
    _BOOL         skip_forwarding;
    _BOOL         skip_next;
    fwd_type_t    fwd_type;
    next_id_t     next_id;
    _BOOL         is_multicast;
    _BOOL         is_controller_packet_out;
    _BOOL         clone_to_cpu;
    bit<8>        ip_proto;
    bit<16>       l4_sport;
    bit<16>       l4_dport;
#ifdef WITH_SPGW
    spgw_meta_t   spgw;
#endif // WITH_SPGW
#ifdef WITH_INT
    int_metadata_t int_meta;
#endif // WITH_INT
}

struct parsed_headers_t {
    ethernet_t ethernet;
    vlan_tag_t vlan_tag;
#ifdef WITH_XCONNECT
    vlan_tag_t inner_vlan_tag;
#endif // WITH_XCONNECT
    mpls_t mpls;
#ifdef WITH_SPGW
    ipv4_t gtpu_ipv4;
    udp_t gtpu_udp;
    gtpu_t gtpu;
    ipv4_t inner_ipv4;
    udp_t inner_udp;
#endif // WITH_SPGW
    ipv4_t ipv4;
#ifdef WITH_IPV6
    ipv6_t ipv6;
#endif // WITH_IPV6
    tcp_t tcp;
    udp_t udp;
    icmp_t icmp;
    packet_out_header_t packet_out;
    packet_in_header_t packet_in;
#ifdef WITH_INT_SINK
    // INT Report encap
    ethernet_t report_ethernet;
    ipv4_t report_ipv4;
    udp_t report_udp;
    // INT Report header (support only fixed)
    report_fixed_header_t report_fixed_header;
    // local_report_t report_local;
#endif // WITH_INT_SINK
#ifdef WITH_INT
    // INT specific headers
    intl4_shim_t intl4_shim;
    int_header_t int_header;
    int_switch_id_t int_switch_id;
    int_port_ids_t int_port_ids;
    int_hop_latency_t int_hop_latency;
    int_q_occupancy_t int_q_occupancy;
    int_ingress_tstamp_t int_ingress_tstamp;
    int_egress_tstamp_t int_egress_tstamp;
    int_q_congestion_t int_q_congestion;
    int_egress_port_tx_util_t int_egress_tx_util;
#ifdef WITH_INT_SINK
    int_data_t int_data;
#endif // WITH_INT_SINK
    intl4_tail_t intl4_tail;
#endif //WITH_INT
}

#endif
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  Petr4.Prog.Env.UnboundName("NoAction")

Raised at Petr4__Prog.Env.raise_unbound in file "lib/prog.ml", line 1455, characters 4-32
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 849, characters 22-54
Called from Petr4__Checker.resolve_function_overload_by in file "lib/checker.ml", line 2478, characters 19-47
Called from Petr4__Checker.type_function_call in file "lib/checker.ml", line 2311, characters 19-62
Called from Petr4__Checker.type_method_call in file "lib/checker.ml", line 2678, characters 19-80
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2649, characters 7-61
Called from Petr4__Checker.type_statements.fold in file "lib/checker.ml", line 2782, characters 26-58
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Petr4__Checker.type_block in file "lib/checker.ml", line 2794, characters 27-73
Called from Petr4__Checker.type_function in file "lib/checker.ml", line 3148, characters 27-55
Called from Petr4__Checker.type_action in file "lib/checker.ml", line 3282, characters 4-83
Called from Petr4__Checker.type_declarations.f in file "lib/checker.ml", line 4118, characters 26-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_declarations in file "lib/checker.ml", line 4121, characters 19-58
Called from Petr4__Checker.check_program in file "lib/checker.ml", line 4128, characters 18-78
Called from Petr4__Common.Make_parse.check_file' in file "lib/common.ml", line 95, characters 17-51
Called from Petr4__Common.Make_parse.check_file in file "lib/common.ml", line 108, characters 10-50
Called from Main.check_command.(fun) in file "bin/main.ml", line 70, characters 14-65
Called from Core_kernel__Command.For_unix.run.(fun) in file "src/command.ml", line 2453, characters 8-238
Called from Base__Exn.handle_uncaught_aux in file "src/exn.ml", line 111, characters 6-10
************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/fabric_20190420/include/define.p4(166): [--Werror=not-found] error: NoAction: declaration not found
    NoAction();
    ^^^^^^^^
