typedef bit<3> fwd_type_t;
typedef bit<32> next_id_t;
typedef bit<20> mpls_label_t;
typedef bit<9> port_num_t;
typedef bit<48> mac_addr_t;
typedef bit<16> mcast_group_id_t;
typedef bit<12> vlan_id_t;
typedef bit<32> ipv4_addr_t;
typedef bit<16> l4_port_t;
typedef bit<2> direction_t;
typedef bit<1> pcc_gate_status_t;
typedef bit<32> sdf_rule_id_t;
typedef bit<32> pcc_rule_id_t;
const ipv4_addr_t S1U_SGW_PREFIX = 2348810240;
const bit<16> ETHERTYPE_QINQ = 0x88a8;
const bit<16> ETHERTYPE_QINQ_NON_STD = 0x9100;
const bit<16> ETHERTYPE_VLAN = 0x8100;
const bit<16> ETHERTYPE_MPLS = 0x8847;
const bit<16> ETHERTYPE_MPLS_MULTICAST = 0x8848;
const bit<16> ETHERTYPE_IPV4 = 0x800;
const bit<16> ETHERTYPE_IPV6 = 0x86dd;
const bit<16> ETHERTYPE_ARP = 0x806;
const bit<8> PROTO_ICMP = 1;
const bit<8> PROTO_TCP = 6;
const bit<8> PROTO_UDP = 17;
const bit<8> PROTO_ICMPV6 = 58;
const bit<4> IPV4_MIN_IHL = 5;
const fwd_type_t FWD_BRIDGING = 0;
const fwd_type_t FWD_MPLS = 1;
const fwd_type_t FWD_IPV4_UNICAST = 2;
const fwd_type_t FWD_IPV4_MULTICAST = 3;
const fwd_type_t FWD_IPV6_UNICAST = 4;
const fwd_type_t FWD_IPV6_MULTICAST = 5;
const fwd_type_t FWD_UNKNOWN = 7;
const vlan_id_t DEFAULT_VLAN_ID = 12w4094;
const bit<8> DEFAULT_MPLS_TTL = 64;
const bit<8> DEFAULT_IPV4_TTL = 64;
const sdf_rule_id_t DEFAULT_SDF_RULE_ID = 0;
const pcc_rule_id_t DEFAULT_PCC_RULE_ID = 0;
const direction_t SPGW_DIR_UNKNOWN = 2w0;
const direction_t SPGW_DIR_UPLINK = 2w1;
const direction_t SPGW_DIR_DOWNLINK = 2w2;
const pcc_gate_status_t PCC_GATE_OPEN = 1w0;
const pcc_gate_status_t PCC_GATE_CLOSED = 1w1;
const bit<6> INT_DSCP = 0x1;
const bit<8> INT_HEADER_LEN_WORDS = 4;
const bit<16> INT_HEADER_LEN_BYTES = 16;
const bit<8> CPU_MIRROR_SESSION_ID = 250;
const bit<32> REPORT_MIRROR_SESSION_ID = 500;
const bit<4> NPROTO_ETHERNET = 0;
const bit<4> NPROTO_TELEMETRY_DROP_HEADER = 1;
const bit<4> NPROTO_TELEMETRY_SWITCH_LOCAL_HEADER = 2;
const bit<6> HW_ID = 1;
const bit<8> REPORT_FIXED_HEADER_LEN = 12;
const bit<8> DROP_REPORT_HEADER_LEN = 12;
const bit<8> LOCAL_REPORT_HEADER_LEN = 16;
const bit<8> ETH_HEADER_LEN = 14;
const bit<8> IPV4_MIN_HEAD_LEN = 20;
const bit<8> UDP_HEADER_LEN = 8;
action nop() {
    NoAction();
}
struct int_metadata_t {
    bool    source;
    bool    transit;
    bool    sink;
    bit<32> switch_id;
    bit<8>  new_words;
    bit<16> new_bytes;
    bit<32> ig_tstamp;
    bit<32> eg_tstamp;
}

header int_header_t {
    bit<2>  ver;
    bit<2>  rep;
    bit<1>  c;
    bit<1>  e;
    bit<5>  rsvd1;
    bit<5>  ins_cnt;
    bit<8>  max_hop_cnt;
    bit<8>  total_hop_cnt;
    bit<4>  instruction_mask_0003;
    bit<4>  instruction_mask_0407;
    bit<4>  instruction_mask_0811;
    bit<4>  instruction_mask_1215;
    bit<16> rsvd2;
}

header intl4_shim_t {
    bit<8> int_type;
    bit<8> rsvd1;
    bit<8> len_words;
    bit<8> rsvd2;
}

header intl4_tail_t {
    bit<8>  next_proto;
    bit<16> dest_port;
    bit<2>  padding;
    bit<6>  dscp;
}

