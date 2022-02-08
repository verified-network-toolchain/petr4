error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument
}

extern packet_in {
    void extract<T>(out T hdr);
    void extract<T>(out T variableSizeHeader, in bit<32> variableFieldSizeInBits);
    T lookahead<T>();
    void advance(in bit<32> sizeInBits);
    bit<32> length();
}

extern packet_out {
    void emit<T>(in T hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

match_kind {
    range,
    optional,
    selector
}

const bit<32> __v1model_version = 20180101;
@metadata @name("standard_metadata") struct standard_metadata_t {
    bit<9>  ingress_port;
    bit<9>  egress_spec;
    bit<9>  egress_port;
    bit<32> instance_type;
    bit<32> packet_length;
    @alias("queueing_metadata.enq_timestamp") 
    bit<32> enq_timestamp;
    @alias("queueing_metadata.enq_qdepth") 
    bit<19> enq_qdepth;
    @alias("queueing_metadata.deq_timedelta") 
    bit<32> deq_timedelta;
    @alias("queueing_metadata.deq_qdepth") 
    bit<19> deq_qdepth;
    @alias("intrinsic_metadata.ingress_global_timestamp") 
    bit<48> ingress_global_timestamp;
    @alias("intrinsic_metadata.egress_global_timestamp") 
    bit<48> egress_global_timestamp;
    @alias("intrinsic_metadata.mcast_grp") 
    bit<16> mcast_grp;
    @alias("intrinsic_metadata.egress_rid") 
    bit<16> egress_rid;
    bit<1>  checksum_error;
    error   parser_error;
    @alias("intrinsic_metadata.priority") 
    bit<3>  priority;
}

enum CounterType {
    packets,
    bytes,
    packets_and_bytes
}

enum MeterType {
    packets,
    bytes
}

extern counter {
    counter(bit<32> size, CounterType type);
    void count(in bit<32> index);
}

extern direct_counter {
    direct_counter(CounterType type);
    void count();
}

extern meter {
    meter(bit<32> size, MeterType type);
    void execute_meter<T>(in bit<32> index, out T result);
}

extern direct_meter<T> {
    direct_meter(MeterType type);
    void read(out T result);
}

extern register<T> {
    register(bit<32> size);
    @noSideEffects void read(out T result, in bit<32> index);
    void write(in bit<32> index, in T value);
}

extern action_profile {
    action_profile(bit<32> size);
}

extern void random<T>(out T result, in T lo, in T hi);
extern void digest<T>(in bit<32> receiver, in T data);
enum HashAlgorithm {
    crc32,
    crc32_custom,
    crc16,
    crc16_custom,
    random,
    identity,
    csum16,
    xor16
}

@deprecated("Please use mark_to_drop(standard_metadata) instead.") extern void mark_to_drop();
@pure extern void mark_to_drop(inout standard_metadata_t standard_metadata);
@pure extern void hash<O, T, D, M>(out O result, in HashAlgorithm algo, in T base, in D data, in M max);
extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

enum CloneType {
    I2E,
    E2E
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

extern void verify_checksum<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@pure extern void update_checksum<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
extern void verify_checksum_with_payload<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@noSideEffects extern void update_checksum_with_payload<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
extern void clone(in CloneType type, in bit<32> session);
@deprecated("Please use 'resubmit_preserving_field_list' instead") extern void resubmit<T>(in T data);
extern void resubmit_preserving_field_list(bit<8> index);
@deprecated("Please use 'recirculate_preserving_field_list' instead") extern void recirculate<T>(in T data);
extern void recirculate_preserving_field_list(bit<8> index);
@deprecated("Please use 'clone_preserving_field_list' instead") extern void clone3<T>(in CloneType type, in bit<32> session, in T data);
extern void clone_preserving_field_list(in CloneType type, in bit<32> session, bit<8> index);
extern void truncate(in bit<32> length);
extern void assert(in bool check);
extern void assume(in bool check);
extern void log_msg(string msg);
extern void log_msg<T>(string msg, in T data);
parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
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

@controller_header("packet_in") header packet_in_header_t {
    port_num_t ingress_port;
    bit<7>     _pad;
}

@controller_header("packet_out") header packet_out_header_t {
    port_num_t egress_port;
    bit<7>     _pad;
}

header ethernet_t {
    mac_addr_t dst_addr;
    mac_addr_t src_addr;
    bit<16>    eth_type;
}

header vlan_tag_t {
    bit<3>    pri;
    bit<1>    cfi;
    vlan_id_t vlan_id;
    bit<16>   eth_type;
}

header mpls_t {
    bit<20> label;
    bit<3>  tc;
    bit<1>  bos;
    bit<8>  ttl;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<6>  dscp;
    bit<2>  ecn;
    bit<16> total_len;
    bit<16> identification;
    bit<3>  flags;
    bit<13> frag_offset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdr_checksum;
    bit<32> src_addr;
    bit<32> dst_addr;
}

header ipv6_t {
    bit<4>   version;
    bit<8>   traffic_class;
    bit<20>  flow_label;
    bit<16>  payload_len;
    bit<8>   next_hdr;
    bit<8>   hop_limit;
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
    bit<8>  icmp_type;
    bit<8>  icmp_code;
    bit<16> checksum;
    bit<16> identifier;
    bit<16> sequence_number;
    bit<64> timestamp;
}

struct fabric_metadata_t {
    bit<16>      eth_type;
    bit<16>      ip_eth_type;
    vlan_id_t    vlan_id;
    bit<3>       vlan_pri;
    bit<1>       vlan_cfi;
    mpls_label_t mpls_label;
    bit<8>       mpls_ttl;
    bool         skip_forwarding;
    bool         skip_next;
    fwd_type_t   fwd_type;
    next_id_t    next_id;
    bool         is_multicast;
    bool         is_controller_packet_out;
    bool         clone_to_cpu;
    bit<8>       ip_proto;
    bit<16>      l4_sport;
    bit<16>      l4_dport;
}

struct parsed_headers_t {
    ethernet_t          ethernet;
    vlan_tag_t          vlan_tag;
    vlan_tag_t          inner_vlan_tag;
    mpls_t              mpls;
    ipv4_t              ipv4;
    tcp_t               tcp;
    udp_t               udp;
    icmp_t              icmp;
    packet_out_header_t packet_out;
    packet_in_header_t  packet_in;
}

control Forwarding(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @hidden action set_next_id(next_id_t next_id) {
        fabric_metadata.next_id = next_id;
    }
    direct_counter(CounterType.packets_and_bytes) bridging_counter;
    action set_next_id_bridging(next_id_t next_id) {
        set_next_id(next_id);
        bridging_counter.count();
    }
    table bridging {
        key = {
            fabric_metadata.vlan_id: exact @name("vlan_id") ;
            hdr.ethernet.dst_addr  : ternary @name("eth_dst") ;
        }
        actions = {
            set_next_id_bridging();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = bridging_counter;
        size = BRIDGING_TABLE_SIZE;
    }
    direct_counter(CounterType.packets_and_bytes) mpls_counter;
    action pop_mpls_and_next(next_id_t next_id) {
        fabric_metadata.mpls_label = 0;
        set_next_id(next_id);
        mpls_counter.count();
    }
    table mpls {
        key = {
            fabric_metadata.mpls_label: exact @name("mpls_label") ;
        }
        actions = {
            pop_mpls_and_next();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = mpls_counter;
        size = MPLS_TABLE_SIZE;
    }
    direct_counter(CounterType.packets_and_bytes) routing_v4_counter;
    action set_next_id_routing_v4(next_id_t next_id) {
        set_next_id(next_id);
        routing_v4_counter.count();
    }
    action nop_routing_v4() {
        routing_v4_counter.count();
    }
    table routing_v4 {
        key = {
            hdr.ipv4.dst_addr: lpm @name("ipv4_dst") ;
        }
        actions = {
            set_next_id_routing_v4();
            nop_routing_v4();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = routing_v4_counter;
        size = ROUTING_V4_TABLE_SIZE;
    }
    apply {
        if (fabric_metadata.fwd_type == FWD_BRIDGING) {
            bridging.apply();
        } else if (fabric_metadata.fwd_type == FWD_MPLS) {
            mpls.apply();
        } else if (fabric_metadata.fwd_type == FWD_IPV4_UNICAST) {
            routing_v4.apply();
        }
    }
}

