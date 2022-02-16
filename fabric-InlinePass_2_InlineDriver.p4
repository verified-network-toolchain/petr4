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

const bit<32> __v1model_version = 32w20180101;
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

@pure extern void mark_to_drop(inout standard_metadata_t standard_metadata);
extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

extern void verify_checksum<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@pure extern void update_checksum<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
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
typedef bit<2> direction_t;
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

header gtpu_t {
    bit<3>  version;
    bit<1>  pt;
    bit<1>  spare;
    bit<1>  ex_flag;
    bit<1>  seq_flag;
    bit<1>  npdu_flag;
    bit<8>  msgtype;
    bit<16> msglen;
    bit<32> teid;
}

struct spgw_meta_t {
    direction_t direction;
    bit<16>     ipv4_len;
    bit<32>     teid;
    bit<32>     s1u_enb_addr;
    bit<32>     s1u_sgw_addr;
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
    spgw_meta_t  spgw;
}

struct parsed_headers_t {
    ethernet_t          ethernet;
    vlan_tag_t          vlan_tag;
    vlan_tag_t          inner_vlan_tag;
    mpls_t              mpls;
    ipv4_t              gtpu_ipv4;
    udp_t               gtpu_udp;
    gtpu_t              gtpu;
    ipv4_t              inner_ipv4;
    udp_t               inner_udp;
    ipv4_t              ipv4;
    tcp_t               tcp;
    udp_t               udp;
    icmp_t              icmp;
    packet_out_header_t packet_out;
    packet_in_header_t  packet_in;
}

control Filtering(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @name("ingress_port_vlan_counter") direct_counter(CounterType.packets_and_bytes) ingress_port_vlan_counter_0;
    @name("deny") action deny_0() {
        fabric_metadata.skip_forwarding = true;
        fabric_metadata.skip_next = true;
        ingress_port_vlan_counter_0.count();
    }
    @name("permit") action permit_0() {
        ingress_port_vlan_counter_0.count();
    }
    @name("permit_with_internal_vlan") action permit_with_internal_vlan_0(@name("vlan_id") vlan_id_t vlan_id_0) {
        fabric_metadata.vlan_id = vlan_id_0;
        ingress_port_vlan_counter_0.count();
    }
    @name("ingress_port_vlan") table ingress_port_vlan_0 {
        key = {
            standard_metadata.ingress_port: exact @name("ig_port") ;
            hdr.vlan_tag.isValid()        : exact @name("vlan_is_valid") ;
            hdr.vlan_tag.vlan_id          : ternary @name("vlan_id") ;
        }
        actions = {
            deny_0();
            permit_0();
            permit_with_internal_vlan_0();
        }
        const default_action = deny_0();
        counters = ingress_port_vlan_counter_0;
        size = 1024;
    }
    @name("fwd_classifier_counter") direct_counter(CounterType.packets_and_bytes) fwd_classifier_counter_0;
    @name("set_forwarding_type") action set_forwarding_type_0(@name("fwd_type") fwd_type_t fwd_type_0) {
        fabric_metadata.fwd_type = fwd_type_0;
        fwd_classifier_counter_0.count();
    }
    @name("fwd_classifier") table fwd_classifier_0 {
        key = {
            standard_metadata.ingress_port: exact @name("ig_port") ;
            hdr.ethernet.dst_addr         : ternary @name("eth_dst") ;
            fabric_metadata.eth_type      : exact @name("eth_type") ;
        }
        actions = {
            set_forwarding_type_0();
        }
        const default_action = set_forwarding_type_0(3w0);
        counters = fwd_classifier_counter_0;
        size = 1024;
    }
    apply {
        if (hdr.vlan_tag.isValid()) {
            fabric_metadata.eth_type = hdr.vlan_tag.eth_type;
            fabric_metadata.vlan_id = hdr.vlan_tag.vlan_id;
            fabric_metadata.vlan_pri = hdr.vlan_tag.pri;
            fabric_metadata.vlan_cfi = hdr.vlan_tag.cfi;
        }
        if (hdr.mpls.isValid()) {
            ;
        } else {
            fabric_metadata.mpls_ttl = 8w65;
        }
        ingress_port_vlan_0.apply();
        fwd_classifier_0.apply();
    }
}

control Forwarding(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @hidden @name("set_next_id") action set_next_id_0(@name("next_id") next_id_t next_id_0) {
        fabric_metadata.next_id = next_id_0;
    }
    @name("bridging_counter") direct_counter(CounterType.packets_and_bytes) bridging_counter_0;
    @name("set_next_id_bridging") action set_next_id_bridging_0(@name("next_id") next_id_t next_id_1) {
        set_next_id_0(next_id_1);
        bridging_counter_0.count();
    }
    @name("bridging") table bridging_0 {
        key = {
            fabric_metadata.vlan_id: exact @name("vlan_id") ;
            hdr.ethernet.dst_addr  : ternary @name("eth_dst") ;
        }
        actions = {
            set_next_id_bridging_0();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = bridging_counter_0;
        size = 1024;
    }
    @name("mpls_counter") direct_counter(CounterType.packets_and_bytes) mpls_counter_0;
    @name("pop_mpls_and_next") action pop_mpls_and_next_0(@name("next_id") next_id_t next_id_2) {
        fabric_metadata.mpls_label = 20w0;
        set_next_id_0(next_id_2);
        mpls_counter_0.count();
    }
    @name("mpls") table mpls_0 {
        key = {
            fabric_metadata.mpls_label: exact @name("mpls_label") ;
        }
        actions = {
            pop_mpls_and_next_0();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = mpls_counter_0;
        size = 1024;
    }
    @name("routing_v4_counter") direct_counter(CounterType.packets_and_bytes) routing_v4_counter_0;
    @name("set_next_id_routing_v4") action set_next_id_routing_v4_0(@name("next_id") next_id_t next_id_3) {
        set_next_id_0(next_id_3);
        routing_v4_counter_0.count();
    }
    @name("nop_routing_v4") action nop_routing_v4_0() {
        routing_v4_counter_0.count();
    }
    @name("routing_v4") table routing_v4_0 {
        key = {
            hdr.ipv4.dst_addr: lpm @name("ipv4_dst") ;
        }
        actions = {
            set_next_id_routing_v4_0();
            nop_routing_v4_0();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = routing_v4_counter_0;
        size = 1024;
    }
    apply {
        if (fabric_metadata.fwd_type == 3w0) {
            bridging_0.apply();
        } else if (fabric_metadata.fwd_type == 3w1) {
            mpls_0.apply();
        } else if (fabric_metadata.fwd_type == 3w2) {
            routing_v4_0.apply();
        }
    }
}

control Acl(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @name("acl_counter") direct_counter(CounterType.packets_and_bytes) acl_counter_0;
    @name("set_next_id_acl") action set_next_id_acl_0(@name("next_id") next_id_t next_id_4) {
        fabric_metadata.next_id = next_id_4;
        acl_counter_0.count();
    }
    @name("punt_to_cpu") action punt_to_cpu_0() {
        standard_metadata.egress_spec = 9w255;
        fabric_metadata.skip_next = true;
        acl_counter_0.count();
    }
    @name("clone_to_cpu") action clone_to_cpu_0() {
        fabric_metadata.clone_to_cpu = true;
        acl_counter_0.count();
    }
    @name("drop") action drop_0() {
        mark_to_drop(standard_metadata);
        fabric_metadata.skip_next = true;
        acl_counter_0.count();
    }
    @name("nop_acl") action nop_acl_0() {
        acl_counter_0.count();
    }
    @name("acl") table acl_0 {
        key = {
            standard_metadata.ingress_port: ternary @name("ig_port") ;
            fabric_metadata.ip_proto      : ternary @name("ip_proto") ;
            fabric_metadata.l4_sport      : ternary @name("l4_sport") ;
            fabric_metadata.l4_dport      : ternary @name("l4_dport") ;
            hdr.ethernet.dst_addr         : ternary @name("eth_src") ;
            hdr.ethernet.src_addr         : ternary @name("eth_dst") ;
            hdr.vlan_tag.vlan_id          : ternary @name("vlan_id") ;
            fabric_metadata.eth_type      : ternary @name("eth_type") ;
            hdr.ipv4.src_addr             : ternary @name("ipv4_src") ;
            hdr.ipv4.dst_addr             : ternary @name("ipv4_dst") ;
            hdr.icmp.icmp_type            : ternary @name("icmp_type") ;
            hdr.icmp.icmp_code            : ternary @name("icmp_code") ;
        }
        actions = {
            set_next_id_acl_0();
            punt_to_cpu_0();
            clone_to_cpu_0();
            drop_0();
            nop_acl_0();
        }
        const default_action = nop_acl_0();
        size = 1024;
        counters = acl_counter_0;
    }
    apply {
        acl_0.apply();
    }
}

control Next(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @hidden @name("output") action output_0(@name("port_num") port_num_t port_num_0) {
        standard_metadata.egress_spec = port_num_0;
    }
    @hidden @name("rewrite_smac") action rewrite_smac_0(@name("smac") mac_addr_t smac_0) {
        hdr.ethernet.src_addr = smac_0;
    }
    @hidden @name("rewrite_dmac") action rewrite_dmac_0(@name("dmac") mac_addr_t dmac_0) {
        hdr.ethernet.dst_addr = dmac_0;
    }
    @hidden @name("set_mpls_label") action set_mpls_label_0(@name("label") mpls_label_t label_0) {
        fabric_metadata.mpls_label = label_0;
    }
    @hidden @name("routing") action routing_0(@name("port_num") port_num_t port_num_1, @name("smac") mac_addr_t smac_1, @name("dmac") mac_addr_t dmac_1) {
        rewrite_smac_0(smac_1);
        rewrite_dmac_0(dmac_1);
        output_0(port_num_1);
    }
    @hidden @name("mpls_routing") action mpls_routing_0(@name("port_num") port_num_t port_num_2, @name("smac") mac_addr_t smac_2, @name("dmac") mac_addr_t dmac_2, @name("label") mpls_label_t label_1) {
        set_mpls_label_0(label_1);
        routing_0(port_num_2, smac_2, dmac_2);
    }
    @name("next_vlan_counter") direct_counter(CounterType.packets_and_bytes) next_vlan_counter_0;
    @name("set_vlan") action set_vlan_0(@name("vlan_id") vlan_id_t vlan_id_1) {
        fabric_metadata.vlan_id = vlan_id_1;
        next_vlan_counter_0.count();
    }
    @name("next_vlan") table next_vlan_0 {
        key = {
            fabric_metadata.next_id: exact @name("next_id") ;
        }
        actions = {
            set_vlan_0();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = next_vlan_counter_0;
        size = 1024;
    }
    @name("xconnect_counter") direct_counter(CounterType.packets_and_bytes) xconnect_counter_0;
    @name("output_xconnect") action output_xconnect_0(@name("port_num") port_num_t port_num_3) {
        output_0(port_num_3);
        xconnect_counter_0.count();
    }
    @name("set_next_id_xconnect") action set_next_id_xconnect_0(@name("next_id") next_id_t next_id_5) {
        fabric_metadata.next_id = next_id_5;
        xconnect_counter_0.count();
    }
    @name("xconnect") table xconnect_0 {
        key = {
            standard_metadata.ingress_port: exact @name("ig_port") ;
            fabric_metadata.next_id       : exact @name("next_id") ;
        }
        actions = {
            output_xconnect_0();
            set_next_id_xconnect_0();
            @defaultonly nop();
        }
        counters = xconnect_counter_0;
        const default_action = nop();
        size = 1024;
    }
    @max_group_size(16) @name("hashed_selector") action_selector(HashAlgorithm.crc16, 32w1024, 32w16) hashed_selector_0;
    @name("hashed_counter") direct_counter(CounterType.packets_and_bytes) hashed_counter_0;
    @name("output_hashed") action output_hashed_0(@name("port_num") port_num_t port_num_4) {
        output_0(port_num_4);
        hashed_counter_0.count();
    }
    @name("routing_hashed") action routing_hashed_0(@name("port_num") port_num_t port_num_5, @name("smac") mac_addr_t smac_3, @name("dmac") mac_addr_t dmac_3) {
        routing_0(port_num_5, smac_3, dmac_3);
        hashed_counter_0.count();
    }
    @name("mpls_routing_hashed") action mpls_routing_hashed_0(@name("port_num") port_num_t port_num_6, @name("smac") mac_addr_t smac_4, @name("dmac") mac_addr_t dmac_4, @name("label") mpls_label_t label_2) {
        mpls_routing_0(port_num_6, smac_4, dmac_4, label_2);
        hashed_counter_0.count();
    }
    @name("hashed") table hashed_0 {
        key = {
            fabric_metadata.next_id : exact @name("next_id") ;
            hdr.ipv4.dst_addr       : selector @name("hdr.ipv4.dst_addr") ;
            hdr.ipv4.src_addr       : selector @name("hdr.ipv4.src_addr") ;
            fabric_metadata.ip_proto: selector @name("fabric_metadata.ip_proto") ;
            fabric_metadata.l4_sport: selector @name("fabric_metadata.l4_sport") ;
            fabric_metadata.l4_dport: selector @name("fabric_metadata.l4_dport") ;
        }
        actions = {
            output_hashed_0();
            routing_hashed_0();
            mpls_routing_hashed_0();
            @defaultonly nop();
        }
        implementation = hashed_selector_0;
        counters = hashed_counter_0;
        const default_action = nop();
        size = 1024;
    }
    @name("multicast_counter") direct_counter(CounterType.packets_and_bytes) multicast_counter_0;
    @name("set_mcast_group_id") action set_mcast_group_id_0(@name("group_id") mcast_group_id_t group_id_0) {
        standard_metadata.mcast_grp = group_id_0;
        fabric_metadata.is_multicast = true;
        multicast_counter_0.count();
    }
    @name("multicast") table multicast_0 {
        key = {
            fabric_metadata.next_id: exact @name("next_id") ;
        }
        actions = {
            set_mcast_group_id_0();
            @defaultonly nop();
        }
        counters = multicast_counter_0;
        const default_action = nop();
        size = 1024;
    }
    apply {
        xconnect_0.apply();
        hashed_0.apply();
        multicast_0.apply();
        next_vlan_0.apply();
    }
}

control EgressNextControl(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @hidden @name("pop_mpls_if_present") action pop_mpls_if_present_0() {
        hdr.mpls.setInvalid();
        fabric_metadata.eth_type = fabric_metadata.ip_eth_type;
    }
    @hidden @name("set_mpls") action set_mpls_0() {
        hdr.mpls.setValid();
        hdr.mpls.label = fabric_metadata.mpls_label;
        hdr.mpls.tc = 3w0;
        hdr.mpls.bos = 1w1;
        hdr.mpls.ttl = fabric_metadata.mpls_ttl;
        fabric_metadata.eth_type = 16w0x8847;
    }
    @hidden @name("push_vlan") action push_vlan_0() {
        hdr.vlan_tag.setValid();
        hdr.vlan_tag.cfi = fabric_metadata.vlan_cfi;
        hdr.vlan_tag.pri = fabric_metadata.vlan_pri;
        hdr.vlan_tag.eth_type = fabric_metadata.eth_type;
        hdr.vlan_tag.vlan_id = fabric_metadata.vlan_id;
        hdr.ethernet.eth_type = 16w0x8100;
    }
    @name("egress_vlan_counter") direct_counter(CounterType.packets_and_bytes) egress_vlan_counter_0;
    @name("pop_vlan") action pop_vlan_0() {
        hdr.ethernet.eth_type = fabric_metadata.eth_type;
        hdr.vlan_tag.setInvalid();
        egress_vlan_counter_0.count();
    }
    @name("egress_vlan") table egress_vlan_0 {
        key = {
            fabric_metadata.vlan_id      : exact @name("vlan_id") ;
            standard_metadata.egress_port: exact @name("eg_port") ;
        }
        actions = {
            pop_vlan_0();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = egress_vlan_counter_0;
        size = 1024;
    }
    apply {
        if (fabric_metadata.is_multicast && standard_metadata.ingress_port == standard_metadata.egress_port) {
            mark_to_drop(standard_metadata);
        }
        if (fabric_metadata.mpls_label == 20w0) {
            if (hdr.mpls.isValid()) {
                pop_mpls_if_present_0();
            }
        } else {
            set_mpls_0();
        }
        if (egress_vlan_0.apply().hit) {
            ;
        } else if (fabric_metadata.vlan_id != 12w4094) {
            push_vlan_0();
        }
        if (hdr.mpls.isValid()) {
            hdr.mpls.ttl = hdr.mpls.ttl + 8w255;
            if (hdr.mpls.ttl == 8w0) {
                mark_to_drop(standard_metadata);
            }
        } else if (hdr.ipv4.isValid()) {
            hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
            if (hdr.ipv4.ttl == 8w0) {
                mark_to_drop(standard_metadata);
            }
        }
    }
}

control PacketIoIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    apply {
        if (hdr.packet_out.isValid()) {
            standard_metadata.egress_spec = hdr.packet_out.egress_port;
            hdr.packet_out.setInvalid();
            fabric_metadata.is_controller_packet_out = true;
            exit;
        }
    }
}

control PacketIoEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    apply {
        if (fabric_metadata.is_controller_packet_out) {
            exit;
        }
        if (standard_metadata.egress_port == 9w255) {
            if (fabric_metadata.is_multicast && !fabric_metadata.clone_to_cpu) {
                mark_to_drop(standard_metadata);
            }
            hdr.packet_in.setValid();
            hdr.packet_in.ingress_port = standard_metadata.ingress_port;
            exit;
        }
    }
}

control spgw_normalizer(in bool is_gtpu_encapped, out ipv4_t gtpu_ipv4, out udp_t gtpu_udp, inout ipv4_t ipv4, inout udp_t udp, in ipv4_t inner_ipv4, in udp_t inner_udp) {
    apply {
        bool hasReturned = false;
        if (is_gtpu_encapped) {
            ;
        } else {
            hasReturned = true;
        }
        if (!hasReturned) {
            gtpu_ipv4 = ipv4;
            ipv4 = inner_ipv4;
            gtpu_udp = udp;
            if (inner_udp.isValid()) {
                udp = inner_udp;
            } else {
                udp.setInvalid();
            }
        }
    }
}

control spgw_ingress(inout ipv4_t gtpu_ipv4, inout udp_t gtpu_udp, inout gtpu_t gtpu, inout ipv4_t ipv4, inout udp_t udp, inout fabric_metadata_t fabric_meta, inout standard_metadata_t standard_metadata) {
    @name("ue_counter") direct_counter(CounterType.packets_and_bytes) ue_counter_0;
    @hidden @name("gtpu_decap") action gtpu_decap_0() {
        gtpu_ipv4.setInvalid();
        gtpu_udp.setInvalid();
        gtpu.setInvalid();
    }
    @name("set_dl_sess_info") action set_dl_sess_info_0(@name("teid") bit<32> teid_0, @name("s1u_enb_addr") bit<32> s1u_enb_addr_0, @name("s1u_sgw_addr") bit<32> s1u_sgw_addr_0) {
        fabric_meta.spgw.teid = teid_0;
        fabric_meta.spgw.s1u_enb_addr = s1u_enb_addr_0;
        fabric_meta.spgw.s1u_sgw_addr = s1u_sgw_addr_0;
        ue_counter_0.count();
    }
    @name("dl_sess_lookup") table dl_sess_lookup_0 {
        key = {
            ipv4.dst_addr: exact @name("ipv4_dst") ;
        }
        actions = {
            set_dl_sess_info_0();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = ue_counter_0;
    }
    @name("s1u_filter_table") table s1u_filter_table_0 {
        key = {
            gtpu_ipv4.dst_addr: exact @name("gtp_ipv4_dst") ;
        }
        actions = {
            nop();
        }
        const default_action = nop();
    }
    apply {
        bool hasReturned_0 = false;
        if (gtpu.isValid()) {
            if (s1u_filter_table_0.apply().hit) {
                ;
            } else {
                mark_to_drop(standard_metadata);
            }
            fabric_meta.spgw.direction = 2w1;
            gtpu_decap_0();
        } else if (dl_sess_lookup_0.apply().hit) {
            fabric_meta.spgw.direction = 2w2;
        } else {
            fabric_meta.spgw.direction = 2w0;
            {
                hasReturned_0 = true;
            }
        }
        if (!hasReturned_0) {
            fabric_meta.spgw.ipv4_len = ipv4.total_len;
        }
    }
}

control spgw_egress(in ipv4_t ipv4, inout ipv4_t gtpu_ipv4, inout udp_t gtpu_udp, inout gtpu_t gtpu, in fabric_metadata_t fabric_meta, in standard_metadata_t std_meta) {
    @hidden @name("gtpu_encap") action gtpu_encap_0() {
        gtpu_ipv4.setValid();
        gtpu_ipv4.version = 4w4;
        gtpu_ipv4.ihl = 4w5;
        gtpu_ipv4.dscp = 6w0;
        gtpu_ipv4.ecn = 2w0;
        gtpu_ipv4.total_len = ipv4.total_len + 16w36;
        gtpu_ipv4.identification = 16w0x1513;
        gtpu_ipv4.flags = 3w0;
        gtpu_ipv4.frag_offset = 13w0;
        gtpu_ipv4.ttl = 8w64;
        gtpu_ipv4.protocol = 8w17;
        gtpu_ipv4.dst_addr = fabric_meta.spgw.s1u_enb_addr;
        gtpu_ipv4.src_addr = fabric_meta.spgw.s1u_sgw_addr;
        gtpu_ipv4.hdr_checksum = 16w0;
        gtpu_udp.setValid();
        gtpu_udp.sport = 16w2152;
        gtpu_udp.dport = 16w2152;
        gtpu_udp.len = fabric_meta.spgw.ipv4_len + 16w16;
        gtpu_udp.checksum = 16w0;
        gtpu.setValid();
        gtpu.version = 3w0x1;
        gtpu.pt = 1w0x1;
        gtpu.spare = 1w0;
        gtpu.ex_flag = 1w0;
        gtpu.seq_flag = 1w0;
        gtpu.npdu_flag = 1w0;
        gtpu.msgtype = 8w0xff;
        gtpu.msglen = fabric_meta.spgw.ipv4_len;
        gtpu.teid = fabric_meta.spgw.teid;
    }
    apply {
        if (fabric_meta.spgw.direction == 2w2) {
            gtpu_encap_0();
        }
    }
}

control update_gtpu_checksum(inout ipv4_t gtpu_ipv4, inout udp_t gtpu_udp, in gtpu_t gtpu, in ipv4_t ipv4, in udp_t udp) {
    apply {
        update_checksum<tuple<bit<4>, bit<4>, bit<6>, bit<2>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(gtpu_ipv4.isValid(), { gtpu_ipv4.version, gtpu_ipv4.ihl, gtpu_ipv4.dscp, gtpu_ipv4.ecn, gtpu_ipv4.total_len, gtpu_ipv4.identification, gtpu_ipv4.flags, gtpu_ipv4.frag_offset, gtpu_ipv4.ttl, gtpu_ipv4.protocol, gtpu_ipv4.src_addr, gtpu_ipv4.dst_addr }, gtpu_ipv4.hdr_checksum, HashAlgorithm.csum16);
    }
}

control FabricComputeChecksum(inout parsed_headers_t hdr, inout fabric_metadata_t meta) {
    @name("update_gtpu_checksum") update_gtpu_checksum() update_gtpu_checksum_inst_0;
    apply {
        update_checksum<tuple<bit<4>, bit<4>, bit<6>, bit<2>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid(), { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.dscp, hdr.ipv4.ecn, hdr.ipv4.total_len, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.frag_offset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.src_addr, hdr.ipv4.dst_addr }, hdr.ipv4.hdr_checksum, HashAlgorithm.csum16);
        {
            update_checksum<tuple<bit<4>, bit<4>, bit<6>, bit<2>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.gtpu_ipv4.isValid(), { hdr.gtpu_ipv4.version, hdr.gtpu_ipv4.ihl, hdr.gtpu_ipv4.dscp, hdr.gtpu_ipv4.ecn, hdr.gtpu_ipv4.total_len, hdr.gtpu_ipv4.identification, hdr.gtpu_ipv4.flags, hdr.gtpu_ipv4.frag_offset, hdr.gtpu_ipv4.ttl, hdr.gtpu_ipv4.protocol, hdr.gtpu_ipv4.src_addr, hdr.gtpu_ipv4.dst_addr }, hdr.gtpu_ipv4.hdr_checksum, HashAlgorithm.csum16);
        }
    }
}

control FabricVerifyChecksum(inout parsed_headers_t hdr, inout fabric_metadata_t meta) {
    apply {
        verify_checksum<tuple<bit<4>, bit<4>, bit<6>, bit<2>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid(), { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.dscp, hdr.ipv4.ecn, hdr.ipv4.total_len, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.frag_offset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.src_addr, hdr.ipv4.dst_addr }, hdr.ipv4.hdr_checksum, HashAlgorithm.csum16);
    }
}

parser FabricParser(packet_in packet, out parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    bit<4> tmp;
    bit<4> tmp_0;
    state start {
        transition start_0;
    }
    state start_0 {
        transition select(standard_metadata.ingress_port) {
            9w255: parse_packet_out;
            default: parse_ethernet;
        }
    }
    state parse_packet_out {
        packet.extract<packet_out_header_t>(hdr.packet_out);
        transition parse_ethernet;
    }
    state parse_ethernet {
        packet.extract<ethernet_t>(hdr.ethernet);
        fabric_metadata.eth_type = hdr.ethernet.eth_type;
        fabric_metadata.vlan_id = 12w4094;
        transition select(hdr.ethernet.eth_type) {
            16w0x8100: parse_vlan_tag;
            16w0x8847: parse_mpls;
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_vlan_tag {
        packet.extract<vlan_tag_t>(hdr.vlan_tag);
        transition select(hdr.vlan_tag.eth_type) {
            16w0x800: parse_ipv4;
            16w0x8847: parse_mpls;
            16w0x8100: parse_inner_vlan_tag;
            default: accept;
        }
    }
    state parse_inner_vlan_tag {
        packet.extract<vlan_tag_t>(hdr.inner_vlan_tag);
        transition select(hdr.inner_vlan_tag.eth_type) {
            16w0x800: parse_ipv4;
            16w0x8847: parse_mpls;
            default: accept;
        }
    }
    state parse_mpls {
        packet.extract<mpls_t>(hdr.mpls);
        fabric_metadata.mpls_label = hdr.mpls.label;
        fabric_metadata.mpls_ttl = hdr.mpls.ttl;
        tmp_0 = packet.lookahead<bit<4>>();
        tmp = tmp_0;
        transition select(tmp) {
            4w4: parse_ipv4;
            default: parse_ethernet;
        }
    }
    state parse_ipv4 {
        packet.extract<ipv4_t>(hdr.ipv4);
        fabric_metadata.ip_proto = hdr.ipv4.protocol;
        fabric_metadata.ip_eth_type = 16w0x800;
        transition select(hdr.ipv4.protocol) {
            8w6: parse_tcp;
            8w17: parse_udp;
            8w1: parse_icmp;
            default: accept;
        }
    }
    state parse_tcp {
        packet.extract<tcp_t>(hdr.tcp);
        fabric_metadata.l4_sport = hdr.tcp.sport;
        fabric_metadata.l4_dport = hdr.tcp.dport;
        transition accept;
    }
    state parse_udp {
        packet.extract<udp_t>(hdr.udp);
        fabric_metadata.l4_sport = hdr.udp.sport;
        fabric_metadata.l4_dport = hdr.udp.dport;
        transition select(hdr.udp.dport) {
            16w2152: parse_gtpu;
            default: accept;
        }
    }
    state parse_icmp {
        packet.extract<icmp_t>(hdr.icmp);
        transition accept;
    }
    state parse_gtpu {
        transition select(hdr.ipv4.dst_addr[31:24]) {
            8w140: do_parse_gtpu;
            default: accept;
        }
    }
    state do_parse_gtpu {
        packet.extract<gtpu_t>(hdr.gtpu);
        packet.extract<ipv4_t>(hdr.inner_ipv4);
        transition select(hdr.inner_ipv4.protocol) {
            8w6: parse_tcp;
            8w17: parse_inner_udp;
            8w1: parse_icmp;
            default: accept;
        }
    }
    state parse_inner_udp {
        packet.extract<udp_t>(hdr.inner_udp);
        fabric_metadata.l4_sport = hdr.inner_udp.sport;
        fabric_metadata.l4_dport = hdr.inner_udp.dport;
        transition accept;
    }
}

control FabricDeparser(packet_out packet, in parsed_headers_t hdr) {
    apply {
        packet.emit<packet_in_header_t>(hdr.packet_in);
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<vlan_tag_t>(hdr.vlan_tag);
        packet.emit<vlan_tag_t>(hdr.inner_vlan_tag);
        packet.emit<mpls_t>(hdr.mpls);
        packet.emit<ipv4_t>(hdr.gtpu_ipv4);
        packet.emit<udp_t>(hdr.gtpu_udp);
        packet.emit<gtpu_t>(hdr.gtpu);
        packet.emit<ipv4_t>(hdr.ipv4);
        packet.emit<tcp_t>(hdr.tcp);
        packet.emit<udp_t>(hdr.udp);
        packet.emit<icmp_t>(hdr.icmp);
    }
}

control PortCountersControl(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @name("egress_port_counter") counter(32w511, CounterType.packets_and_bytes) egress_port_counter_0;
    @name("ingress_port_counter") counter(32w511, CounterType.packets_and_bytes) ingress_port_counter_0;
    apply {
        if (standard_metadata.egress_spec < 9w511) {
            egress_port_counter_0.count((bit<32>)standard_metadata.egress_spec);
        }
        if (standard_metadata.ingress_port < 9w511) {
            ingress_port_counter_0.count((bit<32>)standard_metadata.ingress_port);
        }
    }
}

control FabricIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @name("spgw_normalizer") spgw_normalizer() spgw_normalizer_inst_0;
    @name("spgw_ingress") spgw_ingress() spgw_ingress_inst_0;
    @name("spgw_ingress.ue_counter") direct_counter(CounterType.packets_and_bytes) spgw_ingress_ue_counter;
    @hidden @name("spgw_ingress.gtpu_decap") action spgw_ingress_gtpu_decap() {
        hdr.gtpu_ipv4.setInvalid();
        hdr.gtpu_udp.setInvalid();
        hdr.gtpu.setInvalid();
    }
    @name("spgw_ingress.set_dl_sess_info") action spgw_ingress_set_dl_sess_info(@name("teid") bit<32> teid_0, @name("s1u_enb_addr") bit<32> s1u_enb_addr_0, @name("s1u_sgw_addr") bit<32> s1u_sgw_addr_0) {
        fabric_metadata.spgw.teid = teid_0;
        fabric_metadata.spgw.s1u_enb_addr = s1u_enb_addr_0;
        fabric_metadata.spgw.s1u_sgw_addr = s1u_sgw_addr_0;
        spgw_ingress_ue_counter.count();
    }
    @name("spgw_ingress.dl_sess_lookup") table spgw_ingress_dl_sess_lookup {
        key = {
            hdr.ipv4.dst_addr: exact @name("ipv4_dst") ;
        }
        actions = {
            spgw_ingress_set_dl_sess_info();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = spgw_ingress_ue_counter;
    }
    @name("spgw_ingress.s1u_filter_table") table spgw_ingress_s1u_filter_table {
        key = {
            hdr.gtpu_ipv4.dst_addr: exact @name("gtp_ipv4_dst") ;
        }
        actions = {
            nop();
        }
        const default_action = nop();
    }
    @name("pkt_io_ingress") PacketIoIngress() pkt_io_ingress_0;
    @name("filtering") Filtering() filtering_0;
    @name("filtering.ingress_port_vlan_counter") direct_counter(CounterType.packets_and_bytes) filtering_ingress_port_vlan_counter;
    @name("filtering.deny") action filtering_deny() {
        fabric_metadata.skip_forwarding = true;
        fabric_metadata.skip_next = true;
        filtering_ingress_port_vlan_counter.count();
    }
    @name("filtering.permit") action filtering_permit() {
        filtering_ingress_port_vlan_counter.count();
    }
    @name("filtering.permit_with_internal_vlan") action filtering_permit_with_internal_vlan(@name("vlan_id") vlan_id_t vlan_id_0) {
        fabric_metadata.vlan_id = vlan_id_0;
        filtering_ingress_port_vlan_counter.count();
    }
    @name("filtering.ingress_port_vlan") table filtering_ingress_port_vlan {
        key = {
            standard_metadata.ingress_port: exact @name("ig_port") ;
            hdr.vlan_tag.isValid()        : exact @name("vlan_is_valid") ;
            hdr.vlan_tag.vlan_id          : ternary @name("vlan_id") ;
        }
        actions = {
            filtering_deny();
            filtering_permit();
            filtering_permit_with_internal_vlan();
        }
        const default_action = filtering_deny();
        counters = filtering_ingress_port_vlan_counter;
        size = 1024;
    }
    @name("filtering.fwd_classifier_counter") direct_counter(CounterType.packets_and_bytes) filtering_fwd_classifier_counter;
    @name("filtering.set_forwarding_type") action filtering_set_forwarding_type(@name("fwd_type") fwd_type_t fwd_type_0) {
        fabric_metadata.fwd_type = fwd_type_0;
        filtering_fwd_classifier_counter.count();
    }
    @name("filtering.fwd_classifier") table filtering_fwd_classifier {
        key = {
            standard_metadata.ingress_port: exact @name("ig_port") ;
            hdr.ethernet.dst_addr         : ternary @name("eth_dst") ;
            fabric_metadata.eth_type      : exact @name("eth_type") ;
        }
        actions = {
            filtering_set_forwarding_type();
        }
        const default_action = filtering_set_forwarding_type(3w0);
        counters = filtering_fwd_classifier_counter;
        size = 1024;
    }
    @name("forwarding") Forwarding() forwarding_0;
    @hidden @name("forwarding.set_next_id") action forwarding_set_next_id(@name("next_id") next_id_t next_id_0) {
        fabric_metadata.next_id = next_id_0;
    }
    @name("forwarding.bridging_counter") direct_counter(CounterType.packets_and_bytes) forwarding_bridging_counter;
    @name("forwarding.set_next_id_bridging") action forwarding_set_next_id_bridging(@name("next_id") next_id_t next_id_1) {
        forwarding_set_next_id(next_id_1);
        forwarding_bridging_counter.count();
    }
    @name("forwarding.bridging") table forwarding_bridging {
        key = {
            fabric_metadata.vlan_id: exact @name("vlan_id") ;
            hdr.ethernet.dst_addr  : ternary @name("eth_dst") ;
        }
        actions = {
            forwarding_set_next_id_bridging();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = forwarding_bridging_counter;
        size = 1024;
    }
    @name("forwarding.mpls_counter") direct_counter(CounterType.packets_and_bytes) forwarding_mpls_counter;
    @name("forwarding.pop_mpls_and_next") action forwarding_pop_mpls_and_next(@name("next_id") next_id_t next_id_2) {
        fabric_metadata.mpls_label = 20w0;
        forwarding_set_next_id(next_id_2);
        forwarding_mpls_counter.count();
    }
    @name("forwarding.mpls") table forwarding_mpls {
        key = {
            fabric_metadata.mpls_label: exact @name("mpls_label") ;
        }
        actions = {
            forwarding_pop_mpls_and_next();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = forwarding_mpls_counter;
        size = 1024;
    }
    @name("forwarding.routing_v4_counter") direct_counter(CounterType.packets_and_bytes) forwarding_routing_v4_counter;
    @name("forwarding.set_next_id_routing_v4") action forwarding_set_next_id_routing_v4(@name("next_id") next_id_t next_id_3) {
        forwarding_set_next_id(next_id_3);
        forwarding_routing_v4_counter.count();
    }
    @name("forwarding.nop_routing_v4") action forwarding_nop_routing_v4() {
        forwarding_routing_v4_counter.count();
    }
    @name("forwarding.routing_v4") table forwarding_routing_v4 {
        key = {
            hdr.ipv4.dst_addr: lpm @name("ipv4_dst") ;
        }
        actions = {
            forwarding_set_next_id_routing_v4();
            forwarding_nop_routing_v4();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = forwarding_routing_v4_counter;
        size = 1024;
    }
    @name("acl") Acl() acl_1;
    @name("acl.acl_counter") direct_counter(CounterType.packets_and_bytes) acl_acl_counter;
    @name("acl.set_next_id_acl") action acl_set_next_id_acl(@name("next_id") next_id_t next_id_4) {
        fabric_metadata.next_id = next_id_4;
        acl_acl_counter.count();
    }
    @name("acl.punt_to_cpu") action acl_punt_to_cpu() {
        standard_metadata.egress_spec = 9w255;
        fabric_metadata.skip_next = true;
        acl_acl_counter.count();
    }
    @name("acl.clone_to_cpu") action acl_clone_to_cpu() {
        fabric_metadata.clone_to_cpu = true;
        acl_acl_counter.count();
    }
    @name("acl.drop") action acl_drop() {
        mark_to_drop(standard_metadata);
        fabric_metadata.skip_next = true;
        acl_acl_counter.count();
    }
    @name("acl.nop_acl") action acl_nop_acl() {
        acl_acl_counter.count();
    }
    @name("acl.acl") table acl_acl {
        key = {
            standard_metadata.ingress_port: ternary @name("ig_port") ;
            fabric_metadata.ip_proto      : ternary @name("ip_proto") ;
            fabric_metadata.l4_sport      : ternary @name("l4_sport") ;
            fabric_metadata.l4_dport      : ternary @name("l4_dport") ;
            hdr.ethernet.dst_addr         : ternary @name("eth_src") ;
            hdr.ethernet.src_addr         : ternary @name("eth_dst") ;
            hdr.vlan_tag.vlan_id          : ternary @name("vlan_id") ;
            fabric_metadata.eth_type      : ternary @name("eth_type") ;
            hdr.ipv4.src_addr             : ternary @name("ipv4_src") ;
            hdr.ipv4.dst_addr             : ternary @name("ipv4_dst") ;
            hdr.icmp.icmp_type            : ternary @name("icmp_type") ;
            hdr.icmp.icmp_code            : ternary @name("icmp_code") ;
        }
        actions = {
            acl_set_next_id_acl();
            acl_punt_to_cpu();
            acl_clone_to_cpu();
            acl_drop();
            acl_nop_acl();
        }
        const default_action = acl_nop_acl();
        size = 1024;
        counters = acl_acl_counter;
    }
    @name("next") Next() next_0;
    @hidden @name("next.output") action next_output(@name("port_num") port_num_t port_num_0) {
        standard_metadata.egress_spec = port_num_0;
    }
    @hidden @name("next.rewrite_smac") action next_rewrite_smac(@name("smac") mac_addr_t smac_0) {
        hdr.ethernet.src_addr = smac_0;
    }
    @hidden @name("next.rewrite_dmac") action next_rewrite_dmac(@name("dmac") mac_addr_t dmac_0) {
        hdr.ethernet.dst_addr = dmac_0;
    }
    @hidden @name("next.set_mpls_label") action next_set_mpls_label(@name("label") mpls_label_t label_0) {
        fabric_metadata.mpls_label = label_0;
    }
    @hidden @name("next.routing") action next_routing(@name("port_num") port_num_t port_num_1, @name("smac") mac_addr_t smac_1, @name("dmac") mac_addr_t dmac_1) {
        next_rewrite_smac(smac_1);
        next_rewrite_dmac(dmac_1);
        next_output(port_num_1);
    }
    @hidden @name("next.mpls_routing") action next_mpls_routing(@name("port_num") port_num_t port_num_2, @name("smac") mac_addr_t smac_2, @name("dmac") mac_addr_t dmac_2, @name("label") mpls_label_t label_1) {
        next_set_mpls_label(label_1);
        next_routing(port_num_2, smac_2, dmac_2);
    }
    @name("next.next_vlan_counter") direct_counter(CounterType.packets_and_bytes) next_next_vlan_counter;
    @name("next.set_vlan") action next_set_vlan(@name("vlan_id") vlan_id_t vlan_id_1) {
        fabric_metadata.vlan_id = vlan_id_1;
        next_next_vlan_counter.count();
    }
    @name("next.next_vlan") table next_next_vlan {
        key = {
            fabric_metadata.next_id: exact @name("next_id") ;
        }
        actions = {
            next_set_vlan();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = next_next_vlan_counter;
        size = 1024;
    }
    @name("next.xconnect_counter") direct_counter(CounterType.packets_and_bytes) next_xconnect_counter;
    @name("next.output_xconnect") action next_output_xconnect(@name("port_num") port_num_t port_num_3) {
        next_output(port_num_3);
        next_xconnect_counter.count();
    }
    @name("next.set_next_id_xconnect") action next_set_next_id_xconnect(@name("next_id") next_id_t next_id_5) {
        fabric_metadata.next_id = next_id_5;
        next_xconnect_counter.count();
    }
    @name("next.xconnect") table next_xconnect {
        key = {
            standard_metadata.ingress_port: exact @name("ig_port") ;
            fabric_metadata.next_id       : exact @name("next_id") ;
        }
        actions = {
            next_output_xconnect();
            next_set_next_id_xconnect();
            @defaultonly nop();
        }
        counters = next_xconnect_counter;
        const default_action = nop();
        size = 1024;
    }
    @max_group_size(16) @name("next.hashed_selector") action_selector(HashAlgorithm.crc16, 32w1024, 32w16) next_hashed_selector;
    @name("next.hashed_counter") direct_counter(CounterType.packets_and_bytes) next_hashed_counter;
    @name("next.output_hashed") action next_output_hashed(@name("port_num") port_num_t port_num_4) {
        next_output(port_num_4);
        next_hashed_counter.count();
    }
    @name("next.routing_hashed") action next_routing_hashed(@name("port_num") port_num_t port_num_5, @name("smac") mac_addr_t smac_3, @name("dmac") mac_addr_t dmac_3) {
        next_routing(port_num_5, smac_3, dmac_3);
        next_hashed_counter.count();
    }
    @name("next.mpls_routing_hashed") action next_mpls_routing_hashed(@name("port_num") port_num_t port_num_6, @name("smac") mac_addr_t smac_4, @name("dmac") mac_addr_t dmac_4, @name("label") mpls_label_t label_2) {
        next_mpls_routing(port_num_6, smac_4, dmac_4, label_2);
        next_hashed_counter.count();
    }
    @name("next.hashed") table next_hashed {
        key = {
            fabric_metadata.next_id : exact @name("next_id") ;
            hdr.ipv4.dst_addr       : selector @name("hdr.ipv4.dst_addr") ;
            hdr.ipv4.src_addr       : selector @name("hdr.ipv4.src_addr") ;
            fabric_metadata.ip_proto: selector @name("fabric_metadata.ip_proto") ;
            fabric_metadata.l4_sport: selector @name("fabric_metadata.l4_sport") ;
            fabric_metadata.l4_dport: selector @name("fabric_metadata.l4_dport") ;
        }
        actions = {
            next_output_hashed();
            next_routing_hashed();
            next_mpls_routing_hashed();
            @defaultonly nop();
        }
        implementation = next_hashed_selector;
        counters = next_hashed_counter;
        const default_action = nop();
        size = 1024;
    }
    @name("next.multicast_counter") direct_counter(CounterType.packets_and_bytes) next_multicast_counter;
    @name("next.set_mcast_group_id") action next_set_mcast_group_id(@name("group_id") mcast_group_id_t group_id_0) {
        standard_metadata.mcast_grp = group_id_0;
        fabric_metadata.is_multicast = true;
        next_multicast_counter.count();
    }
    @name("next.multicast") table next_multicast {
        key = {
            fabric_metadata.next_id: exact @name("next_id") ;
        }
        actions = {
            next_set_mcast_group_id();
            @defaultonly nop();
        }
        counters = next_multicast_counter;
        const default_action = nop();
        size = 1024;
    }
    @name("port_counters_control") PortCountersControl() port_counters_control_0;
    @name("port_counters_control.egress_port_counter") counter(32w511, CounterType.packets_and_bytes) port_counters_control_egress_port_counter;
    @name("port_counters_control.ingress_port_counter") counter(32w511, CounterType.packets_and_bytes) port_counters_control_ingress_port_counter;
    apply {
        {
            hdr.gtpu_ipv4.setInvalid();
            hdr.gtpu_udp.setInvalid();
            @name("spgw_normalizer.hasReturned") bool spgw_normalizer_hasReturned = false;
            if (hdr.gtpu.isValid()) {
                ;
            } else {
                spgw_normalizer_hasReturned = true;
            }
            if (!spgw_normalizer_hasReturned) {
                hdr.gtpu_ipv4 = hdr.ipv4;
                hdr.ipv4 = hdr.inner_ipv4;
                hdr.gtpu_udp = hdr.udp;
                if (hdr.inner_udp.isValid()) {
                    hdr.udp = hdr.inner_udp;
                } else {
                    hdr.udp.setInvalid();
                }
            }
        }
        {
            if (hdr.packet_out.isValid()) {
                standard_metadata.egress_spec = hdr.packet_out.egress_port;
                hdr.packet_out.setInvalid();
                fabric_metadata.is_controller_packet_out = true;
                exit;
            }
        }
        {
            if (hdr.vlan_tag.isValid()) {
                fabric_metadata.eth_type = hdr.vlan_tag.eth_type;
                fabric_metadata.vlan_id = hdr.vlan_tag.vlan_id;
                fabric_metadata.vlan_pri = hdr.vlan_tag.pri;
                fabric_metadata.vlan_cfi = hdr.vlan_tag.cfi;
            }
            if (hdr.mpls.isValid()) {
                ;
            } else {
                fabric_metadata.mpls_ttl = 8w65;
            }
            filtering_ingress_port_vlan.apply();
            filtering_fwd_classifier.apply();
        }
        {
            @name("spgw_ingress.hasReturned_0") bool spgw_ingress_hasReturned = false;
            if (hdr.gtpu.isValid()) {
                if (spgw_ingress_s1u_filter_table.apply().hit) {
                    ;
                } else {
                    mark_to_drop(standard_metadata);
                }
                fabric_metadata.spgw.direction = 2w1;
                spgw_ingress_gtpu_decap();
            } else if (spgw_ingress_dl_sess_lookup.apply().hit) {
                fabric_metadata.spgw.direction = 2w2;
            } else {
                fabric_metadata.spgw.direction = 2w0;
                {
                    spgw_ingress_hasReturned = true;
                }
            }
            if (!spgw_ingress_hasReturned) {
                fabric_metadata.spgw.ipv4_len = hdr.ipv4.total_len;
            }
        }
        if (fabric_metadata.skip_forwarding) {
            ;
        } else {
            if (fabric_metadata.fwd_type == 3w0) {
                forwarding_bridging.apply();
            } else if (fabric_metadata.fwd_type == 3w1) {
                forwarding_mpls.apply();
            } else if (fabric_metadata.fwd_type == 3w2) {
                forwarding_routing_v4.apply();
            }
        }
        {
            acl_acl.apply();
        }
        if (fabric_metadata.skip_next) {
            ;
        } else {
            {
                next_xconnect.apply();
                next_hashed.apply();
                next_multicast.apply();
                next_next_vlan.apply();
            }
            {
                if (standard_metadata.egress_spec < 9w511) {
                    port_counters_control_egress_port_counter.count((bit<32>)standard_metadata.egress_spec);
                }
                if (standard_metadata.ingress_port < 9w511) {
                    port_counters_control_ingress_port_counter.count((bit<32>)standard_metadata.ingress_port);
                }
            }
        }
    }
}

control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
    @name("spgw_egress") spgw_egress() spgw_egress_inst_0;
    @hidden @name("spgw_egress.gtpu_encap") action spgw_egress_gtpu_encap() {
        hdr.gtpu_ipv4.setValid();
        hdr.gtpu_ipv4.version = 4w4;
        hdr.gtpu_ipv4.ihl = 4w5;
        hdr.gtpu_ipv4.dscp = 6w0;
        hdr.gtpu_ipv4.ecn = 2w0;
        hdr.gtpu_ipv4.total_len = hdr.ipv4.total_len + 16w36;
        hdr.gtpu_ipv4.identification = 16w0x1513;
        hdr.gtpu_ipv4.flags = 3w0;
        hdr.gtpu_ipv4.frag_offset = 13w0;
        hdr.gtpu_ipv4.ttl = 8w64;
        hdr.gtpu_ipv4.protocol = 8w17;
        hdr.gtpu_ipv4.dst_addr = fabric_metadata.spgw.s1u_enb_addr;
        hdr.gtpu_ipv4.src_addr = fabric_metadata.spgw.s1u_sgw_addr;
        hdr.gtpu_ipv4.hdr_checksum = 16w0;
        hdr.gtpu_udp.setValid();
        hdr.gtpu_udp.sport = 16w2152;
        hdr.gtpu_udp.dport = 16w2152;
        hdr.gtpu_udp.len = fabric_metadata.spgw.ipv4_len + 16w16;
        hdr.gtpu_udp.checksum = 16w0;
        hdr.gtpu.setValid();
        hdr.gtpu.version = 3w0x1;
        hdr.gtpu.pt = 1w0x1;
        hdr.gtpu.spare = 1w0;
        hdr.gtpu.ex_flag = 1w0;
        hdr.gtpu.seq_flag = 1w0;
        hdr.gtpu.npdu_flag = 1w0;
        hdr.gtpu.msgtype = 8w0xff;
        hdr.gtpu.msglen = fabric_metadata.spgw.ipv4_len;
        hdr.gtpu.teid = fabric_metadata.spgw.teid;
    }
    @name("pkt_io_egress") PacketIoEgress() pkt_io_egress_0;
    @name("egress_next") EgressNextControl() egress_next_0;
    @hidden @name("egress_next.pop_mpls_if_present") action egress_next_pop_mpls_if_present() {
        hdr.mpls.setInvalid();
        fabric_metadata.eth_type = fabric_metadata.ip_eth_type;
    }
    @hidden @name("egress_next.set_mpls") action egress_next_set_mpls() {
        hdr.mpls.setValid();
        hdr.mpls.label = fabric_metadata.mpls_label;
        hdr.mpls.tc = 3w0;
        hdr.mpls.bos = 1w1;
        hdr.mpls.ttl = fabric_metadata.mpls_ttl;
        fabric_metadata.eth_type = 16w0x8847;
    }
    @hidden @name("egress_next.push_vlan") action egress_next_push_vlan() {
        hdr.vlan_tag.setValid();
        hdr.vlan_tag.cfi = fabric_metadata.vlan_cfi;
        hdr.vlan_tag.pri = fabric_metadata.vlan_pri;
        hdr.vlan_tag.eth_type = fabric_metadata.eth_type;
        hdr.vlan_tag.vlan_id = fabric_metadata.vlan_id;
        hdr.ethernet.eth_type = 16w0x8100;
    }
    @name("egress_next.egress_vlan_counter") direct_counter(CounterType.packets_and_bytes) egress_next_egress_vlan_counter;
    @name("egress_next.pop_vlan") action egress_next_pop_vlan() {
        hdr.ethernet.eth_type = fabric_metadata.eth_type;
        hdr.vlan_tag.setInvalid();
        egress_next_egress_vlan_counter.count();
    }
    @name("egress_next.egress_vlan") table egress_next_egress_vlan {
        key = {
            fabric_metadata.vlan_id      : exact @name("vlan_id") ;
            standard_metadata.egress_port: exact @name("eg_port") ;
        }
        actions = {
            egress_next_pop_vlan();
            @defaultonly nop();
        }
        const default_action = nop();
        counters = egress_next_egress_vlan_counter;
        size = 1024;
    }
    apply {
        {
            if (fabric_metadata.is_controller_packet_out) {
                exit;
            }
            if (standard_metadata.egress_port == 9w255) {
                if (fabric_metadata.is_multicast && !fabric_metadata.clone_to_cpu) {
                    mark_to_drop(standard_metadata);
                }
                hdr.packet_in.setValid();
                hdr.packet_in.ingress_port = standard_metadata.ingress_port;
                exit;
            }
        }
        {
            if (fabric_metadata.is_multicast && standard_metadata.ingress_port == standard_metadata.egress_port) {
                mark_to_drop(standard_metadata);
            }
            if (fabric_metadata.mpls_label == 20w0) {
                if (hdr.mpls.isValid()) {
                    egress_next_pop_mpls_if_present();
                }
            } else {
                egress_next_set_mpls();
            }
            if (egress_next_egress_vlan.apply().hit) {
                ;
            } else if (fabric_metadata.vlan_id != 12w4094) {
                egress_next_push_vlan();
            }
            if (hdr.mpls.isValid()) {
                hdr.mpls.ttl = hdr.mpls.ttl + 8w255;
                if (hdr.mpls.ttl == 8w0) {
                    mark_to_drop(standard_metadata);
                }
            } else if (hdr.ipv4.isValid()) {
                hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
                if (hdr.ipv4.ttl == 8w0) {
                    mark_to_drop(standard_metadata);
                }
            }
        }
        {
            if (fabric_metadata.spgw.direction == 2w2) {
                spgw_egress_gtpu_encap();
            }
        }
    }
}

V1Switch<parsed_headers_t, fabric_metadata_t>(FabricParser(), FabricVerifyChecksum(), FabricIngress(), FabricEgress(), FabricComputeChecksum(), FabricDeparser()) main;

