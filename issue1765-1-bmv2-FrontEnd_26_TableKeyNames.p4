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
typedef bit<48> mac_addr_t;
typedef bit<32> ipv4_addr_t;
typedef bit<128> ipv6_addr_t;
typedef bit<9> port_t;
typedef bit<16> mcast_t;
typedef bit<16> task_t;
const bit<16> TYPE_IPV4 = 16w0x800;
const bit<16> TYPE_IPV6 = 16w0x86dd;
const bit<16> TYPE_CPU = 16w0x4242;
const bit<16> TYPE_DEBUG = 16w0x2323;
const bit<8> PROTO_ICMP = 8w1;
const bit<8> PROTO_TCP = 8w6;
const bit<8> PROTO_UDP = 8w17;
const bit<8> PROTO_ICMP6 = 8w58;
const bit<8> TCP_SEQ_LEN = 8w4;
const bit<8> ICMP6_ECHO_REQUEST = 8w128;
const bit<8> ICMP6_ECHO_REPLY = 8w129;
const bit<8> ICMP6_NS = 8w135;
const bit<8> ICMP6_NA = 8w136;
const task_t TASK_ICMP6_NS = (bit<16>)16w1;
const task_t TASK_ICMP6_GENERAL = (bit<16>)16w2;
const task_t TASK_DEBUG = (bit<16>)16w3;
const task_t TASK_ICMP6_REPLY = (bit<16>)16w4;
header ethernet_t {
    mac_addr_t dst_addr;
    mac_addr_t src_addr;
    bit<16>    ethertype;
}

header ipv4_t {
    bit<4>      version;
    bit<4>      ihl;
    bit<6>      diff_serv;
    bit<2>      ecn;
    bit<16>     totalLen;
    bit<16>     identification;
    bit<3>      flags;
    bit<13>     fragOffset;
    bit<8>      ttl;
    bit<8>      protocol;
    bit<16>     hdrChecksum;
    ipv4_addr_t src_addr;
    ipv4_addr_t dst_addr;
}

header ipv6_t {
    bit<4>      version;
    bit<8>      traffic_class;
    bit<20>     flow_label;
    bit<16>     payload_length;
    bit<8>      next_header;
    bit<8>      hop_limit;
    ipv6_addr_t src_addr;
    ipv6_addr_t dst_addr;
}

header tcp_t {
    bit<16> src_port;
    bit<16> dst_port;
    int<32> seqNo;
    int<32> ackNo;
    bit<4>  data_offset;
    bit<4>  res;
    bit<1>  cwr;
    bit<1>  ece;
    bit<1>  urg;
    bit<1>  ack;
    bit<1>  psh;
    bit<1>  rst;
    bit<1>  syn;
    bit<1>  fin;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgentPtr;
}

header udp_t {
    bit<16> src_port;
    bit<16> dst_port;
    bit<16> payload_length;
    bit<16> checksum;
}

header icmp6_t {
    bit<8>  type;
    bit<8>  code;
    bit<16> checksum;
}

header icmp_t {
    bit<8>  type;
    bit<8>  code;
    bit<16> checksum;
    bit<32> rest;
}

header cpu_t {
    task_t  task;
    bit<16> ingress_port;
    bit<16> ethertype;
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
    ipv6_t     ipv6;
    tcp_t      tcp;
    udp_t      udp;
    icmp6_t    icmp6;
    icmp_t     icmp;
    cpu_t      cpu;
}

struct metadata {
    @field_list(0) 
    port_t  ingress_port;
    @field_list(0) 
    task_t  task;
    @field_list(0) 
    bit<16> tcp_length;
    @field_list(0) 
    bit<32> cast_length;
    @field_list(0) 
    bit<1>  do_cksum;
}

parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.ethertype) {
            16w0x800: ipv4;
            16w0x86dd: ipv6;
            default: accept;
        }
    }
    state ipv4 {
        packet.extract<ipv4_t>(hdr.ipv4);
        meta.tcp_length = hdr.ipv4.totalLen - 16w20;
        transition select(hdr.ipv4.protocol) {
            8w6: tcp;
            8w17: udp;
            8w1: icmp;
            default: accept;
        }
    }
    state ipv6 {
        packet.extract<ipv6_t>(hdr.ipv6);
        meta.tcp_length = hdr.ipv6.payload_length;
        transition select(hdr.ipv6.next_header) {
            8w6: tcp;
            8w17: udp;
            8w58: icmp6;
            default: accept;
        }
    }
    state tcp {
        packet.extract<tcp_t>(hdr.tcp);
        transition accept;
    }
    state udp {
        packet.extract<udp_t>(hdr.udp);
        transition accept;
    }
    state icmp6 {
        packet.extract<icmp6_t>(hdr.icmp6);
        transition accept;
    }
    state icmp {
        packet.extract<icmp_t>(hdr.icmp);
        transition accept;
    }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<cpu_t>(hdr.cpu);
        packet.emit<ipv4_t>(hdr.ipv4);
        packet.emit<ipv6_t>(hdr.ipv6);
        packet.emit<tcp_t>(hdr.tcp);
        packet.emit<udp_t>(hdr.udp);
        packet.emit<icmp_t>(hdr.icmp);
        packet.emit<icmp6_t>(hdr.icmp6);
    }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum_with_payload<tuple<bit<128>, bit<128>, bit<32>, bit<24>, bit<8>>, bit<16>>(meta.do_cksum == 1w1, { hdr.ipv6.src_addr, hdr.ipv6.dst_addr, (bit<32>)hdr.ipv6.payload_length, 24w0, 8w58 }, hdr.icmp6.checksum, HashAlgorithm.csum16);
    }
}

control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    action drop() {
        mark_to_drop(standard_metadata);
    }
    action set_egress_port(port_t out_port) {
        standard_metadata.egress_spec = out_port;
    }
    action controller_debug() {
        meta.task = TASK_DEBUG;
        meta.ingress_port = standard_metadata.ingress_port;
        clone_preserving_field_list(CloneType.I2E, (bit<32>)100, 8w0);
    }
    action controller_reply(task_t task) {
        meta.task = task;
        meta.ingress_port = standard_metadata.ingress_port;
        clone_preserving_field_list(CloneType.I2E, (bit<32>)100, 8w0);
    }
    action multicast_pkg(mcast_t mcast_grp) {
        standard_metadata.mcast_grp = mcast_grp;
    }
    action icmp6_neighbor_solicitation(ipv6_addr_t addr) {
        standard_metadata.egress_spec = standard_metadata.ingress_port;
        hdr.ipv6.dst_addr = hdr.ipv6.src_addr;
        hdr.ipv6.src_addr = addr;
        hdr.icmp6.type = 8w136;
    }
    action icmp6_echo_reply() {
        mac_addr_t mac_tmp = hdr.ethernet.dst_addr;
        hdr.ethernet.dst_addr = hdr.ethernet.src_addr;
        hdr.ethernet.src_addr = mac_tmp;
        ipv6_addr_t addr_tmp = hdr.ipv6.dst_addr;
        hdr.ipv6.dst_addr = hdr.ipv6.src_addr;
        hdr.ipv6.src_addr = addr_tmp;
        hdr.icmp6.type = 8w129;
        meta.do_cksum = (bit<1>)1w1;
    }
    table ndp_answer {
        key = {
            hdr.ipv6.dst_addr: exact @name("hdr.ipv6.dst_addr") ;
            hdr.icmp6.type   : exact @name("hdr.icmp6.type") ;
        }
        actions = {
            controller_debug();
            icmp6_neighbor_solicitation();
            NoAction();
        }
        size = 64;
        default_action = NoAction();
    }
    table port2mcast {
        key = {
            standard_metadata.ingress_port: exact @name("standard_metadata.ingress_port") ;
        }
        actions = {
            multicast_pkg();
            controller_debug();
            NoAction();
        }
        size = 64;
        default_action = NoAction();
    }
    table addr2mcast {
        key = {
            hdr.ipv6.dst_addr: exact @name("hdr.ipv6.dst_addr") ;
        }
        actions = {
            multicast_pkg();
            controller_debug();
            NoAction();
        }
        size = 64;
        default_action = NoAction();
    }
    table ndp {
        key = {
            hdr.ipv6.dst_addr             : lpm @name("hdr.ipv6.dst_addr") ;
            standard_metadata.ingress_port: exact @name("standard_metadata.ingress_port") ;
        }
        actions = {
            multicast_pkg();
            controller_debug();
            NoAction();
        }
        size = 64;
        default_action = controller_debug();
    }
    action icmp6_answer() {
        if (hdr.icmp6.isValid()) {
            if (hdr.icmp6.code == 8w128) {
                ipv6_addr_t tmp = hdr.ipv6.src_addr;
                hdr.ipv6.src_addr = hdr.ipv6.dst_addr;
                hdr.ipv6.dst_addr = tmp;
                hdr.icmp6.code = 8w129;
            }
        }
    }
    table v6_addresses {
        key = {
            hdr.ipv6.dst_addr: exact @name("hdr.ipv6.dst_addr") ;
        }
        actions = {
            controller_debug();
            controller_reply();
            icmp6_echo_reply();
            NoAction();
        }
        size = 64;
        default_action = NoAction();
    }
    table v6_networks {
        key = {
            hdr.ipv6.dst_addr: lpm @name("hdr.ipv6.dst_addr") ;
        }
        actions = {
            set_egress_port();
            controller_debug();
            controller_reply();
            NoAction();
        }
        size = 64;
        default_action = NoAction();
    }
    table v4_networks {
        key = {
            hdr.ipv4.dst_addr: lpm @name("hdr.ipv4.dst_addr") ;
        }
        actions = {
            set_egress_port();
            NoAction();
        }
        size = 64;
        default_action = NoAction();
    }
    apply {
        if (hdr.ipv6.isValid()) {
            v6_addresses.apply();
            v6_networks.apply();
        }
        if (hdr.ipv4.isValid()) {
            v4_networks.apply();
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
        if (standard_metadata.instance_type == 32w1) {
            hdr.cpu.setValid();
            hdr.cpu.task = meta.task;
            hdr.cpu.ethertype = hdr.ethernet.ethertype;
            hdr.cpu.ingress_port = (bit<16>)meta.ingress_port;
            hdr.ethernet.ethertype = 16w0x4242;
        }
    }
}

V1Switch<headers, metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;

