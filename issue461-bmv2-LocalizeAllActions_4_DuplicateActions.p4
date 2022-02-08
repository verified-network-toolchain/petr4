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
struct fwd_metadata_t {
    bit<32> l2ptr;
    bit<24> out_bd;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}

struct metadata {
    fwd_metadata_t fwd_metadata;
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
}

@name(".my_drop") action my_drop(@name("smeta") inout standard_metadata_t smeta_0) {
    mark_to_drop(smeta_0);
}
parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state parse_ipv4 {
        packet.extract<ipv4_t>(hdr.ipv4);
        transition accept;
    }
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".my_drop") action my_drop_0(@name("smeta") inout standard_metadata_t smeta_0) {
        mark_to_drop(smeta_0);
    }
    @name(".my_drop") action my_drop_2(@name("smeta") inout standard_metadata_t smeta_0) {
        mark_to_drop(smeta_0);
    }
    @name("ipv4_da_lpm_stats") direct_counter(CounterType.packets) ipv4_da_lpm_stats_0;
    @name("set_l2ptr") action set_l2ptr_0(@name("l2ptr") bit<32> l2ptr_0) {
        ipv4_da_lpm_stats_0.count();
        meta.fwd_metadata.l2ptr = l2ptr_0;
    }
    @name("set_l2ptr") action set_l2ptr(@name("l2ptr") bit<32> l2ptr_0) {
        ipv4_da_lpm_stats_0.count();
        meta.fwd_metadata.l2ptr = l2ptr_0;
    }
    @name("drop_with_count") action drop_with_count_0() {
        ipv4_da_lpm_stats_0.count();
        mark_to_drop(standard_metadata);
    }
    @name("drop_with_count") action drop_with_count() {
        ipv4_da_lpm_stats_0.count();
        mark_to_drop(standard_metadata);
    }
    @name("set_bd_dmac_intf") action set_bd_dmac_intf_0(@name("bd") bit<24> bd_0, @name("dmac") bit<48> dmac_0, @name("intf") bit<9> intf_0) {
        meta.fwd_metadata.out_bd = bd_0;
        hdr.ethernet.dstAddr = dmac_0;
        standard_metadata.egress_spec = intf_0;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
    }
    @name("set_bd_dmac_intf") action set_bd_dmac_intf(@name("bd") bit<24> bd_0, @name("dmac") bit<48> dmac_0, @name("intf") bit<9> intf_0) {
        meta.fwd_metadata.out_bd = bd_0;
        hdr.ethernet.dstAddr = dmac_0;
        standard_metadata.egress_spec = intf_0;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
    }
    @name("ipv4_da_lpm") table ipv4_da_lpm_0 {
        actions = {
            set_l2ptr();
            drop_with_count();
        }
        key = {
            hdr.ipv4.dstAddr: lpm @name("hdr.ipv4.dstAddr") ;
        }
        default_action = drop_with_count();
        counters = ipv4_da_lpm_stats_0;
    }
    @name("mac_da") table mac_da_0 {
        actions = {
            set_bd_dmac_intf();
            my_drop_2(standard_metadata);
        }
        key = {
            meta.fwd_metadata.l2ptr: exact @name("meta.fwd_metadata.l2ptr") ;
        }
        default_action = my_drop_2(standard_metadata);
    }
    apply {
        ipv4_da_lpm_0.apply();
        mac_da_0.apply();
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".my_drop") action my_drop_1(@name("smeta") inout standard_metadata_t smeta_0) {
        mark_to_drop(smeta_0);
    }
    @name(".my_drop") action my_drop_3(@name("smeta") inout standard_metadata_t smeta_0) {
        mark_to_drop(smeta_0);
    }
    @name("rewrite_mac") action rewrite_mac_0(@name("smac") bit<48> smac_0) {
        hdr.ethernet.srcAddr = smac_0;
    }
    @name("rewrite_mac") action rewrite_mac(@name("smac") bit<48> smac_0) {
        hdr.ethernet.srcAddr = smac_0;
    }
    @name("send_frame") table send_frame_0 {
        actions = {
            rewrite_mac();
            my_drop_3(standard_metadata);
        }
        key = {
            meta.fwd_metadata.out_bd: exact @name("meta.fwd_metadata.out_bd") ;
        }
        default_action = my_drop_3(standard_metadata);
    }
    apply {
        send_frame_0.apply();
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
        verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

V1Switch<headers, metadata>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

