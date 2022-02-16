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
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_NORMAL = 32w0;
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_INGRESS_CLONE = 32w1;
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_EGRESS_CLONE = 32w2;
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_COALESCED = 32w3;
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_RECIRC = 32w4;
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_REPLICATION = 32w5;
const bit<32> BMV2_V1MODEL_INSTANCE_TYPE_RESUBMIT = 32w6;
const bit<32> I2E_CLONE_SESSION_ID = 32w5;
const bit<32> E2E_CLONE_SESSION_ID = 32w11;
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

header switch_to_cpu_header_t {
    bit<32> word0;
    bit<32> word1;
}

struct fwd_meta_t {
    bit<32> l2ptr;
    bit<24> out_bd;
}

struct meta_t {
    fwd_meta_t fwd;
}

struct headers_t {
    switch_to_cpu_header_t switch_to_cpu;
    ethernet_t             ethernet;
    ipv4_t                 ipv4;
}

action my_drop(inout standard_metadata_t smeta) {
    mark_to_drop(smeta);
}
parser ParserImpl(packet_in packet, out headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    const bit<16> ETHERTYPE_IPV4 = 16w0x800;
    state start {
        transition parse_ethernet;
    }
    state parse_ethernet {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        packet.extract<ipv4_t>(hdr.ipv4);
        transition accept;
    }
}

control fill_ipv4_address(out bit<32> ipv4_address, in bit<8> byte0, in bit<8> byte1, in bit<8> byte2, in bit<8> byte3) {
    apply {
        ipv4_address = byte0 ++ byte1 ++ byte2 ++ byte3;
    }
}

control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    fill_ipv4_address() c_fill_ipv4_address;
    const bit<32> RESUBMITTED_PKT_L2PTR = 32w0xe50b;
    const bit<32> RECIRCULATED_PKT_L2PTR = 32w0xec1c;
    action set_l2ptr(bit<32> l2ptr) {
        meta.fwd.l2ptr = l2ptr;
    }
    action set_mcast_grp(bit<16> mcast_grp) {
        standard_metadata.mcast_grp = mcast_grp;
    }
    action do_resubmit(bit<32> new_ipv4_dstAddr) {
        hdr.ipv4.dstAddr = new_ipv4_dstAddr;
        resubmit_preserving_field_list(8w0);
    }
    action do_clone_i2e(bit<32> l2ptr) {
        clone_preserving_field_list(CloneType.I2E, 32w5, 8w0);
        meta.fwd.l2ptr = l2ptr;
    }
    table ipv4_da_lpm {
        key = {
            hdr.ipv4.dstAddr: lpm @name("hdr.ipv4.dstAddr") ;
        }
        actions = {
            set_l2ptr();
            set_mcast_grp();
            do_resubmit();
            do_clone_i2e();
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }
    action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf) {
        meta.fwd.out_bd = bd;
        hdr.ethernet.dstAddr = dmac;
        standard_metadata.egress_spec = intf;
        hdr.ipv4.ttl = hdr.ipv4.ttl - 8w1;
    }
    table mac_da {
        key = {
            meta.fwd.l2ptr: exact @name("meta.fwd.l2ptr") ;
        }
        actions = {
            set_bd_dmac_intf();
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }
    apply {
        if (standard_metadata.instance_type == 32w6) {
            c_fill_ipv4_address.apply(hdr.ipv4.srcAddr, (bit<8>)10, (bit<8>)252, (bit<8>)129, (bit<8>)2);
            meta.fwd.l2ptr = 32w0xe50b;
        } else if (standard_metadata.instance_type == 32w4) {
            c_fill_ipv4_address.apply(hdr.ipv4.srcAddr, (bit<8>)10, (bit<8>)199, (bit<8>)86, (bit<8>)99);
            meta.fwd.l2ptr = 32w0xec1c;
        } else {
            ipv4_da_lpm.apply();
        }
        if (meta.fwd.l2ptr != 32w0) {
            mac_da.apply();
        }
    }
}

control egress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    action set_out_bd(bit<24> bd) {
        meta.fwd.out_bd = bd;
    }
    table get_multicast_copy_out_bd {
        key = {
            standard_metadata.mcast_grp : exact @name("standard_metadata.mcast_grp") ;
            standard_metadata.egress_rid: exact @name("standard_metadata.egress_rid") ;
        }
        actions = {
            set_out_bd();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    action rewrite_mac(bit<48> smac) {
        hdr.ethernet.srcAddr = smac;
    }
    action do_recirculate(bit<32> new_ipv4_dstAddr) {
        hdr.ipv4.dstAddr = new_ipv4_dstAddr;
        recirculate_preserving_field_list(8w0);
    }
    action do_clone_e2e(bit<48> smac) {
        hdr.ethernet.srcAddr = smac;
        clone_preserving_field_list(CloneType.E2E, 32w11, 8w0);
    }
    table send_frame {
        key = {
            meta.fwd.out_bd: exact @name("meta.fwd.out_bd") ;
        }
        actions = {
            rewrite_mac();
            do_recirculate();
            do_clone_e2e();
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }
    apply {
        if (standard_metadata.instance_type == 32w1) {
            hdr.switch_to_cpu.setValid();
            hdr.switch_to_cpu.word0 = (bit<32>)32w0x12e012e;
            hdr.switch_to_cpu.word1 = (bit<32>)32w0x5a5a5a5a;
        } else if (standard_metadata.instance_type == 32w2) {
            hdr.switch_to_cpu.setValid();
            hdr.switch_to_cpu.word0 = (bit<32>)32w0xe2e0e2e;
            hdr.switch_to_cpu.word1 = (bit<32>)32w0x5a5a5a5a;
        } else {
            if (standard_metadata.instance_type == 32w5) {
                get_multicast_copy_out_bd.apply();
            }
            send_frame.apply();
        }
    }
}

control DeparserImpl(packet_out packet, in headers_t hdr) {
    apply {
        packet.emit<switch_to_cpu_header_t>(hdr.switch_to_cpu);
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
    }
}

control verifyChecksum(inout headers_t hdr, inout meta_t meta) {
    apply {
        verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid() && hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers_t hdr, inout meta_t meta) {
    apply {
        update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid() && hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

V1Switch<headers_t, meta_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

