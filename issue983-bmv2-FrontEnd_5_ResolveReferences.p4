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
typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

struct fwd_meta_t {
    bit<16> tmp;
    bit<32> x1;
    bit<16> x2;
    bit<32> x3;
    bit<32> x4;
    bit<16> exp_etherType;
    bit<32> exp_x1;
    bit<16> exp_x2;
    bit<32> exp_x3;
    bit<32> exp_x4;
}

struct metadata {
    fwd_meta_t fwd_meta;
}

struct headers {
    ethernet_t ethernet;
}

parser IngressParserImpl(packet_in buffer, out headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
    state start {
        buffer.extract(hdr.ethernet);
        transition accept;
    }
}

control ingress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
    table debug_table_cksum1 {
        key = {
            hdr.ethernet.srcAddr            : exact;
            hdr.ethernet.dstAddr            : exact;
            hdr.ethernet.etherType          : exact;
            user_meta.fwd_meta.exp_etherType: exact;
            user_meta.fwd_meta.tmp          : exact;
            user_meta.fwd_meta.exp_x1       : exact;
            user_meta.fwd_meta.x1           : exact;
            user_meta.fwd_meta.exp_x2       : exact;
            user_meta.fwd_meta.x2           : exact;
            user_meta.fwd_meta.exp_x3       : exact;
            user_meta.fwd_meta.x3           : exact;
            user_meta.fwd_meta.exp_x4       : exact;
            user_meta.fwd_meta.x4           : exact;
        }
        actions = {
            NoAction();
        }
        default_action = NoAction();
    }
    bit<16> tmp;
    bit<32> x1;
    bit<16> x2;
    apply {
        tmp = ~hdr.ethernet.etherType;
        x1 = (bit<32>)tmp;
        x2 = x1[31:16] + x1[15:0];
        user_meta.fwd_meta.tmp = tmp;
        user_meta.fwd_meta.x1 = x1;
        user_meta.fwd_meta.x2 = x2;
        user_meta.fwd_meta.x3 = (bit<32>)~hdr.ethernet.etherType;
        user_meta.fwd_meta.x4 = ~(bit<32>)hdr.ethernet.etherType;
        user_meta.fwd_meta.exp_etherType = 0x800;
        user_meta.fwd_meta.exp_x1 = (bit<32>)~16w0x800;
        user_meta.fwd_meta.exp_x2 = ~16w0x800;
        user_meta.fwd_meta.exp_x3 = (bit<32>)~16w0x800;
        user_meta.fwd_meta.exp_x4 = ~32w0x800;
        hdr.ethernet.dstAddr = 0;
        if (hdr.ethernet.etherType != user_meta.fwd_meta.exp_etherType) {
            hdr.ethernet.dstAddr[47:40] = 1;
        }
        if (user_meta.fwd_meta.x1 != user_meta.fwd_meta.exp_x1) {
            hdr.ethernet.dstAddr[39:32] = 1;
        }
        if (user_meta.fwd_meta.x2 != user_meta.fwd_meta.exp_x2) {
            hdr.ethernet.dstAddr[31:24] = 1;
        }
        if (user_meta.fwd_meta.x3 != user_meta.fwd_meta.exp_x3) {
            hdr.ethernet.dstAddr[23:16] = 1;
        }
        if (user_meta.fwd_meta.x4 != user_meta.fwd_meta.exp_x4) {
            hdr.ethernet.dstAddr[15:8] = 1;
        }
        debug_table_cksum1.apply();
    }
}

control egress(inout headers hdr, inout metadata user_meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

V1Switch(IngressParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

