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

extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header h0_t {
    bit<8> f0;
}

header h1_t {
    bit<8> f1;
}

header h2_t {
    bit<8> f2;
}

header h3_t {
    bit<8> f3;
}

header h4_t {
    bit<8> f4;
}

struct metadata {
}

struct headers {
    ethernet_t ethernet;
    h0_t       h0;
    h1_t       h1;
    h2_t       h2;
    h3_t       h3;
    h4_t       h4;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.srcAddr[7:0], hdr.ethernet.etherType) {
            (8w0x61 .. 8w0x67, 16w0x800 .. 16w0x806): parse_h0;
            (8w0x61 .. 8w0x67, 16w0x901 .. 16w0x902): parse_h1;
            (8w0x77 .. 8w0x7b, 16w0x801 .. 16w0x806): parse_h2;
            (8w0x77 .. 8w0x7b, 16w0xa00 .. 16w0xaaa): parse_h3;
            (default, 16w0xa00 .. 16w0xaaa): parse_h4;
            default: accept;
        }
    }
    state parse_h0 {
        packet.extract<h0_t>(hdr.h0);
        transition accept;
    }
    state parse_h1 {
        packet.extract<h1_t>(hdr.h1);
        transition accept;
    }
    state parse_h2 {
        packet.extract<h2_t>(hdr.h2);
        transition accept;
    }
    state parse_h3 {
        packet.extract<h3_t>(hdr.h3);
        transition accept;
    }
    state parse_h4 {
        packet.extract<h4_t>(hdr.h4);
        transition accept;
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("tmp") bit<1> tmp_4;
    @name("tmp_0") bit<1> tmp_5;
    @name("tmp_1") bit<1> tmp_6;
    @name("tmp_2") bit<1> tmp_7;
    @name("tmp_3") bit<1> tmp_8;
    apply {
        if (hdr.h4.isValid()) {
            tmp_4 = 1w1;
        } else {
            tmp_4 = 1w0;
        }
        hdr.ethernet.dstAddr[44:44] = tmp_4;
        if (hdr.h3.isValid()) {
            tmp_5 = 1w1;
        } else {
            tmp_5 = 1w0;
        }
        hdr.ethernet.dstAddr[43:43] = tmp_5;
        if (hdr.h2.isValid()) {
            tmp_6 = 1w1;
        } else {
            tmp_6 = 1w0;
        }
        hdr.ethernet.dstAddr[42:42] = tmp_6;
        if (hdr.h1.isValid()) {
            tmp_7 = 1w1;
        } else {
            tmp_7 = 1w0;
        }
        hdr.ethernet.dstAddr[41:41] = tmp_7;
        if (hdr.h0.isValid()) {
            tmp_8 = 1w1;
        } else {
            tmp_8 = 1w0;
        }
        hdr.ethernet.dstAddr[40:40] = tmp_8;
        standard_metadata.egress_spec = 9w3;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<h0_t>(hdr.h0);
        packet.emit<h1_t>(hdr.h1);
        packet.emit<h2_t>(hdr.h2);
        packet.emit<h3_t>(hdr.h3);
        packet.emit<h4_t>(hdr.h4);
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

V1Switch<headers, metadata>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

