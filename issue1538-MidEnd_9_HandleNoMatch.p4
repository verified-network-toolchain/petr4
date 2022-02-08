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

parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
struct metadata {
    bit<16> tmp_port;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

struct headers {
    ethernet_t ethernet;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("ParserImpl.tmp_port") bit<16> tmp_port_0;
    @name("ParserImpl.x_1") bit<16> x;
    @name("ParserImpl.hasReturned") bool hasReturned;
    @name("ParserImpl.retval") bit<16> retval;
    @name("ParserImpl.x_2") bit<16> x_6;
    @name("ParserImpl.hasReturned") bool hasReturned_0;
    @name("ParserImpl.retval") bit<16> retval_0;
    state start {
        x = (bit<16>)standard_metadata.ingress_port;
        hasReturned = false;
        hasReturned = true;
        retval = x + 16w1;
        tmp_port_0 = retval;
        transition start_0;
    }
    state start_0 {
        packet.extract<ethernet_t>(hdr.ethernet);
        x_6 = hdr.ethernet.etherType;
        hasReturned_0 = false;
        hasReturned_0 = true;
        retval_0 = x_6 + 16w1;
        hdr.ethernet.etherType = retval_0;
        meta.tmp_port = tmp_port_0;
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("ingress.smeta") standard_metadata_t smeta_0;
    @name("ingress.x_3") bit<16> x_7;
    @name("ingress.hasReturned_0") bool hasReturned_3;
    @name("ingress.retval_0") bit<16> retval_3;
    @name("ingress.tmp") bit<16> tmp;
    @name("ingress.tmp_0") bit<16> tmp_0;
    @name("ingress.tmp_1") bit<16> tmp_1;
    @name("ingress.x_0") bit<16> x_8;
    @name("ingress.hasReturned") bool hasReturned_4;
    @name("ingress.retval") bit<16> retval_4;
    @name("ingress.x_4") bit<16> x_9;
    @name("ingress.hasReturned") bool hasReturned_5;
    @name("ingress.retval") bit<16> retval_5;
    @name("ingress.x_5") bit<16> x_10;
    @name("ingress.hasReturned") bool hasReturned_6;
    @name("ingress.retval") bit<16> retval_6;
    @name(".my_drop") action my_drop_0() {
        smeta_0 = standard_metadata;
        mark_to_drop(smeta_0);
        standard_metadata = smeta_0;
    }
    @name("ingress.set_port") action set_port(@name("output_port") bit<9> output_port) {
        standard_metadata.egress_spec = output_port;
    }
    @name("ingress.mac_da") table mac_da_0 {
        key = {
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
        }
        actions = {
            set_port();
            my_drop_0();
        }
        default_action = my_drop_0();
    }
    apply {
        mac_da_0.apply();
        x_7 = hdr.ethernet.srcAddr[15:0];
        hasReturned_3 = false;
        tmp = x_7;
        x_8 = x_7;
        hasReturned_4 = false;
        hasReturned_4 = true;
        retval_4 = x_8 + 16w1;
        tmp_0 = retval_4;
        tmp_1 = tmp + tmp_0;
        hasReturned_3 = true;
        retval_3 = tmp_1;
        hdr.ethernet.srcAddr[15:0] = retval_3;
        x_9 = hdr.ethernet.srcAddr[15:0];
        hasReturned_5 = false;
        hasReturned_5 = true;
        retval_5 = x_9 + 16w1;
        hdr.ethernet.srcAddr[15:0] = retval_5;
        x_10 = hdr.ethernet.etherType;
        hasReturned_6 = false;
        hasReturned_6 = true;
        retval_6 = x_10 + 16w1;
        hdr.ethernet.etherType = retval_6;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
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

