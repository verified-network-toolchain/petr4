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
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
    bit<8> b;
    bit<8> c;
    bit<8> d;
    bit<8> e;
    bit<8> f;
    bit<8> g;
    bit<8> h;
    bit<8> i;
    bit<8> j;
    bit<8> k;
    bit<8> l;
    bit<8> m;
}

header B {
    bit<8> a;
    bit<8> b;
    bit<8> c;
    bit<8> d;
}

struct Headers {
    ethernet_t eth_hdr;
    H          h;
    B          b;
}

struct Meta {
}

bit<8> function_with_side_effect(inout bit<8> val) {
    val = 8w1;
    return 8w2;
}
parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        pkt.extract<H>(hdr.h);
        pkt.extract<B>(hdr.b);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    @name("dummy_var") bit<8> dummy_var_0;
    @name("dummy_bool") bool dummy_bool_0;
    bit<8> tmp;
    bit<8> tmp_0;
    bit<8> tmp_1;
    bit<8> tmp_2;
    bit<8> tmp_3;
    bit<8> tmp_4;
    bit<8> tmp_5;
    bit<8> tmp_6;
    bit<8> tmp_7;
    bit<8> tmp_8;
    bit<8> tmp_9;
    bit<8> tmp_10;
    bit<8> tmp_11;
    bit<8> tmp_12;
    bit<8> tmp_13;
    bit<8> tmp_14;
    bit<8> tmp_15;
    bit<8> tmp_16;
    bit<8> tmp_17;
    bit<8> tmp_18;
    bit<8> tmp_19;
    bit<8> tmp_20;
    bit<8> tmp_21;
    bit<8> tmp_22;
    bit<8> tmp_23;
    bit<8> tmp_24;
    bit<8> tmp_25;
    bit<8> tmp_26;
    bit<8> tmp_27;
    bit<8> tmp_28;
    bit<8> tmp_29;
    bit<16> tmp_30;
    bit<8> tmp_31;
    bit<24> tmp_32;
    bit<8> tmp_33;
    bit<8> tmp_34;
    bit<8> tmp_35;
    bool tmp_36;
    bit<8> tmp_37;
    bit<8> tmp_38;
    bit<8> tmp_39;
    bool tmp_40;
    apply {
        tmp_0 = function_with_side_effect(h.h.a);
        tmp_3 = function_with_side_effect(h.h.b);
        tmp_6 = function_with_side_effect(h.h.c);
        tmp_9 = function_with_side_effect(h.h.d);
        tmp_12 = function_with_side_effect(h.h.e);
        tmp_15 = function_with_side_effect(h.h.f);
        dummy_var_0 = function_with_side_effect(h.h.g);
        tmp_18 = function_with_side_effect(h.h.h);
        tmp_21 = function_with_side_effect(h.h.i);
        tmp_24 = function_with_side_effect(h.h.j);
        tmp_27 = function_with_side_effect(h.h.k);
        tmp_29 = function_with_side_effect(h.h.l);
        tmp_31 = function_with_side_effect(h.h.m);
        tmp_34 = function_with_side_effect(h.b.c);
        tmp_35 = function_with_side_effect(h.b.c);
        tmp_38 = function_with_side_effect(h.b.d);
        tmp_39 = function_with_side_effect(h.b.d);
    }
}

control vrfy(inout Headers h, inout Meta m) {
    apply {
    }
}

control update(inout Headers h, inout Meta m) {
    apply {
    }
}

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
    }
}

control deparser(packet_out b, in Headers h) {
    apply {
        b.emit<Headers>(h);
    }
}

V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

