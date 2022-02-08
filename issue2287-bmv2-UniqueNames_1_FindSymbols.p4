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

parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        pkt.extract<H>(hdr.h);
        pkt.extract<B>(hdr.b);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    @name("dummy_var") bit<8> dummy_var;
    @name("tmp_0") bit<8> tmp;
    @name("tmp_3") bit<8> tmp_1;
    @name("tmp_6") bit<8> tmp_2;
    @name("tmp_9") bit<8> tmp_4;
    @name("tmp_12") bit<8> tmp_5;
    @name("tmp_15") bit<8> tmp_7;
    @name("tmp_18") bit<8> tmp_8;
    @name("tmp_21") bit<8> tmp_10;
    @name("tmp_24") bit<8> tmp_11;
    @name("tmp_27") bit<8> tmp_13;
    @name("tmp_29") bit<8> tmp_14;
    @name("tmp_31") bit<8> tmp_16;
    @name("tmp_34") bit<8> tmp_17;
    @name("tmp_35") bit<8> tmp_19;
    @name("tmp_38") bit<8> tmp_20;
    @name("tmp_39") bit<8> tmp_22;
    apply {
        {
            bit<8> val_0 = h.h.a;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_0 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.a = val_0;
            tmp = retval_0;
        }
        {
            bit<8> val_1 = h.h.b;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_1 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.b = val_1;
            tmp_1 = retval_0;
        }
        {
            bit<8> val_2 = h.h.c;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_2 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.c = val_2;
            tmp_2 = retval_0;
        }
        {
            bit<8> val_3 = h.h.d;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_3 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.d = val_3;
            tmp_4 = retval_0;
        }
        {
            bit<8> val_4 = h.h.e;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_4 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.e = val_4;
            tmp_5 = retval_0;
        }
        {
            bit<8> val_5 = h.h.f;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_5 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.f = val_5;
            tmp_7 = retval_0;
        }
        {
            bit<8> val_6 = h.h.g;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_6 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.g = val_6;
            dummy_var = retval_0;
        }
        {
            bit<8> val_7 = h.h.h;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_7 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.h = val_7;
            tmp_8 = retval_0;
        }
        {
            bit<8> val_8 = h.h.i;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_8 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.i = val_8;
            tmp_10 = retval_0;
        }
        {
            bit<8> val_9 = h.h.j;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_9 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.j = val_9;
            tmp_11 = retval_0;
        }
        {
            bit<8> val_10 = h.h.k;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_10 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.k = val_10;
            tmp_13 = retval_0;
        }
        {
            bit<8> val_11 = h.h.l;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_11 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.l = val_11;
            tmp_14 = retval_0;
        }
        {
            bit<8> val_12 = h.h.m;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_12 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.h.m = val_12;
            tmp_16 = retval_0;
        }
        {
            bit<8> val_13 = h.b.c;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_13 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.b.c = val_13;
            tmp_17 = retval_0;
        }
        {
            bit<8> val_14 = h.b.c;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_14 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.b.c = val_14;
            tmp_19 = retval_0;
        }
        {
            bit<8> val_15 = h.b.d;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_15 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.b.d = val_15;
            tmp_20 = retval_0;
        }
        {
            bit<8> val_16 = h.b.d;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<8> retval_0;
            hasReturned_0 = false;
            val_16 = 8w1;
            hasReturned_0 = true;
            retval_0 = 8w2;
            h.b.d = val_16;
            tmp_22 = retval_0;
        }
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

