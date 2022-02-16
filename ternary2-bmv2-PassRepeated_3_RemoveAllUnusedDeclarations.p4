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
header data_h {
    bit<32> f1;
    bit<32> f2;
    bit<16> h1;
    bit<8>  b1;
    bit<8>  b2;
}

header extra_h {
    bit<16> h;
    bit<8>  b1;
    bit<8>  b2;
}

struct packet_t {
    data_h     data;
    extra_h[4] extra;
}

struct Meta {
}

parser p(packet_in b, out packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
    state start {
        b.extract<data_h>(hdrs.data);
        transition extra;
    }
    state extra {
        b.extract<extra_h>(hdrs.extra.next);
        transition select(hdrs.extra.last.b2) {
            8w0x80 &&& 8w0x80: extra;
            default: accept;
        }
    }
}

control vrfy(inout packet_t h, inout Meta m) {
    apply {
    }
}

control update(inout packet_t h, inout Meta m) {
    apply {
    }
}

control ingress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
    @name("setb1") action setb1_0(@name("port") bit<9> port, @name("val") bit<8> val) {
        hdrs.data.b1 = val;
        meta.egress_spec = port;
    }
    @name("noop") action noop_0() {
    }
    @name("noop") action noop_5() {
    }
    @name("noop") action noop_6() {
    }
    @name("noop") action noop_7() {
    }
    @name("noop") action noop_8() {
    }
    @name("reg") bit<8> reg;
    @name("setbyte") action setbyte_0(@name("val") bit<8> val_5) {
        reg = val_5;
        hdrs.extra[0].b1 = reg;
    }
    @name("reg") bit<8> reg_1;
    @name("setbyte") action setbyte_4(@name("val") bit<8> val_6) {
        reg_1 = val_6;
        hdrs.data.b2 = reg_1;
    }
    @name("reg") bit<8> reg_2;
    @name("setbyte") action setbyte_5(@name("val") bit<8> val_7) {
        reg_2 = val_7;
        hdrs.extra[1].b1 = reg_2;
    }
    @name("reg") bit<8> reg_3;
    @name("setbyte") action setbyte_6(@name("val") bit<8> val_8) {
        reg_3 = val_8;
        hdrs.extra[2].b2 = reg_3;
    }
    @name("act1") action act1_0(@name("val") bit<8> val_9) {
        hdrs.extra[0].b1 = val_9;
    }
    @name("act2") action act2_0(@name("val") bit<8> val_10) {
        hdrs.extra[0].b1 = val_10;
    }
    @name("act3") action act3_0(@name("val") bit<8> val_11) {
        hdrs.extra[0].b1 = val_11;
    }
    @name("test1") table test1 {
        key = {
            hdrs.data.f1: ternary @name("hdrs.data.f1") ;
        }
        actions = {
            setb1_0();
            noop_0();
        }
        default_action = noop_0();
    }
    @name("ex1") table ex1 {
        key = {
            hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
        }
        actions = {
            setbyte_0();
            act1_0();
            act2_0();
            act3_0();
            noop_5();
        }
        default_action = noop_5();
    }
    @name("tbl1") table tbl1 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte_4();
            noop_6();
        }
        default_action = noop_6();
    }
    @name("tbl2") table tbl2 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte_5();
            noop_7();
        }
        default_action = noop_7();
    }
    @name("tbl3") table tbl3 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte_6();
            noop_8();
        }
        default_action = noop_8();
    }
    apply {
        test1.apply();
        switch (ex1.apply().action_run) {
            act1_0: {
                tbl1.apply();
            }
            act2_0: {
                tbl2.apply();
            }
            act3_0: {
                tbl3.apply();
            }
            default: {
            }
        }
    }
}

control egress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
    apply {
    }
}

control deparser(packet_out b, in packet_t hdrs) {
    apply {
        b.emit<data_h>(hdrs.data);
        b.emit<extra_h[4]>(hdrs.extra);
    }
}

V1Switch<packet_t, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

