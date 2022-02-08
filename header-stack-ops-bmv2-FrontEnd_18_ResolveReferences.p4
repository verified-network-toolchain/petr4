error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument,
    BadHeaderType
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
header h1_t {
    bit<8> hdr_type;
    bit<8> op1;
    bit<8> op2;
    bit<8> op3;
    bit<8> h2_valid_bits;
    bit<8> next_hdr_type;
}

header h2_t {
    bit<8> hdr_type;
    bit<8> f1;
    bit<8> f2;
    bit<8> next_hdr_type;
}

header h3_t {
    bit<8> hdr_type;
    bit<8> data;
}

struct headers {
    h1_t    h1;
    h2_t[5] h2;
    h3_t    h3;
}

struct metadata {
}

parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract<h1_t>(hdr.h1);
        verify(hdr.h1.hdr_type == 8w1, error.BadHeaderType);
        transition select(hdr.h1.next_hdr_type) {
            8w2: parse_h2;
            8w3: parse_h3;
            default: accept;
        }
    }
    state parse_h2 {
        pkt.extract<h2_t>(hdr.h2.next);
        verify(hdr.h2.last.hdr_type == 8w2, error.BadHeaderType);
        transition select(hdr.h2.last.next_hdr_type) {
            8w2: parse_h2;
            8w3: parse_h3;
            default: accept;
        }
    }
    state parse_h3 {
        pkt.extract<h3_t>(hdr.h3);
        verify(hdr.h3.hdr_type == 8w3, error.BadHeaderType);
        transition accept;
    }
}

control cDoOneOp(inout headers hdr, in bit<8> op) {
    apply {
        if (op == 8w0x0) {
        } else if (op[7:4] == 4w1) {
            if (op[3:0] == 4w1) {
                hdr.h2.push_front(1);
            } else if (op[3:0] == 4w2) {
                hdr.h2.push_front(2);
            } else if (op[3:0] == 4w3) {
                hdr.h2.push_front(3);
            } else if (op[3:0] == 4w4) {
                hdr.h2.push_front(4);
            } else if (op[3:0] == 4w5) {
                hdr.h2.push_front(5);
            } else if (op[3:0] == 4w6) {
                hdr.h2.push_front(6);
            }
        } else if (op[7:4] == 4w2) {
            if (op[3:0] == 4w1) {
                hdr.h2.pop_front(1);
            } else if (op[3:0] == 4w2) {
                hdr.h2.pop_front(2);
            } else if (op[3:0] == 4w3) {
                hdr.h2.pop_front(3);
            } else if (op[3:0] == 4w4) {
                hdr.h2.pop_front(4);
            } else if (op[3:0] == 4w5) {
                hdr.h2.pop_front(5);
            } else if (op[3:0] == 4w6) {
                hdr.h2.pop_front(6);
            }
        } else if (op[7:4] == 4w3) {
            if (op[3:0] == 4w0) {
                hdr.h2[0].setValid();
                hdr.h2[0].hdr_type = (bit<8>)8w2;
                hdr.h2[0].f1 = (bit<8>)8w0xa0;
                hdr.h2[0].f2 = (bit<8>)8w0xa;
                hdr.h2[0].next_hdr_type = (bit<8>)8w9;
            } else if (op[3:0] == 4w1) {
                hdr.h2[1].setValid();
                hdr.h2[1].hdr_type = (bit<8>)8w2;
                hdr.h2[1].f1 = (bit<8>)8w0xa1;
                hdr.h2[1].f2 = (bit<8>)8w0x1a;
                hdr.h2[1].next_hdr_type = (bit<8>)8w9;
            } else if (op[3:0] == 4w2) {
                hdr.h2[2].setValid();
                hdr.h2[2].hdr_type = (bit<8>)8w2;
                hdr.h2[2].f1 = (bit<8>)8w0xa2;
                hdr.h2[2].f2 = (bit<8>)8w0x2a;
                hdr.h2[2].next_hdr_type = (bit<8>)8w9;
            } else if (op[3:0] == 4w3) {
                hdr.h2[3].setValid();
                hdr.h2[3].hdr_type = (bit<8>)8w2;
                hdr.h2[3].f1 = (bit<8>)8w0xa3;
                hdr.h2[3].f2 = (bit<8>)8w0x3a;
                hdr.h2[3].next_hdr_type = (bit<8>)8w9;
            } else if (op[3:0] == 4w4) {
                hdr.h2[4].setValid();
                hdr.h2[4].hdr_type = (bit<8>)8w2;
                hdr.h2[4].f1 = (bit<8>)8w0xa4;
                hdr.h2[4].f2 = (bit<8>)8w0x4a;
                hdr.h2[4].next_hdr_type = (bit<8>)8w9;
            }
        } else if (op[7:4] == 4w4) {
            if (op[3:0] == 4w0) {
                hdr.h2[0].setInvalid();
            } else if (op[3:0] == 4w1) {
                hdr.h2[1].setInvalid();
            } else if (op[3:0] == 4w2) {
                hdr.h2[2].setInvalid();
            } else if (op[3:0] == 4w3) {
                hdr.h2[3].setInvalid();
            } else if (op[3:0] == 4w4) {
                hdr.h2[4].setInvalid();
            }
        }
    }
}

control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    cDoOneOp() do_one_op;
    apply {
        do_one_op.apply(hdr, hdr.h1.op1);
        do_one_op.apply(hdr, hdr.h1.op2);
        do_one_op.apply(hdr, hdr.h1.op3);
        hdr.h1.h2_valid_bits = (bit<8>)8w0;
        if (hdr.h2[0].isValid()) {
            hdr.h1.h2_valid_bits[0:0] = (bit<1>)1w1;
        }
        if (hdr.h2[1].isValid()) {
            hdr.h1.h2_valid_bits[1:1] = (bit<1>)1w1;
        }
        if (hdr.h2[2].isValid()) {
            hdr.h1.h2_valid_bits[2:2] = (bit<1>)1w1;
        }
        if (hdr.h2[3].isValid()) {
            hdr.h1.h2_valid_bits[3:3] = (bit<1>)1w1;
        }
        if (hdr.h2[4].isValid()) {
            hdr.h1.h2_valid_bits[4:4] = (bit<1>)1w1;
        }
    }
}

control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}

control vc(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control uc(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control DeparserI(packet_out packet, in headers hdr) {
    apply {
        packet.emit<h1_t>(hdr.h1);
        packet.emit<h2_t[5]>(hdr.h2);
        packet.emit<h3_t>(hdr.h3);
    }
}

V1Switch<headers, metadata>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;

