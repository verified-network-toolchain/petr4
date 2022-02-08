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

const bit<32> __v1model_version = 32w20200408;
typedef bit<9> PortId_t;
@metadata @name("standard_metadata") struct standard_metadata_t {
    PortId_t ingress_port;
    PortId_t egress_spec;
    PortId_t egress_port;
    bit<32>  instance_type;
    bit<32>  packet_length;
    @alias("queueing_metadata.enq_timestamp") 
    bit<32>  enq_timestamp;
    @alias("queueing_metadata.enq_qdepth") 
    bit<19>  enq_qdepth;
    @alias("queueing_metadata.deq_timedelta") 
    bit<32>  deq_timedelta;
    @alias("queueing_metadata.deq_qdepth") 
    bit<19>  deq_qdepth;
    @alias("intrinsic_metadata.ingress_global_timestamp") 
    bit<48>  ingress_global_timestamp;
    @alias("intrinsic_metadata.egress_global_timestamp") 
    bit<48>  egress_global_timestamp;
    @alias("intrinsic_metadata.mcast_grp") 
    bit<16>  mcast_grp;
    @alias("intrinsic_metadata.egress_rid") 
    bit<16>  egress_rid;
    bit<1>   checksum_error;
    error    parser_error;
    @alias("intrinsic_metadata.priority") 
    bit<3>   priority;
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

extern counter<I> {
    counter(bit<32> size, CounterType type);
    void count(in I index);
}

extern direct_counter {
    direct_counter(CounterType type);
    void count();
}

extern meter<I> {
    meter(bit<32> size, MeterType type);
    void execute_meter<T>(in I index, out T result);
}

extern direct_meter<T> {
    direct_meter(MeterType type);
    void read(out T result);
}

extern register<T, I> {
    register(bit<32> size);
    @noSideEffects void read(out T result, in I index);
    void write(in I index, in T value);
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

enum CloneType {
    I2E,
    E2E
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
header Header {
    bit<32> data;
}

struct H {
    Header h1;
    Header h2;
}

struct M {
}

parser ParserI(packet_in pkt, out H hdr, inout M meta, inout standard_metadata_t smeta) {
    state start {
        pkt.extract<Header>(hdr.h1);
        transition accept;
    }
}

control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    Header h1;
    Header h2;
    apply {
        h1.setInvalid();
        h2.setValid();
        h1.data = 32w0;
        h2.data = 32w1;
        switch (hdr.h1.data) {
            32w0: {
                h1.setValid();
                h2.setInvalid();
            }
            default: {
                h1.setValid();
                h2.setInvalid();
            }
        }
        hdr.h1.data = h1.data;
        hdr.h1.data = h2.data;
        switch (hdr.h1.data) {
            32w0: {
                h1.setValid();
                h2.setValid();
            }
            default: {
                h1.setInvalid();
                h2.setInvalid();
            }
        }
        hdr.h1.data = h1.data;
        hdr.h1.data = h2.data;
    }
}

control EgressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    apply {
    }
}

control DeparserI(packet_out pk, in H hdr) {
    apply {
    }
}

control VerifyChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}

control ComputeChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}

V1Switch<H, M>(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;

