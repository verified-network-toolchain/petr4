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

extern void verify_checksum<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@pure extern void update_checksum<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
typedef bit<48> EthD_t;
@p4runtime_translation("p4.org/psa/v1/EthT_t" , 48) type bit<48> EthT_t;
typedef bit<8> CustomD_t;
type bit<8> CustomT_t;
typedef CustomD_t CustomDD_t;
type CustomD_t CustomDT_t;
typedef CustomT_t CustomTD_t;
type CustomT_t CustomTT_t;
typedef CustomDD_t CustomDDD_t;
type CustomDD_t CustomDDT_t;
typedef CustomDT_t CustomDTD_t;
type CustomDT_t CustomDTT_t;
typedef CustomTD_t CustomTDD_t;
type CustomTD_t CustomTDT_t;
typedef CustomTT_t CustomTTD_t;
type CustomTT_t CustomTTT_t;
header ethernet_t {
    EthD_t  dstAddr;
    EthT_t  srcAddr;
    bit<16> etherType;
}

header custom_t {
    bit<8>      e;
    CustomD_t   ed;
    CustomT_t   et;
    CustomDD_t  edd;
    CustomDT_t  edt;
    CustomTD_t  etd;
    CustomTT_t  ett;
    CustomDDD_t eddd;
    CustomDDT_t eddt;
    CustomDTD_t edtd;
    CustomDTT_t edtt;
    CustomTDD_t etdd;
    CustomTDT_t etdt;
    CustomTTD_t ettd;
    CustomTTT_t ettt;
    bit<16>     checksum;
}

struct meta_t {
}

struct headers_t {
    ethernet_t ethernet;
    custom_t   custom;
}

parser ParserImpl(packet_in packet, out headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0xdead: parse_custom;
            default: accept;
        }
    }
    state parse_custom {
        packet.extract<custom_t>(hdr.custom);
        transition accept;
    }
}

control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    @name("set_output") action set_output_0(@name("out_port") bit<9> out_port_0) {
        standard_metadata.egress_spec = out_port_0;
    }
    @name("set_headers") action set_headers_0(@name("e") bit<8> e_0, @name("ed") CustomD_t ed_0, @name("et") CustomT_t et_0, @name("edd") CustomDD_t edd_0, @name("edt") CustomDT_t edt_0, @name("etd") CustomTD_t etd_0, @name("ett") CustomTT_t ett_0, @name("eddd") CustomDDD_t eddd_0, @name("eddt") CustomDDT_t eddt_0, @name("edtd") CustomDTD_t edtd_0, @name("edtt") CustomDTT_t edtt_0, @name("etdd") CustomTDD_t etdd_0, @name("etdt") CustomTDT_t etdt_0, @name("ettd") CustomTTD_t ettd_0, @name("ettt") CustomTTT_t ettt_0) {
        hdr.custom.e = e_0;
        hdr.custom.ed = ed_0;
        hdr.custom.et = et_0;
        hdr.custom.edd = edd_0;
        hdr.custom.edt = edt_0;
        hdr.custom.etd = etd_0;
        hdr.custom.ett = ett_0;
        hdr.custom.eddd = eddd_0;
        hdr.custom.eddt = eddt_0;
        hdr.custom.edtd = edtd_0;
        hdr.custom.edtt = edtt_0;
        hdr.custom.etdd = etdd_0;
        hdr.custom.etdt = etdt_0;
        hdr.custom.ettd = ettd_0;
        hdr.custom.ettt = ettt_0;
    }
    @name("my_drop") action my_drop_0() {
    }
    @name("custom_table") table custom_table_0 {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
            hdr.custom.e        : exact @name("hdr.custom.e") ;
            hdr.custom.ed       : exact @name("hdr.custom.ed") ;
            hdr.custom.et       : exact @name("hdr.custom.et") ;
            hdr.custom.edd      : exact @name("hdr.custom.edd") ;
            hdr.custom.eddt     : exact @name("hdr.custom.eddt") ;
            hdr.custom.edtd     : exact @name("hdr.custom.edtd") ;
            hdr.custom.edtt     : exact @name("hdr.custom.edtt") ;
            hdr.custom.etdd     : exact @name("hdr.custom.etdd") ;
            hdr.custom.etdt     : exact @name("hdr.custom.etdt") ;
            hdr.custom.ettd     : exact @name("hdr.custom.ettd") ;
            hdr.custom.ettt     : exact @name("hdr.custom.ettt") ;
        }
        actions = {
            set_output_0();
            set_headers_0();
            my_drop_0();
        }
        default_action = my_drop_0();
    }
    apply {
        if (hdr.custom.isValid()) {
            custom_table_0.apply();
        }
    }
}

control egress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers_t hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<custom_t>(hdr.custom);
    }
}

control verifyChecksum(inout headers_t hdr, inout meta_t meta) {
    apply {
        verify_checksum<tuple<bit<8>, bit<8>, CustomT_t, bit<8>, CustomDT_t, CustomT_t, CustomTT_t, bit<8>, CustomDDT_t, CustomDT_t, CustomDTT_t, CustomT_t, CustomTDT_t, CustomTT_t, CustomTTT_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.e, hdr.custom.ed, hdr.custom.et, hdr.custom.edd, hdr.custom.edt, hdr.custom.etd, hdr.custom.ett, hdr.custom.eddd, hdr.custom.eddt, hdr.custom.edtd, hdr.custom.edtt, hdr.custom.etdd, hdr.custom.etdt, hdr.custom.ettd, hdr.custom.ettt }, hdr.custom.checksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers_t hdr, inout meta_t meta) {
    apply {
        update_checksum<tuple<bit<8>, bit<8>, CustomT_t, bit<8>, CustomDT_t, CustomT_t, CustomTT_t, bit<8>, CustomDDT_t, CustomDT_t, CustomDTT_t, CustomT_t, CustomTDT_t, CustomTT_t, CustomTTT_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.e, hdr.custom.ed, hdr.custom.et, hdr.custom.edd, hdr.custom.edt, hdr.custom.etd, hdr.custom.ett, hdr.custom.eddd, hdr.custom.eddt, hdr.custom.edtd, hdr.custom.edtt, hdr.custom.etdd, hdr.custom.etdt, hdr.custom.ettd, hdr.custom.ettt }, hdr.custom.checksum, HashAlgorithm.csum16);
    }
}

V1Switch<headers_t, meta_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

