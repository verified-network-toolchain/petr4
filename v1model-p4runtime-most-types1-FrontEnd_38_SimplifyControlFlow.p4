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
typedef bit<48> Eth0_t;
type bit<48> Eth1_t;
@p4runtime_translation("mycompany.com/EthernetAddress" , 49) type bit<48> Eth2_t;
typedef bit<8> Custom0_t;
type bit<8> Custom1_t;
@p4runtime_translation("mycompany.com/My_Byte2" , 12) type bit<8> Custom2_t;
typedef Custom0_t Custom00_t;
type Custom0_t Custom01_t;
@p4runtime_translation("mycompany.com/My_Byte3" , 13) type Custom0_t Custom02_t;
typedef Custom1_t Custom10_t;
type Custom1_t Custom11_t;
@p4runtime_translation("mycompany.com/My_Byte4" , 14) type Custom1_t Custom12_t;
typedef Custom2_t Custom20_t;
type Custom2_t Custom21_t;
@p4runtime_translation("mycompany.com/My_Byte5" , 15) type Custom2_t Custom22_t;
type Custom00_t Custom001_t;
@p4runtime_translation("mycompany.com/My_Byte6" , 16) type Custom00_t Custom002_t;
type Custom10_t Custom101_t;
@p4runtime_translation("mycompany.com/My_Byte7" , 17) type Custom10_t Custom102_t;
type Custom20_t Custom201_t;
@p4runtime_translation("mycompany.com/My_Byte8" , 18) type Custom20_t Custom202_t;
typedef Custom22_t Custom220_t;
typedef Custom002_t Custom0020_t;
typedef Custom0020_t Custom00200_t;
type Custom00200_t Custom002001_t;
@p4runtime_translation("mycompany.com/My_Byte9" , 19) type Custom00200_t Custom002002_t;
typedef Custom002001_t Custom0020010_t;
typedef Custom002002_t Custom0020020_t;
enum bit<8> serenum_t {
    A = 8w1,
    B = 8w3
}

typedef serenum_t serenum0_t;
header ethernet_t {
    Eth0_t  dstAddr;
    Eth1_t  srcAddr;
    bit<16> etherType;
}

struct struct1_t {
    bit<7> x;
    bit<9> y;
}

header custom_t {
    Eth0_t          addr0;
    Eth1_t          addr1;
    Eth2_t          addr2;
    bit<8>          e;
    Custom0_t       e0;
    Custom1_t       e1;
    Custom2_t       e2;
    Custom00_t      e00;
    Custom01_t      e01;
    Custom02_t      e02;
    Custom10_t      e10;
    Custom11_t      e11;
    Custom12_t      e12;
    Custom20_t      e20;
    Custom21_t      e21;
    Custom22_t      e22;
    Custom001_t     e001;
    Custom002_t     e002;
    Custom101_t     e101;
    Custom102_t     e102;
    Custom201_t     e201;
    Custom202_t     e202;
    Custom220_t     e220;
    Custom0020010_t e0020010;
    Custom0020020_t e0020020;
    struct1_t       my_nested_struct1;
    bit<16>         checksum;
    serenum0_t      s0;
}

@controller_header("packet_in") header packet_in_header_t {
    bit<8> punt_reason;
}

@controller_header("packet_out") header packet_out_header_t {
    Eth0_t          addr0;
    Eth1_t          addr1;
    Eth2_t          addr2;
    bit<8>          e;
    Custom0_t       e0;
    Custom1_t       e1;
    Custom2_t       e2;
    Custom00_t      e00;
    Custom01_t      e01;
    Custom02_t      e02;
    Custom10_t      e10;
    Custom11_t      e11;
    Custom12_t      e12;
    Custom20_t      e20;
    Custom21_t      e21;
    Custom22_t      e22;
    Custom001_t     e001;
    Custom002_t     e002;
    Custom101_t     e101;
    Custom102_t     e102;
    Custom201_t     e201;
    Custom202_t     e202;
    Custom220_t     e220;
    Custom0020010_t e0020010;
    Custom0020020_t e0020020;
}

struct headers_t {
    packet_in_header_t  packet_in;
    packet_out_header_t packet_out;
    ethernet_t          ethernet;
    custom_t            custom;
}

struct valueset1_t {
    Eth0_t     addr0;
    bit<8>     e;
    Custom0_t  e0;
    Custom00_t e00;
}

struct metadata_t {
}

parser ParserImpl(packet_in packet, out headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    @name("valueset1") value_set<valueset1_t>(4) valueset1_0;
    state start {
        transition select(stdmeta.ingress_port) {
            9w0: parse_packet_out_header;
            default: parse_ethernet;
        }
    }
    state parse_packet_out_header {
        packet.extract<packet_out_header_t>(hdr.packet_out);
        transition select(hdr.packet_out.addr0, hdr.packet_out.e, hdr.packet_out.e0, hdr.packet_out.e00) {
            valueset1_0: accept;
            default: parse_ethernet;
        }
    }
    state parse_ethernet {
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

control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    @name("set_output") action set_output_0(bit<9> out_port) {
        stdmeta.egress_spec = out_port;
    }
    @name("set_headers") action set_headers_0(Eth0_t addr0, Eth1_t addr1, Eth2_t addr2, bit<8> e, Custom0_t e0, Custom1_t e1, Custom2_t e2, Custom00_t e00, Custom01_t e01, Custom02_t e02, Custom10_t e10, Custom11_t e11, Custom12_t e12, Custom20_t e20, Custom21_t e21, Custom22_t e22, Custom001_t e001, Custom002_t e002, Custom101_t e101, Custom102_t e102, Custom201_t e201, Custom202_t e202, Custom220_t e220, Custom0020010_t e0020010, Custom0020020_t e0020020, serenum0_t s0) {
        hdr.custom.addr0 = addr0;
        hdr.custom.addr1 = addr1;
        hdr.custom.addr2 = addr2;
        hdr.custom.e = e;
        hdr.custom.e0 = e0;
        hdr.custom.e1 = e1;
        hdr.custom.e2 = e2;
        hdr.custom.e00 = e00;
        hdr.custom.e01 = e01;
        hdr.custom.e02 = e02;
        hdr.custom.e10 = e10;
        hdr.custom.e11 = e11;
        hdr.custom.e12 = e12;
        hdr.custom.e20 = e20;
        hdr.custom.e21 = e21;
        hdr.custom.e22 = e22;
        hdr.custom.e001 = e001;
        hdr.custom.e002 = e002;
        hdr.custom.e101 = e101;
        hdr.custom.e102 = e102;
        hdr.custom.e201 = e201;
        hdr.custom.e202 = e202;
        hdr.custom.e220 = e220;
        hdr.custom.e0020010 = e0020010;
        hdr.custom.e0020020 = e0020020;
        hdr.custom.s0 = s0;
    }
    @name("my_drop") action my_drop_0() {
    }
    @name("custom_table") table custom_table_0 {
        key = {
            hdr.custom.addr0   : exact @name("hdr.custom.addr0") ;
            hdr.custom.addr1   : exact @name("hdr.custom.addr1") ;
            hdr.custom.addr2   : exact @name("hdr.custom.addr2") ;
            hdr.custom.e       : exact @name("hdr.custom.e") ;
            hdr.custom.e0      : exact @name("hdr.custom.e0") ;
            hdr.custom.e1      : exact @name("hdr.custom.e1") ;
            hdr.custom.e2      : exact @name("hdr.custom.e2") ;
            hdr.custom.e00     : exact @name("hdr.custom.e00") ;
            hdr.custom.e01     : exact @name("hdr.custom.e01") ;
            hdr.custom.e02     : exact @name("hdr.custom.e02") ;
            hdr.custom.e10     : exact @name("hdr.custom.e10") ;
            hdr.custom.e11     : exact @name("hdr.custom.e11") ;
            hdr.custom.e12     : exact @name("hdr.custom.e12") ;
            hdr.custom.e20     : exact @name("hdr.custom.e20") ;
            hdr.custom.e21     : exact @name("hdr.custom.e21") ;
            hdr.custom.e22     : exact @name("hdr.custom.e22") ;
            hdr.custom.e001    : exact @name("hdr.custom.e001") ;
            hdr.custom.e002    : exact @name("hdr.custom.e002") ;
            hdr.custom.e101    : exact @name("hdr.custom.e101") ;
            hdr.custom.e102    : exact @name("hdr.custom.e102") ;
            hdr.custom.e201    : exact @name("hdr.custom.e201") ;
            hdr.custom.e202    : exact @name("hdr.custom.e202") ;
            hdr.custom.e220    : exact @name("hdr.custom.e220") ;
            hdr.custom.e0020010: exact @name("hdr.custom.e0020010") ;
            hdr.custom.e0020020: exact @name("hdr.custom.e0020020") ;
            hdr.custom.s0      : exact @name("hdr.custom.s0") ;
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

control egress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers_t hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<custom_t>(hdr.custom);
    }
}

control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
        verify_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, serenum_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
        update_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, serenum_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
    }
}

V1Switch<headers_t, metadata_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

