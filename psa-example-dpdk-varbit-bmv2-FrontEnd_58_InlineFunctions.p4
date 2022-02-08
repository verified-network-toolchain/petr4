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
#include <bmv2/psa.p4>

typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header ipv4_base_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}

header ipv4_option_timestamp_t {
    bit<8>      value;
    bit<8>      len;
    varbit<304> data;
}

struct headers_t {
    ethernet_t              ethernet;
    ipv4_base_t             ipv4_base;
    ipv4_option_timestamp_t ipv4_option_timestamp;
}

struct EMPTY {
}

parser MyIP(packet_in packet, out headers_t hdr, inout EMPTY b, in psa_ingress_parser_input_metadata_t c, in EMPTY d, in EMPTY e) {
    @name("tmp16") bit<16> tmp16;
    @name("tmp_len") bit<8> tmp_len;
    @name("tmp") bit<8> tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        packet.extract<ipv4_base_t>(hdr.ipv4_base);
        transition select(hdr.ipv4_base.ihl) {
            4w0x5: accept;
            default: parse_ipv4_options;
        }
    }
    state parse_ipv4_option_timestamp {
        tmp16 = packet.lookahead<bit<16>>();
        tmp_len = tmp16[7:0];
        packet.extract<ipv4_option_timestamp_t>(hdr.ipv4_option_timestamp, ((bit<32>)tmp_len << 3) + 32w4294967280);
        transition accept;
    }
    state parse_ipv4_options {
        tmp_2 = packet.lookahead<bit<8>>();
        tmp_1 = tmp_2;
        transition select(tmp_1) {
            8w0x44: parse_ipv4_option_timestamp;
            default: accept;
        }
    }
}

parser MyEP(packet_in buffer, out EMPTY a, inout EMPTY b, in psa_egress_parser_input_metadata_t c, in EMPTY d, in EMPTY e, in EMPTY f) {
    state start {
        transition accept;
    }
}

control MyIC(inout headers_t hdr, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_3() {
    }
    @name("meta") psa_ingress_output_metadata_t meta_1;
    @name("egress_port") PortId_t egress_port_1;
    @noWarnUnused @name(".send_to_port") action send_to_port() {
        meta_1 = d;
        egress_port_1 = (PortId_t)32w0;
        meta_1.drop = false;
        meta_1.multicast_group = (MulticastGroup_t)32w0;
        meta_1.egress_port = egress_port_1;
        d = meta_1;
    }
    @name("ap") ActionProfile(32w1024) ap;
    @name("a1") action a1_0(@name("param") bit<48> param) {
        hdr.ethernet.dstAddr = param;
    }
    @name("a2") action a2_0(@name("param") bit<16> param_2) {
        hdr.ethernet.etherType = param_2;
    }
    @name("tbl") table tbl {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            NoAction_0();
            a2_0();
        }
        psa_implementation = ap;
        default_action = NoAction_0();
    }
    @name("tbl2") table tbl2 {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            NoAction_3();
            a1_0();
        }
        psa_implementation = ap;
        default_action = NoAction_3();
    }
    apply {
        send_to_port();
        tbl.apply();
        tbl2.apply();
    }
}

control MyEC(inout EMPTY a, inout EMPTY b, in psa_egress_input_metadata_t c, inout psa_egress_output_metadata_t d) {
    apply {
    }
}

control MyID(packet_out buffer, out EMPTY a, out EMPTY b, out EMPTY c, inout headers_t hdr, in EMPTY e, in psa_ingress_output_metadata_t f) {
    apply {
        buffer.emit<ethernet_t>(hdr.ethernet);
        buffer.emit<ipv4_base_t>(hdr.ipv4_base);
    }
}

control MyED(packet_out buffer, out EMPTY a, out EMPTY b, inout EMPTY c, in EMPTY d, in psa_egress_output_metadata_t e, in psa_egress_deparser_input_metadata_t f) {
    apply {
    }
}

IngressPipeline<headers_t, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(MyIP(), MyIC(), MyID()) ip;

EgressPipeline<EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(MyEP(), MyEC(), MyED()) ep;

PSA_Switch<headers_t, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;

