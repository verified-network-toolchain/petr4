/petr4/ci-test/type-checking/testdata/p4_16_samples/psa-example-dpdk-varbit-bmv2.p4
\n
#include <core.p4>
#include <psa.p4>

typedef bit<48>  EthernetAddress;

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
    ethernet_t ethernet;
    ipv4_base_t             ipv4_base;
    ipv4_option_timestamp_t ipv4_option_timestamp;
}

struct EMPTY { };

parser MyIP(
    packet_in packet,
    out headers_t hdr,
    inout EMPTY b,
    in psa_ingress_parser_input_metadata_t c,
    in EMPTY d,
    in EMPTY e) {

    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        packet.extract(hdr.ipv4_base);
        transition select(hdr.ipv4_base.ihl) {
            4w0x5: accept;
            default: parse_ipv4_options;
        }
    }
    state parse_ipv4_option_timestamp {
        bit<16> tmp16 = packet.lookahead<bit<16>>();
        bit<8> tmp_len = tmp16[7:0];
        packet.extract(hdr.ipv4_option_timestamp, (bit<32>)tmp_len * 8 - 16);
        transition accept;
    }
    state parse_ipv4_options {
        transition select(packet.lookahead<bit<8>>()) {
            8w0x44 &&& 8w0xff: parse_ipv4_option_timestamp;
            default : accept;
        }
    }
}

parser MyEP(
    packet_in buffer,
    out EMPTY a,
    inout EMPTY b,
    in psa_egress_parser_input_metadata_t c,
    in EMPTY d,
    in EMPTY e,
    in EMPTY f) {
    state start {
        transition accept;
    }
}

control MyIC(
    inout headers_t hdr,
    inout EMPTY b,
    in psa_ingress_input_metadata_t c,
    inout psa_ingress_output_metadata_t d) {

    ActionProfile(1024) ap;
    action a1(bit<48> param) { hdr.ethernet.dstAddr = param; }
    action a2(bit<16> param) { hdr.ethernet.etherType = param; }
    table tbl {
        key = {
            hdr.ethernet.srcAddr : exact;
        }
        actions = { NoAction; a2; }
        psa_implementation = ap;
    }
    table tbl2 {
        key = {
            hdr.ethernet.srcAddr : exact;
        }
        actions = { NoAction; a1; }
        psa_implementation = ap;
    }
    apply {
        send_to_port(d, (PortId_t)0);
        tbl.apply();
        tbl2.apply();
    }
}

control MyEC(
    inout EMPTY a,
    inout EMPTY b,
    in psa_egress_input_metadata_t c,
    inout psa_egress_output_metadata_t d) {
    apply { }
}

control MyID(
    packet_out buffer,
    out EMPTY a,
    out EMPTY b,
    out EMPTY c,
    inout headers_t hdr,
    in EMPTY e,
    in psa_ingress_output_metadata_t f) {
    apply {
        buffer.emit(hdr.ethernet);
        buffer.emit(hdr.ipv4_base);
    }
}

control MyED(
    packet_out buffer,
    out EMPTY a,
    out EMPTY b,
    inout EMPTY c,
    in EMPTY d,
    in psa_egress_output_metadata_t e,
    in psa_egress_deparser_input_metadata_t f) {
    apply { }
}

IngressPipeline(MyIP(), MyIC(), MyID()) ip;
EgressPipeline(MyEP(), MyEC(), MyED()) ep;

PSA_Switch(
    ip,
    PacketReplicationEngine(),
    ep,
    BufferingQueueingEngine()) main;
************************\n******** petr4 type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/psa-example-dpdk-varbit-bmv2.p4:2:10: fatal error: psa.p4: No such file or directory
    2 | #include <psa.p4>
      |          ^~~~~~~~
compilation terminated.
error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused")
action NoAction() { 
}
match_kind {
  exact, ternary, lpm
}

************************\n******** p4c type checking result: ********\n************************\n
/usr/local/share/p4c/p4include/bmv2/psa.p4(546): [--Wwarn=unused] warning: 'W' is unused
extern Counter<W, S> {
               ^
/usr/local/share/p4c/p4include/bmv2/psa.p4(575): [--Wwarn=unused] warning: 'W' is unused
extern DirectCounter<W> {
                     ^
