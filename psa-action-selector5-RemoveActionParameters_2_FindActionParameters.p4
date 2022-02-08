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

struct EMPTY {
}

typedef bit<48> EthernetAddress;
struct user_meta_t {
    bit<16> data;
}

header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

struct headers_t {
    ethernet_t ethernet;
}

parser MyIP(packet_in buffer, out headers_t hdr, inout user_meta_t b, in psa_ingress_parser_input_metadata_t c, in EMPTY d, in EMPTY e) {
    state start {
        buffer.extract<ethernet_t>(hdr.ethernet);
        transition accept;
    }
}

parser MyEP(packet_in buffer, out EMPTY a, inout EMPTY b, in psa_egress_parser_input_metadata_t c, in EMPTY d, in EMPTY e, in EMPTY f) {
    state start {
        transition accept;
    }
}

control MyIC(inout headers_t hdr, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_4() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_5() {
    }
    @name("as") ActionSelector(PSA_HashAlgorithm_t.CRC32, 32w1024, 32w16) as;
    @name(".a1") action a1_0(@name("param") bit<48> param) {
        hdr.ethernet.dstAddr = param;
    }
    @name(".a2") action a2_0(@name("param") bit<16> param_2) {
        hdr.ethernet.etherType = param_2;
    }
    @name("tbl") table tbl {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
            b.data              : selector @name("b.data") ;
        }
        actions = {
            NoAction_0();
            a1_0();
            a2_0();
        }
        psa_implementation = as;
        default_action = NoAction_0();
    }
    @name("foo") table foo {
        actions = {
            NoAction_4();
        }
        default_action = NoAction_4();
    }
    @name("bar") table bar {
        actions = {
            NoAction_5();
        }
        default_action = NoAction_5();
    }
    apply {
        switch (tbl.apply().action_run) {
            a1_0: {
                foo.apply();
            }
            a2_0: {
                bar.apply();
            }
            default: {
            }
        }
    }
}

control MyEC(inout EMPTY a, inout EMPTY b, in psa_egress_input_metadata_t c, inout psa_egress_output_metadata_t d) {
    apply {
    }
}

control MyID(packet_out buffer, out EMPTY a, out EMPTY b, out EMPTY c, inout headers_t hdr, in user_meta_t e, in psa_ingress_output_metadata_t f) {
    apply {
        buffer.emit<ethernet_t>(hdr.ethernet);
    }
}

control MyED(packet_out buffer, out EMPTY a, out EMPTY b, inout EMPTY c, in EMPTY d, in psa_egress_output_metadata_t e, in psa_egress_deparser_input_metadata_t f) {
    apply {
    }
}

IngressPipeline<headers_t, user_meta_t, EMPTY, EMPTY, EMPTY, EMPTY>(MyIP(), MyIC(), MyID()) ip;

EgressPipeline<EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(MyEP(), MyEC(), MyED()) ep;

PSA_Switch<headers_t, user_meta_t, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;

