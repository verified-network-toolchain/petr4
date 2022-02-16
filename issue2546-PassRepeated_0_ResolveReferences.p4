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

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    @name("key_0") bit<8> key_1;
    @name("tmp") bool tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_3() {
    }
    @name("simple_table_1") table simple_table_1 {
        key = {
            48w1: exact @name("KOXpQP") ;
        }
        actions = {
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    @name("simple_table_2") table simple_table_2 {
        key = {
            key_1: exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction_3();
        }
        default_action = NoAction_3();
    }
    apply {
        tmp_1 = simple_table_1.apply().hit;
        if (tmp_1) {
            tmp_2 = 8w1;
        } else {
            tmp_2 = 8w2;
        }
        key_1 = tmp_2;
        if (simple_table_2.apply().hit) {
            h.eth_hdr.dst_addr = 48w1;
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

