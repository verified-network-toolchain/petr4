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

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
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
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    table simple_table_1 {
        key = {
            48w1: exact @name("KOXpQP") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    table simple_table_2 {
        key = {
            (simple_table_1.apply().hit ? 8w1 : 8w2): exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        if (simple_table_2.apply().hit) {
            h.eth_hdr.dst_addr = (bit<48>)48w1;
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

