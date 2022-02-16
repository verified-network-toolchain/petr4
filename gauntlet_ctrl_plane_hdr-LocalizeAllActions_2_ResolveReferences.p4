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

@noWarn("unused") @name(".NoAction") action NoAction() {
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
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("do_action") action do_action_0(@name("ctrl_hdr") ethernet_t ctrl_hdr_0) {
        h.eth_hdr.dst_addr = ctrl_hdr_0.dst_addr;
    }
    @name("simple_table") table simple_table_0 {
        key = {
            h.eth_hdr.eth_type: exact @name("key") ;
        }
        actions = {
            do_action_0();
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    apply {
        simple_table_0.apply();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

