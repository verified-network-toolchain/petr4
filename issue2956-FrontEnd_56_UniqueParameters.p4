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
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("simple_assign") action simple_assign_0() {
        h.eth_hdr.eth_type = 16w1;
    }
    @name("simple_assign") action simple_assign_3() {
        h.eth_hdr.eth_type = 16w1;
    }
    @name("simple_assign") action simple_assign_4() {
        h.eth_hdr.eth_type = 16w1;
    }
    @name("dummy_table") table dummy_table {
        key = {
            h.eth_hdr.src_addr: exact @name("key") ;
        }
        actions = {
            NoAction_0();
            simple_assign_0();
        }
        default_action = NoAction_0();
    }
    apply {
        switch (dummy_table.apply().action_run) {
            simple_assign_0: {
                simple_assign_3();
            }
            NoAction_0: {
            }
        }
        simple_assign_4();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

