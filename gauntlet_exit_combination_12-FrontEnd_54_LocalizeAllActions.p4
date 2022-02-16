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
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("do_action") action do_action() {
        if (h.eth_hdr.src_addr == 48w1) {
            exit;
        } else {
            h.eth_hdr.src_addr = 48w1;
        }
    }
    @name("simple_table") table simple_table_0 {
        key = {
            h.eth_hdr.eth_type: exact @name("tyhSfv") ;
        }
        actions = {
            do_action();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        switch (simple_table_0.apply().action_run) {
            do_action: {
                h.eth_hdr.eth_type = 16w0xdead;
            }
            default: {
            }
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

