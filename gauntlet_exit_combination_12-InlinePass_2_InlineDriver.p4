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
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    @name("do_action") action do_action_0() {
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
            do_action_0();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        switch (simple_table_0.apply().action_run) {
            do_action_0: {
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

