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
    bit<48> src_addr;
}

struct Headers {
    ethernet_t eth_hdr;
}

action do_global_action(in bool make_zero, out bool val_undefined) {
    bit<16> tmp;
    tmp = tmp * (make_zero ? 16w0 : 16w1);
}
control ingress(inout Headers h) {
    bool filler_bool = true;
    bool tmp_bool = false;
    action do_action() {
        do_global_action(tmp_bool, tmp_bool);
    }
    table simple_table {
        key = {
            h.eth_hdr.src_addr: exact @name("h.eth_hdr.src_addr") ;
        }
        actions = {
            do_action();
            do_global_action(true, filler_bool);
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        simple_table.apply();
    }
}

control c<H>(inout H h);
package top<H>(c<H> _c);
top<Headers>(ingress()) main;

