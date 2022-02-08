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
    @name("tmp") bit<16> tmp_0;
    tmp_0 = tmp_0 * (make_zero ? 16w0 : 16w1);
}
control ingress(inout Headers h) {
    @name("filler_bool") bool filler_bool_0;
    @name("tmp_bool") bool tmp_bool_0;
    bool tmp;
    @name("do_action") action do_action_0() {
        tmp = tmp_bool_0;
        do_global_action(tmp, tmp_bool_0);
    }
    @name("simple_table") table simple_table_0 {
        key = {
            h.eth_hdr.src_addr: exact @name("h.eth_hdr.src_addr") ;
        }
        actions = {
            do_action_0();
            do_global_action(true, filler_bool_0);
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        filler_bool_0 = true;
        tmp_bool_0 = false;
        simple_table_0.apply();
    }
}

control c<H>(inout H h);
package top<H>(c<H> _c);
top<Headers>(ingress()) main;

