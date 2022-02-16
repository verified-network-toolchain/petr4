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
    bit<48> src_addr;
}

struct Headers {
    ethernet_t eth_hdr;
}

control ingress(inout Headers h) {
    @name("ingress.tmp") bit<16> tmp;
    @name("ingress.tmp_bool") bool tmp_bool_0;
    @name("ingress.val_undefined") bool val_undefined_0;
    @name("ingress.tmp") bit<16> tmp_4;
    @name(".do_global_action") action do_global_action_0() {
        tmp = tmp * 16w0;
    }
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("ingress.do_action") action do_action() {
        tmp_4 = tmp_4 * (tmp_bool_0 ? 16w0 : 16w1);
        tmp_bool_0 = val_undefined_0;
    }
    @name("ingress.simple_table") table simple_table_0 {
        key = {
            h.eth_hdr.src_addr: exact @name("h.eth_hdr.src_addr") ;
        }
        actions = {
            do_action();
            do_global_action_0();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        tmp_bool_0 = false;
        simple_table_0.apply();
    }
}

control c<H>(inout H h);
package top<H>(c<H> _c);
top<Headers>(ingress()) main;

