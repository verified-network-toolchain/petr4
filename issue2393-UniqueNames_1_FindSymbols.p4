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
    @name("tmp") bit<16> tmp_1;
    @name("filler_bool") bool filler_bool;
    @name("tmp_bool") bool tmp_bool;
    @name("tmp") bool tmp_2;
    @name("make_zero") bool make_zero_1;
    @name("val_undefined") bool val_undefined_1;
    @name("tmp") bit<16> tmp_3;
    @name("make_zero") bool make_zero;
    @name("val_undefined") bool val_undefined;
    @name(".do_global_action") action do_global_action() {
        make_zero = true;
        tmp_1 = tmp_1 * (make_zero ? 16w0 : 16w1);
        filler_bool = val_undefined;
    }
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("do_action") action do_action_0() {
        tmp_2 = tmp_bool;
        make_zero_1 = tmp_2;
        tmp_3 = tmp_3 * (make_zero_1 ? 16w0 : 16w1);
        tmp_bool = val_undefined_1;
    }
    @name("simple_table") table simple_table {
        key = {
            h.eth_hdr.src_addr: exact @name("h.eth_hdr.src_addr") ;
        }
        actions = {
            do_action_0();
            do_global_action();
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    apply {
        tmp_bool = false;
        simple_table.apply();
    }
}

control c<H>(inout H h);
package top<H>(c<H> _c);
top<Headers>(ingress()) main;

