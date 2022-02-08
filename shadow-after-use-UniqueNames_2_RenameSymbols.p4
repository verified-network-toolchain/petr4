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

control c(inout bit<16> x) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("incx") action incx() {
        x = x + 16w1;
    }
    @name("nop") action nop() {
    }
    @name("x") table x_0 {
        actions = {
            incx();
            nop();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        x_0.apply();
    }
}

control C(inout bit<16> x);
package top(C _c);
top(c()) main;

