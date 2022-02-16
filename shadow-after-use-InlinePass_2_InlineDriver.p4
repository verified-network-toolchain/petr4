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

control c(inout bit<16> x) {
    @name("incx") action incx_0() {
        x = x + 16w1;
    }
    @name("nop") action nop_0() {
    }
    @name("x") table x_0 {
        actions = {
            incx_0();
            nop_0();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        x_0.apply();
    }
}

control C(inout bit<16> x);
package top(C _c);
top(c()) main;

