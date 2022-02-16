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

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

control c(inout bit<16> x) {
    action incx() {
        x = x + 1;
    }
    action nop() {
    }
    table x {
        actions = {
            incx();
            nop();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        x.apply();
    }
}

control C(inout bit<16> x);
package top(C _c);
top(c()) main;

