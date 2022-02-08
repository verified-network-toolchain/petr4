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

control C(inout bit<2> x);
package S(C c);
control MyC(inout bit<2> x) {
    action a() {
    }
    action b() {
    }
    table t {
        key = {
            x: exact;
        }
        actions = {
            a();
            b();
            @defaultonly NoAction();
        }
        const entries = {
                        0 : a();
                        1 : b();
                        2 : a();
                        3 : b();
        }
        default_action = NoAction();
    }
    apply {
        t.apply();
    }
}

S(MyC()) main;

