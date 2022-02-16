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

control C(inout bit<2> x);
package S(C c);
control MyC(inout bit<2> x) {
    @name("a") action a_0() {
    }
    @name("b") action b_0() {
    }
    @name("t") table t_0 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            a_0();
            b_0();
            @defaultonly NoAction();
        }
        const entries = {
                        2w0 : a_0();
                        2w1 : b_0();
                        2w2 : a_0();
                        2w3 : b_0();
        }
        default_action = NoAction();
    }
    apply {
        t_0.apply();
    }
}

S(MyC()) main;

