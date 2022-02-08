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

@noWarn("unused") @name(".NoAction") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

control C(inout bit<2> x);
package S(C c);
control MyC(inout bit<2> x) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("a") action a_0() {
    }
    @name("a") action a() {
    }
    @name("b") action b_0() {
    }
    @name("b") action b() {
    }
    @name("t") table t_0 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            a();
            b();
            @defaultonly NoAction_1();
        }
        const entries = {
                        2w0 : a();
                        2w1 : b();
                        2w2 : a();
                        2w3 : b();
        }
        default_action = NoAction_1();
    }
    apply {
        t_0.apply();
    }
}

S(MyC()) main;

