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

control E(out bit<1> b);
control D(out bit<1> b) {
    apply {
        b = 1w1;
    }
}

control F(out bit<1> b) {
    apply {
        b = 1w0;
    }
}

control C(out bit<1> b)(E d) {
    apply {
        d.apply(b);
    }
}

control Ingress(out bit<1> b) {
    @name("d") D() d_0;
    @name("f") F() f_0;
    @name("c0") C(d_0) c0_0;
    @name("c1") C(f_0) c1_0;
    apply {
        c0_0.apply(b);
        c1_0.apply(b);
    }
}

package top(E _e);
top(Ingress()) main;

