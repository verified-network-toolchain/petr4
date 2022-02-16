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
    D() d;
    F() f;
    C(d) c0;
    C(f) c1;
    apply {
        c0.apply(b);
        c1.apply(b);
    }
}

package top(E _e);
top(Ingress()) main;

