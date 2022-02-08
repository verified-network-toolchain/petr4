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

parser p1(out bit<2> w)(bit<2> a) {
    state start {
        w = 2w2;
        transition accept;
    }
}

parser p2(out bit<2> w)(bit<2> a) {
    p1(a) x;
    state start {
        x.apply(w);
        transition accept;
    }
}

parser simple(out bit<2> w);
package m(simple n);
m(p2(2w1)) main;

