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

extern void f(bit<32> a=0, bit<32> b);
extern E {
    E(bit<32> x=0);
    void f(in bit<16> z=2);
}

control c()(bit<32> binit=4) {
    E(x = 32w0) e;
    apply {
        f(a = 32w0, b = binit);
        e.f(z = (bit<16>)2);
    }
}

control ctrl();
package top(ctrl _c);
top(c(binit = 32w4)) main;

