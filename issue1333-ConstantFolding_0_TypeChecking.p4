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

extern void f(bit<32> a=0, bit<32> b);
extern E {
    E(bit<32> x=0);
    void f(in bit<16> z=2);
}

control c()(bit<32> binit=4) {
    @name("e") E(x = 32w0) e_0;
    apply {
        f(a = 32w0, b = binit);
        e_0.f(z = 16w2);
    }
}

control ctrl();
package top(ctrl _c);
top(c(binit = 32w4)) main;

