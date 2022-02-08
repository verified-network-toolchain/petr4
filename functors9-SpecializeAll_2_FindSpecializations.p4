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

extern e<T> {
    e();
    T get();
}

parser p1<T>(in T a) {
    @name("w") T w_0;
    @name("ei") e<T>() ei_0;
    state start {
        ei_0.get();
        transition accept;
    }
}

parser simple(in bit<2> a);
package m(simple n);
m(p1<bit<2>>()) main;

