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

header hdr {
    bit<32> a;
    bit<32> b;
    bit<8>  c;
}

control ingress(inout hdr h) {
    apply {
        h.a[7:0] = h.c;
        h.a[15:8] = h.c + h.c;
    }
}

control c(inout hdr h);
package top(c _c);
top(ingress()) main;

