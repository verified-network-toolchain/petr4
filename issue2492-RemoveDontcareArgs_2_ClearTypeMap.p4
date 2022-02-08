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

header data_t {
    bit<16> h1;
}

struct headers {
    data_t data;
}

control ingress(inout headers hdr) {
    apply {
        hdr.data.h1 = 16w1;
    }
}

control ctr<H>(inout H hdr);
package top<H1, H2, H3>(ctr<H1> ctrl1, @optional ctr<H2> ctrl2, @optional ctr<H3> ctrl3);
top<headers, _, _>(ingress()) main;

