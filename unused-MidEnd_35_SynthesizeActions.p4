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

header Header {
    bit<32> data1;
    bit<32> data2;
    bit<32> data3;
}

struct S {
    Header h;
}

extern E {
    E();
    bit<32> get<T>(in T b);
}

control c(inout S s) {
    @name("c.e") E() e_0;
    @hidden action unused38() {
        s.h.data3 = 32w0;
    }
    @hidden action unused40() {
        s.h.data1 = e_0.get<bit<32>>(s.h.data2);
    }
    apply {
        if (s.h.isValid()) {
            unused38();
        }
        if (s.h.data2 == 32w0) {
            unused40();
        }
    }
}

control cproto<T>(inout T v);
package top(cproto<_> _c);
top(c()) main;

