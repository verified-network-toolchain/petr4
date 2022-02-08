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
    E() e;
    apply {
        if (s.h.isValid()) {
            s.h.data3 = 0;
        }
        if (s.h.data2 == 0) {
            s.h.data1 = e.get(s.h.data2);
        }
    }
}

parser proto(packet_in p, out Header h);
control cproto<T>(inout T v);
package top(cproto<_> _c);
top(c()) main;

