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

parser p(out bit<32> z) {
    state start {
        bool b = true;
        if (b) {
            bit<32> x = 1;
            z = x;
        } else {
            bit<32> w = 2;
            z = w;
        }
        transition accept;
    }
}

parser _p(out bit<32> z);
package top(_p _pa);
top(p()) main;

