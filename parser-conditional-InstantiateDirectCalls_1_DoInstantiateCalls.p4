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

parser p(out bit<32> b) {
    bit<32> a = 1;
    state start {
        b = (a == 0 ? 32w2 : 3);
        b = b + 1;
        b = (a > 0 ? (a > 1 ? b + 1 : b + 2) : b + 3);
        transition accept;
    }
}

parser proto(out bit<32> b);
package top(proto _p);
top(p()) main;

