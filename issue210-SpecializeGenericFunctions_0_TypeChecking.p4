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

control Ing(out bit<32> a) {
    bool b;
    action cond() {
        if (b) {
            a = (bit<32>)32w5;
        } else {
            a = (bit<32>)32w10;
        }
    }
    apply {
        b = true;
        cond();
    }
}

control s(out bit<32> a);
package top(s e);
top(Ing()) main;

