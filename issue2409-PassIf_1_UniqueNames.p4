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
        @name("b") bool b_0 = true;
        if (b_0) {
            @name("x") bit<32> x_0 = (bit<32>)32w1;
            z = x_0;
        } else {
            @name("w") bit<32> w_0 = (bit<32>)32w2;
            z = w_0;
        }
        transition accept;
    }
}

parser _p(out bit<32> z);
package top(_p _pa);
top(p()) main;

