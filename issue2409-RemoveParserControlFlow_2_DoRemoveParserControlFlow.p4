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
    @name("b") bool b_0;
    @name("x") bit<32> x_0;
    @name("w") bit<32> w_0;
    state start {
        b_0 = true;
        transition select(b_0) {
            true: start_true;
            false: start_false;
        }
    }
    state start_true {
        x_0 = (bit<32>)32w1;
        z = x_0;
        transition start_join;
    }
    state start_false {
        w_0 = (bit<32>)32w2;
        z = w_0;
        transition start_join;
    }
    state start_join {
        transition accept;
    }
}

parser _p(out bit<32> z);
package top(_p _pa);
top(p()) main;

