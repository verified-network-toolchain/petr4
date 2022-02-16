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

parser p(out bit<32> z) {
    @name("b") bool b;
    @name("x") bit<32> x;
    @name("w") bit<32> w;
    state start {
        b = true;
        transition select(b) {
            true: start_true;
            false: start_false;
        }
    }
    state start_true {
        x = 32w1;
        z = x;
        transition start_join;
    }
    state start_false {
        w = 32w2;
        z = w;
        transition start_join;
    }
    state start_join {
        transition accept;
    }
}

parser _p(out bit<32> z);
package top(_p _pa);
top(p()) main;

