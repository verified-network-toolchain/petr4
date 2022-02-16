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

parser simple(out bit<2> z);
package m(simple n);
parser p1_0(out bit<2> z1) {
    state start {
        z1 = 2w0;
        transition accept;
    }
}

parser p1_1(out bit<2> z1) {
    state start {
        z1 = 2w1;
        transition accept;
    }
}

parser p1_2(out bit<2> z1) {
    state start {
        z1 = 2w2;
        transition accept;
    }
}

parser p2_0(out bit<2> z2) {
    @name("x1") bit<2> x1_0;
    @name("x2") bit<2> x2_0;
    @name("x3") bit<2> x3_0;
    @name("p1a") p1_0() p1a_0;
    @name("p1b") p1_1() p1b_0;
    @name("p1c") p1_2() p1c_0;
    state start {
        transition p1_0_start;
    }
    state p1_0_start {
        x1_0 = 2w0;
        transition start_0;
    }
    state start_0 {
        transition p1_1_start;
    }
    state p1_1_start {
        x2_0 = 2w1;
        transition start_1;
    }
    state start_1 {
        transition p1_2_start;
    }
    state p1_2_start {
        x3_0 = 2w2;
        transition start_2;
    }
    state start_2 {
        z2 = 2w3 | x1_0 | x2_0 | x3_0;
        transition accept;
    }
}

m(p2_0()) main;

