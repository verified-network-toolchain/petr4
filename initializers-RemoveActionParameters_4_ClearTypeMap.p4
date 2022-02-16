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

extern Fake {
    Fake();
    void call(in bit<32> data);
}

parser P() {
    @name("x") bit<32> x;
    @name("fake") Fake() fake;
    state start {
        x = 32w0;
        transition start_0;
    }
    state start_0 {
        fake.call(x);
        transition accept;
    }
}

control C() {
    @name("x") bit<32> x_2;
    @name("y") bit<32> y;
    @name("fake") Fake() fake_2;
    apply {
        x_2 = 32w0;
        y = x_2 + 32w1;
        fake_2.call(y);
    }
}

parser SimpleParser();
control SimpleControl();
package top(SimpleParser prs, SimpleControl ctrl);
top(P(), C()) main;

