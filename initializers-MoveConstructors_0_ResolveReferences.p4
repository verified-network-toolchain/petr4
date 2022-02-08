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
    @name("x") bit<32> x_0;
    @name("fake") Fake() fake_0;
    state start {
        x_0 = 32w0;
        transition start_0;
    }
    state start_0 {
        fake_0.call(x_0);
        transition accept;
    }
}

control C() {
    @name("x") bit<32> x_1;
    @name("y") bit<32> y_0;
    @name("fake") Fake() fake_1;
    apply {
        x_1 = 32w0;
        y_0 = x_1 + 32w1;
        fake_1.call(y_0);
    }
}

parser SimpleParser();
control SimpleControl();
package top(SimpleParser prs, SimpleControl ctrl);
top(P(), C()) main;

