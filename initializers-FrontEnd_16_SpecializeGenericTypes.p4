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

extern Fake {
    Fake();
    void call(in bit<32> data);
}

parser P() {
    bit<32> x = (bit<32>)32w0;
    Fake() fake;
    state start {
        fake.call(x);
        transition accept;
    }
}

control C() {
    bit<32> x = (bit<32>)32w0;
    bit<32> y = x + 32w1;
    Fake() fake;
    apply {
        fake.call(y);
    }
}

parser SimpleParser();
control SimpleControl();
package top(SimpleParser prs, SimpleControl ctrl);
top(P(), C()) main;

