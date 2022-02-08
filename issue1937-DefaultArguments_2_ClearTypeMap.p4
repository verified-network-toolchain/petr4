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

header h1_t {
    bit<8> f1;
    bit<8> f2;
}

parser foo(out bit<8> x, in bit<8> y=5) {
    state start {
        x = y >> 2;
        transition accept;
    }
}

parser parserImpl(out h1_t hdr) {
    @name("foo") foo() foo_inst;
    @name("foo") foo() foo_inst_0;
    state start {
        foo_inst.apply(hdr.f1, hdr.f1);
        foo_inst_0.apply(x = hdr.f2, y = 5);
        transition accept;
    }
}

parser p<T>(out T h);
package top<T>(p<T> p);
top<h1_t>(parserImpl()) main;

