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
    bit<8> tmp;
    state start {
        tmp = hdr.f1;
        transition foo_start;
    }
    state foo_start {
        hdr.f1 = tmp >> 2;
        transition start_0;
    }
    state start_0 {
        transition foo_start_0;
    }
    state foo_start_0 {
        hdr.f2 = 8w5 >> 2;
        transition start_1;
    }
    state start_1 {
        transition accept;
    }
}

parser p<T>(out T h);
package top<T>(p<T> p);
top<h1_t>(parserImpl()) main;

