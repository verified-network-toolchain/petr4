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

header header_h {
    bit<8> field;
}

struct struct_t {
    header_h[4] stack;
}

parser Parser(inout struct_t input) {
    state start {
        input.stack[input.stack.lastIndex].field = 8w1;
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

parser MyParser<S>(inout S input);
package MyPackage<S>(MyParser<S> p);
MyPackage<struct_t>(Parser()) main;

