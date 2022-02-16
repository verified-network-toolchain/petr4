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

parser Parser();
package Package(Parser p1, Parser p2);
parser Inside() {
    state start {
        transition accept;
    }
}

parser Parser1_0() {
    state start {
        transition Inside_start;
    }
    state Inside_start {
        transition start_0;
    }
    state start_0 {
        transition accept;
    }
}

parser Parser2_0() {
    state start {
        transition Inside_start_0;
    }
    state Inside_start_0 {
        transition start_1;
    }
    state start_1 {
        transition accept;
    }
}

Package(Parser1_0(), Parser2_0()) main;

