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

parser p(out bit<32> b) {
    @name("a") bit<32> a_0;
    bit<32> tmp;
    bit<32> tmp_0;
    bit<32> tmp_1;
    state start {
        a_0 = 32w1;
        transition start_0;
    }
    state start_0 {
        {
            if (a_0 == 32w0) {
                tmp = 32w2;
            } else {
                tmp = 32w3;
            }
            b = tmp;
        }
        b = b + 32w1;
        {
            if (a_0 > 32w0) {
                if (a_0 > 32w1) {
                    tmp_1 = b + 32w1;
                } else {
                    tmp_1 = b + 32w2;
                }
                tmp_0 = tmp_1;
            } else {
                tmp_0 = b + 32w3;
            }
            b = tmp_0;
        }
        transition accept;
    }
}

parser proto(out bit<32> b);
package top(proto _p);
top(p()) main;

