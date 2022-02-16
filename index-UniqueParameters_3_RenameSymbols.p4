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

header H {
    bit<32> field;
}

parser P(packet_in p, out H[2] h) {
    @name("x") bit<32> x;
    @name("tmp") H tmp_1;
    @name("tmp") bit<32> tmp_2;
    state start {
        tmp_1.setInvalid();
        p.extract<H>(tmp_1);
        transition select(tmp_1.field) {
            32w0: n1;
            default: n2;
        }
    }
    state n1 {
        x = 32w1;
        transition n3;
    }
    state n2 {
        x = 32w2;
        transition n3;
    }
    state n3 {
        x = x + 32w4294967295;
        tmp_2 = x;
        p.extract<H>(h[tmp_2]);
        transition accept;
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top<H[2]>(P()) main;

