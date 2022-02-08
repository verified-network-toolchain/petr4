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
    @name("x") bit<32> x_0;
    @name("tmp") H tmp_0;
    bit<32> tmp;
    state start {
        tmp_0.setInvalid();
        p.extract<H>(tmp_0);
        transition select(tmp_0.field) {
            32w0: n1;
            default: n2;
        }
    }
    state n1 {
        x_0 = 32w1;
        transition n3;
    }
    state n2 {
        x_0 = 32w2;
        transition n3;
    }
    state n3 {
        x_0 = x_0 + 32w4294967295;
        {
            tmp = x_0;
            p.extract<H>(h[tmp]);
        }
        transition accept;
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top<H[2]>(P()) main;

