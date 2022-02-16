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

parser par(out bool b) {
    @name("x") bit<32> x;
    state start {
        transition adder_0_start;
    }
    state adder_0_start {
        x = 32w0 + 32w6;
        transition start_0;
    }
    state start_0 {
        b = x == 32w0;
        transition accept;
    }
}

control c(out bool b) {
    @name("xv") bit<16> xv;
    @name("x_1") bit<16> x_3;
    @name("b_0") bool b_2;
    @name("x_2") bit<16> x_4;
    @name("b_1") bool b_3;
    @name("a") action a_0(@name("bi") in bit<16> bi_0, @name("mb") out bit<16> mb_0) {
        mb_0 = -bi_0;
    }
    @name("a") action a_2(@name("bi") in bit<16> bi_0, @name("mb") out bit<16> mb_0) {
        mb_0 = -bi_0;
    }
    apply {
        a_0(bi_0 = 16w3, mb_0 = xv);
        a_2(mb_0 = xv, bi_0 = 16w0);
        {
            x_3 = xv;
            b_2 = x_3 == 16w0;
            b = b_2;
            xv = x_3;
        }
        {
            x_4 = xv;
            b_3 = x_4 == 16w1;
            xv = x_4;
            b = b_3;
        }
        xv = 16w1;
        {
            x_3 = xv;
            b_2 = x_3 == 16w0;
            xv = x_3;
            b = b_2;
        }
        {
            x_4 = xv;
            b_3 = x_4 == 16w1;
            b = b_3;
            xv = x_4;
        }
    }
}

control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_e = c(), _p = par()) main;

