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
    @name("x") bit<32> x_0;
    state start {
        transition adder_0_start;
    }
    state adder_0_start {
        x_0 = 32w0 + 32w6;
        transition start_0;
    }
    state start_0 {
        b = x_0 == 32w0;
        transition accept;
    }
}

control c(out bool b) {
    @name("xv") bit<16> xv_0;
    bit<16> x_1;
    bool b_0;
    bit<16> x_2;
    bool b_1;
    @name("a") action a(@name("bi") in bit<16> bi_0, @name("mb") out bit<16> mb_0) {
        mb_0 = -bi_0;
    }
    @name("a") action a_1(@name("bi") in bit<16> bi_0, @name("mb") out bit<16> mb_0) {
        mb_0 = -bi_0;
    }
    apply {
        a(bi_0 = 16w3, mb_0 = xv_0);
        a_1(mb_0 = xv_0, bi_0 = 16w0);
        {
            x_1 = xv_0;
            b_0 = x_1 == 16w0;
            b = b_0;
            xv_0 = x_1;
        }
        {
            x_2 = xv_0;
            b_1 = x_2 == 16w1;
            xv_0 = x_2;
            b = b_1;
        }
        xv_0 = 16w1;
        {
            x_1 = xv_0;
            b_0 = x_1 == 16w0;
            xv_0 = x_1;
            b = b_0;
        }
        {
            x_2 = xv_0;
            b_1 = x_2 == 16w1;
            b = b_1;
            xv_0 = x_2;
        }
    }
}

control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_e = c(), _p = par()) main;

