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

parser adder(in bit<32> y, out bit<32> x)(bit<32> add, bool ignore) {
    state start {
        x = y + add;
        transition accept;
    }
}

parser par(out bool b) {
    @name("x") bit<32> x_0;
    @name("p") adder(ignore = false, add = 32w6) p_0;
    state start {
        p_0.apply(x = x_0, y = 32w0);
        b = x_0 == 32w0;
        transition accept;
    }
}

control comp(inout bit<16> x, out bool b)(bit<16> compare, bit<2> ignore) {
    apply {
        b = x == compare;
    }
}

control c(out bool b) {
    @name("xv") bit<16> xv_0;
    @name("c0") comp(ignore = 2w1, compare = 16w0) c0_0;
    @name("c1") comp(ignore = 2w2, compare = 16w1) c1_0;
    @name("a") action a_0(in bit<16> bi, out bit<16> mb) {
        mb = -bi;
    }
    apply {
        xv_0 = 16w0;
        a_0(bi = 16w3, mb = xv_0);
        a_0(mb = xv_0, bi = 16w0);
        c0_0.apply(b = b, x = xv_0);
        c1_0.apply(xv_0, b);
        xv_0 = 16w1;
        c0_0.apply(x = xv_0, b = b);
        c1_0.apply(b = b, x = xv_0);
    }
}

control ce(out bool b);
parser pe(out bool b);
package top(pe _p, ce _e, @optional ce _e1);
top(_e = c(), _p = par()) main;

