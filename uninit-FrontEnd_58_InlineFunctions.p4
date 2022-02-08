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

header Header {
    bit<32> data1;
    bit<32> data2;
    bit<32> data3;
}

extern void func(in Header h);
extern bit<32> g(inout bit<32> v, in bit<32> w);
parser p1(packet_in p, out Header h) {
    @name("stack") Header[2] stack;
    @name("tmp") bit<32> tmp_2;
    @name("tmp_0") bit<32> tmp_3;
    @name("tmp_1") bit<32> tmp_4;
    state start {
        stack[0].setInvalid();
        stack[1].setInvalid();
        h.data1 = 32w0;
        func(h);
        tmp_2 = h.data2;
        tmp_3 = h.data2;
        tmp_4 = g(h.data2, tmp_3);
        g(tmp_2, tmp_4);
        h.data2 = h.data3 + 32w1;
        transition select(h.isValid()) {
            true: next1;
            false: next2;
        }
    }
    state next1 {
        transition next3;
    }
    state next2 {
        transition next3;
    }
    state next3 {
        transition accept;
    }
}

control c(out bit<32> v) {
    @name("e") bit<32> e;
    @name("a1") action a1_0() {
    }
    @name("a1") action a1_2() {
    }
    @name("a2") action a2_0() {
    }
    @name("t") table t {
        actions = {
            a1_0();
            a2_0();
        }
        default_action = a1_0();
    }
    apply {
        if (e > 32w0) {
            e = 32w1;
        } else {
            ;
        }
        e = e + 32w1;
        switch (t.apply().action_run) {
            a1_0: {
            }
            default: {
            }
        }
        if (e > 32w0) {
            t.apply();
        } else {
            a1_2();
        }
    }
}

parser proto(packet_in p, out Header h);
control cproto(out bit<32> v);
package top(proto _p, cproto _c);
top(p1(), c()) main;

