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
@noWarn("uninitialized_use") parser p1(packet_in p, out Header h) {
    @name("stack") Header[2] stack_0;
    @name("b") bool b_0;
    @name("c") bool c_0;
    @name("d") bool d_0;
    @noWarn("invalid_header") @noWarn("ordering") state start {
        stack_0[0].setInvalid();
        stack_0[1].setInvalid();
        h.data1 = 32w0;
        func(h);
        g(h.data2, g(h.data2, h.data2));
        transition next;
    }
    @noWarn("invalid_header") state next {
        h.data2 = h.data3 + 32w1;
        stack_0[0] = stack_0[1];
        b_0 = stack_0[1].isValid();
        transition select(h.isValid()) {
            true: next1;
            false: next2;
        }
    }
    state next1 {
        d_0 = false;
        transition next3;
    }
    state next2 {
        c_0 = true;
        d_0 = c_0;
        transition next3;
    }
    state next3 {
        c_0 = !c_0;
        d_0 = !d_0;
        transition accept;
    }
}

control c(out bit<32> v) {
    @name("b") bit<32> b_1;
    @name("d") bit<32> d_1;
    @name("setByAction") bit<32> setByAction_0;
    @name("e") bit<32> e_0;
    @name("f") bit<32> f_0;
    @name("touched") bool touched_0;
    @name("a1") action a1_0() {
        setByAction_0 = 32w1;
    }
    @name("a2") action a2_0() {
        setByAction_0 = 32w1;
    }
    @name("t") table t_0 {
        actions = {
            a1_0();
            a2_0();
        }
        default_action = a1_0();
    }
    apply @noWarn("uninitialized_use") {
        d_1 = 32w1;
        b_1 = b_1 + 32w1;
        d_1 = d_1 + 32w1;
        if (e_0 > 32w0) {
            e_0 = 32w1;
            f_0 = 32w2;
        } else {
            f_0 = 32w3;
        }
        e_0 = e_0 + 32w1;
        switch (t_0.apply().action_run) {
            a1_0: {
                touched_0 = true;
            }
            default: {
            }
        }
        touched_0 = !touched_0;
        if (e_0 > 32w0) {
            t_0.apply();
        } else {
            a1_0();
        }
        setByAction_0 = setByAction_0 + 32w1;
    }
}

parser proto(packet_in p, out Header h);
control cproto(out bit<32> v);
package top(proto _p, cproto _c);
top(p1(), c()) main;

