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
    @name("a") bit<32> a;
    @name("tmp") bit<32> tmp_2;
    @name("tmp_0") bit<32> tmp_3;
    @name("tmp_1") bit<32> tmp_4;
    state start {
        a = 32w1;
        transition start_0;
    }
    state start_0 {
        transition select(a == 32w0) {
            true: start_0_true;
            false: start_0_false;
        }
    }
    state start_0_true {
        tmp_2 = 32w2;
        transition start_0_join;
    }
    state start_0_false {
        tmp_2 = 32w3;
        transition start_0_join;
    }
    state start_0_join {
        b = tmp_2;
        b = b + 32w1;
        transition select(a > 32w0) {
            true: start_0_true_0;
            false: start_0_false_0;
        }
    }
    state start_0_true_0 {
        transition select(a > 32w1) {
            true: start_0_true_0_true;
            false: start_0_true_0_false;
        }
    }
    state start_0_true_0_true {
        tmp_4 = b + 32w1;
        transition start_0_true_0_join;
    }
    state start_0_true_0_false {
        tmp_4 = b + 32w2;
        transition start_0_true_0_join;
    }
    state start_0_true_0_join {
        tmp_3 = tmp_4;
        transition start_0_join_0;
    }
    state start_0_false_0 {
        tmp_3 = b + 32w3;
        transition start_0_join_0;
    }
    state start_0_join_0 {
        b = tmp_3;
        transition accept;
    }
}

parser proto(out bit<32> b);
package top(proto _p);
top(p()) main;

