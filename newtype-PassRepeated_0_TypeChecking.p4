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

typedef bit<32> B32;
type bit<32> N32;
struct S {
    B32 b;
    N32 n;
}

header H {
    N32 field;
}

control c(out B32 x) {
    @name("k") N32 k;
    @name("b") bit<32> b_1;
    @name("n") N32 n_1;
    @name("n1") N32 n1;
    @name("s") S s;
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("t") table t {
        actions = {
            NoAction_0();
        }
        key = {
            k: exact @name("k") ;
        }
        default_action = NoAction_0();
    }
    apply {
        b_1 = 32w0;
        n_1 = (N32)b_1;
        k = n_1;
        x = (B32)n_1;
        n1 = (N32)32w1;
        if (n_1 == n1) {
            x = 32w2;
        }
        s.b = b_1;
        s.n = n_1;
        t.apply();
        if (s.b == (B32)s.n) {
            x = 32w3;
        }
    }
}

control e(out B32 x);
package top(e _e);
top(c()) main;

