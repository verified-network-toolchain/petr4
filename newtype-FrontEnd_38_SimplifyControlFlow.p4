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

@noWarn("unused") action NoAction() {
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

type N32 NN32;
control c(out B32 x) {
    @name("k") N32 k_0;
    @name("nn") NN32 nn_0;
    @name("b") bit<32> b_0;
    @name("n") N32 n_0;
    @name("n1") N32 n1_0;
    @name("s") S s_0;
    @name("t") table t_0 {
        actions = {
            NoAction();
        }
        key = {
            k_0: exact @name("k") ;
        }
        default_action = NoAction();
    }
    apply {
        b_0 = 32w0;
        n_0 = (N32)32w1;
        n_0 = (N32)b_0;
        nn_0 = (NN32)n_0;
        k_0 = n_0;
        x = (B32)n_0;
        n1_0 = (N32)32w1;
        if (n_0 == n1_0) {
            x = 32w2;
        }
        s_0.b = b_0;
        s_0.n = n_0;
        t_0.apply();
        if (s_0.b == (B32)s_0.n) {
            x = 32w3;
        }
    }
}

control e(out B32 x);
package top(e _e);
top(c()) main;

