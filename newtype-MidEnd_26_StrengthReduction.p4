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
typedef bit<32> N32;
struct S {
    B32 b;
    N32 n;
}

header H {
    N32 field;
}

control c(out B32 x) {
    @name("c.k") N32 k_0;
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("c.t") table t_0 {
        actions = {
            NoAction_1();
        }
        key = {
            k_0: exact @name("k") ;
        }
        default_action = NoAction_1();
    }
    apply {
        k_0 = 32w0;
        x = 32w0;
        ;
        t_0.apply();
        x = 32w3;
    }
}

control e(out B32 x);
package top(e _e);
top(c()) main;

