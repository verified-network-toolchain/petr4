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

header H1 {
    bit<32> x;
}

header H2 {
    bit<16> y;
}

header_union U {
    H1 h1;
    H2 h2;
}

struct Headers {
    U u;
}

control c(in Headers h) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("a") action a() {
    }
    @name("t") table t_0 {
        key = {
            h.u.h1.x: exact @name("h.u.h1.x") ;
        }
        actions = {
            a();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        t_0.apply();
    }
}

control _c(in Headers h);
package top(_c c);
top(c()) main;

