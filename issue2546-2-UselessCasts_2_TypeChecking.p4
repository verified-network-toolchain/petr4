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

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

control ingress(inout bit<32> b) {
    table t0 {
        key = {
            b: exact @name("b") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    table t1 {
        key = {
            (t0.apply().hit ? 8w1 : 8w2): exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    table t2 {
        key = {
            (t1.apply().hit ? 8w3 : 8w4): exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        if (t2.apply().hit) {
            b = 32w1;
        }
    }
}

control Ingress(inout bit<32> b);
package top(Ingress ig);
top(ingress()) main;

