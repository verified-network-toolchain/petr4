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

control ingress(inout bit<32> b) {
    @name("t0") table t0_0 {
        key = {
            b: exact @name("b") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    @name("t1") table t1_0 {
        key = {
            (t0_0.apply().hit ? 8w1 : 8w2): exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    bit<8> key_0;
    @name("t2") table t2_0 {
        key = {
            key_0: exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        {
            key_0 = (t1_0.apply().hit ? 8w3 : 8w4);
            if (t2_0.apply().hit) {
                b = 32w1;
            }
        }
    }
}

control Ingress(inout bit<32> b);
package top(Ingress ig);
top(ingress()) main;

