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

control ingress(inout bit<32> b) {
    @name("key_1") bit<8> key_2;
    @name("key_0") bit<8> key_3;
    @name("tmp") bool tmp_3;
    @name("tmp_0") bit<8> tmp_4;
    @name("tmp_1") bool tmp_5;
    @name("tmp_2") bit<8> tmp_6;
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_4() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_5() {
    }
    @name("t0") table t0 {
        key = {
            b: exact @name("b") ;
        }
        actions = {
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    @name("t1") table t1 {
        key = {
            key_2: exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction_4();
        }
        default_action = NoAction_4();
    }
    @name("t2") table t2 {
        key = {
            key_3: exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction_5();
        }
        default_action = NoAction_5();
    }
    apply {
        tmp_5 = t0.apply().hit;
        if (tmp_5) {
            tmp_6 = 8w1;
        } else {
            tmp_6 = 8w2;
        }
        key_2 = tmp_6;
        tmp_3 = t1.apply().hit;
        if (tmp_3) {
            tmp_4 = 8w3;
        } else {
            tmp_4 = 8w4;
        }
        key_3 = tmp_4;
        if (t2.apply().hit) {
            b = 32w1;
        }
    }
}

control Ingress(inout bit<32> b);
package top(Ingress ig);
top(ingress()) main;

