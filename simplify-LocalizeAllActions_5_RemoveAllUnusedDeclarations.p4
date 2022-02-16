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

control c(out bool x) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_2() {
    }
    bool tmp;
    bool tmp_0;
    bool tmp_1;
    @name("t1") table t1_0 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            NoAction_1();
        }
        default_action = NoAction_1();
    }
    @name("t2") table t2_0 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            NoAction_2();
        }
        default_action = NoAction_2();
    }
    apply {
        x = true;
        tmp = t1_0.apply().hit;
        if (tmp) {
            tmp_1 = t2_0.apply().hit;
            tmp_0 = tmp_1;
        } else {
            tmp_0 = false;
        }
        if (tmp_0) {
            x = false;
        }
    }
}

control proto(out bool x);
package top(proto p);
top(c()) main;

