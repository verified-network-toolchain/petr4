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
    @name("tmp") bool tmp_2;
    @name("tmp_0") bool tmp_3;
    @name("tmp_1") bool tmp_4;
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_3() {
    }
    @name("t1") table t1 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            NoAction_0();
        }
        default_action = NoAction_0();
    }
    @name("t2") table t2 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            NoAction_3();
        }
        default_action = NoAction_3();
    }
    apply {
        x = true;
        tmp_2 = t1.apply().hit;
        if (tmp_2) {
            tmp_4 = t2.apply().hit;
            tmp_3 = tmp_4;
        } else {
            tmp_3 = false;
        }
        if (tmp_3) {
            x = false;
        }
    }
}

control proto(out bool x);
package top(proto p);
top(c()) main;

