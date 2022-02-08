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
    @name("c.tmp") bool tmp;
    @name("c.tmp_0") bool tmp_0;
    @name("c.tmp_1") bool tmp_1;
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_2() {
    }
    @name("c.t1") table t1_0 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            NoAction_1();
        }
        default_action = NoAction_1();
    }
    @name("c.t2") table t2_0 {
        key = {
            x: exact @name("x") ;
        }
        actions = {
            NoAction_2();
        }
        default_action = NoAction_2();
    }
    @hidden action act() {
        tmp = true;
    }
    @hidden action act_0() {
        tmp = false;
    }
    @hidden action simplify31() {
        x = true;
    }
    @hidden action act_1() {
        tmp_1 = true;
    }
    @hidden action act_2() {
        tmp_1 = false;
    }
    @hidden action simplify32() {
        tmp_0 = tmp_1;
    }
    @hidden action simplify32_0() {
        tmp_0 = false;
    }
    @hidden action simplify33() {
        x = false;
    }
    apply {
        simplify31();
        if (t1_0.apply().hit) {
            act();
        } else {
            act_0();
        }
        if (tmp) {
            if (t2_0.apply().hit) {
                act_1();
            } else {
                act_2();
            }
            simplify32();
        } else {
            simplify32_0();
        }
        if (tmp_0) {
            simplify33();
        }
    }
}

control proto(out bool x);
package top(proto p);
top(c()) main;

