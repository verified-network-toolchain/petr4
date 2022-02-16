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

extern Virtual {
    Virtual();
    void increment();
    @synchronous(increment) abstract bit<16> f(in bit<16> ix);
    bit<16> total();
}

control c(inout bit<16> p) {
    @name("local") bit<16> local_0;
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("cntr") Virtual() cntr_0 = {
        bit<16> f(in bit<16> ix) {
            return ix + local_0;
        }
    };
    @name("final_ctr") action final_ctr() {
        p = cntr_0.total();
    }
    @name("add_ctr") action add_ctr() {
        cntr_0.increment();
    }
    @name("run_ctr") table run_ctr_0 {
        key = {
            p: exact @name("p") ;
        }
        actions = {
            add_ctr();
            final_ctr();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        local_0 = 16w4;
        run_ctr_0.apply();
    }
}

control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;

