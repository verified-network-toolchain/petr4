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

extern Virtual {
    Virtual();
    void increment();
    @synchronous(increment) abstract bit<16> f(in bit<16> ix);
    bit<16> total();
}

control c(inout bit<16> p) {
    bit<16> local;
    Virtual() cntr = {
        bit<16> f(in bit<16> ix) {
            return ix + local;
        }
    };
    action final_ctr() {
        p = cntr.total();
    }
    action add_ctr() {
        cntr.increment();
    }
    table run_ctr {
        key = {
            p: exact;
        }
        actions = {
            add_ctr();
            final_ctr();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        local = 4;
        run_ctr.apply();
    }
}

control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;

