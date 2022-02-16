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

control c(inout bit<32> b) {
    bit<32> switch_0_key;
    @hidden action switch_0_case() {
    }
    @hidden action switch_0_case_0() {
    }
    @hidden action switch_0_case_1() {
    }
    @hidden table switch_0_table {
        key = {
            switch_0_key: exact;
        }
        actions = {
            switch_0_case();
            switch_0_case_0();
            switch_0_case_1();
        }
        const default_action = switch_0_case_1();
        const entries = {
                        32w16 : switch_0_case();
                        32w32 : switch_0_case();
                        32w64 : switch_0_case_0();
                        32w92 : switch_0_case_1();
        }
    }
    @hidden action switchexpression7() {
        b = 32w1;
    }
    @hidden action switchexpression8() {
        b = 32w2;
    }
    @hidden action switchexpression10() {
        b = 32w3;
    }
    @hidden action switchexpression5() {
        switch_0_key = b;
    }
    apply {
        {
            switchexpression5();
            switch (switch_0_table.apply().action_run) {
                switch_0_case: {
                    switchexpression7();
                }
                switch_0_case_0: {
                    switchexpression8();
                }
                switch_0_case_1: {
                    switchexpression10();
                }
            }
        }
    }
}

control ct(inout bit<32> b);
package top(ct _c);
top(c()) main;

