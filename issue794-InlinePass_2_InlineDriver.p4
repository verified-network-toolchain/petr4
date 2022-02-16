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

control c();
parser p();
package Top(c i, p prs);
extern Random2 {
    Random2();
    bit<10> read();
}

parser callee(Random2 rand) {
    state start {
        rand.read();
        transition accept;
    }
}

parser caller() {
    @name("rand1") Random2() rand1_0;
    @name("ca") callee() ca_0;
    state start {
        transition callee_start;
    }
    state callee_start {
        rand1_0.read();
        transition start_0;
    }
    state start_0 {
        transition accept;
    }
}

control foo2(Random2 rand) {
    apply {
        rand.read();
    }
}

control ingress() {
    @name("rand1") Random2() rand1_1;
    @name("foo2_inst") foo2() foo2_inst_0;
    apply {
        {
            rand1_1.read();
        }
    }
}

Top(ingress(), caller()) main;

