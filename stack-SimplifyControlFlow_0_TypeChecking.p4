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

header h {
}

parser p() {
    @name("stack") h[4] stack_0;
    state start {
        stack_0[0].setInvalid();
        stack_0[1].setInvalid();
        stack_0[2].setInvalid();
        stack_0[3].setInvalid();
        stack_0[3].setValid();
        transition accept;
    }
}

control c() {
    @name("stack") h[4] stack_1;
    @name("b") h b_0;
    apply {
        stack_1[0].setInvalid();
        stack_1[1].setInvalid();
        stack_1[2].setInvalid();
        stack_1[3].setInvalid();
        stack_1[3].setValid();
        b_0 = stack_1[3];
        stack_1[2] = b_0;
        stack_1.push_front(2);
        stack_1.pop_front(2);
    }
}

parser Simple();
control Simpler();
package top(Simple par, Simpler ctr);
top(p(), c()) main;

