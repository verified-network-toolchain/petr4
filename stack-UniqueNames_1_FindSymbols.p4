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
    @name("stack") h[4] stack;
    state start {
        stack[0].setInvalid();
        stack[1].setInvalid();
        stack[2].setInvalid();
        stack[3].setInvalid();
        stack[3].setValid();
        transition accept;
    }
}

control c() {
    @name("stack") h[4] stack_2;
    @name("b") h b;
    apply {
        stack_2[0].setInvalid();
        stack_2[1].setInvalid();
        stack_2[2].setInvalid();
        stack_2[3].setInvalid();
        stack_2[3].setValid();
        b = stack_2[3];
        stack_2[2] = b;
        stack_2.push_front(2);
        stack_2.pop_front(2);
    }
}

parser Simple();
control Simpler();
package top(Simple par, Simpler ctr);
top(p(), c()) main;

