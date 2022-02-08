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

header h {
}

parser p() {
    state start {
        h[4] stack;
        stack[3].setValid();
        h b = stack[3];
        b = stack.last;
        stack[2] = b;
        b = stack.next;
        bit<32> e = stack.lastIndex;
        transition accept;
    }
}

control c() {
    apply {
        h[4] stack;
        stack[3].setValid();
        h b = stack[3];
        stack[2] = b;
        stack.push_front(2);
        stack.pop_front(2);
        bit<32> sz = 32w4;
    }
}

parser Simple();
control Simpler();
package top(Simple par, Simpler ctr);
top(p(), c()) main;

