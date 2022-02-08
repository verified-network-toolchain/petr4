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

header H {
    bit<32> f;
}

parser p(packet_in pk) {
    value_set<tuple<bit<32>, bit<2>>>(4) vs;
    H h;
    state start {
        pk.extract(h);
        transition select(h.f, 2w2) {
            vs: next;
            default: reject;
        }
    }
    state next {
        transition accept;
    }
}

parser ps(packet_in p);
package top(ps _p);
top(p()) main;

