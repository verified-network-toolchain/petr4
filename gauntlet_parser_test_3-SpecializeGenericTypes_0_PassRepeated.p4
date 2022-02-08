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

header Hdr {
    bit<8> x;
}

struct Headers {
    Hdr[2] h1;
    Hdr[2] h2;
}

parser P(packet_in p, out Headers h) {
    state start {
        p.extract<Hdr>(h.h1.next);
        p.extract<Hdr>(h.h1.next);
        if (h.h1[1].x == 8w1) {
            h.h2[1] = h.h1.next;
        } else {
            h.h2[1] = h.h1.last;
        }
        transition accept;
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top<Headers>(P()) main;

