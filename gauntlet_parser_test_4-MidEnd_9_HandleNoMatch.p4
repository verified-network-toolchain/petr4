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

header Hdr {
    bit<1> x;
}

struct Headers {
    Hdr[2] h1;
}

parser P(packet_in p, out Headers h) {
    state start {
        p.extract<Hdr>(h.h1.next);
        transition select(h.h1[0].x == 1w1) {
            true: start_true;
            false: start_join;
            default: noMatch;
        }
    }
    state start_true {
        p.extract<Hdr>(h.h1.next);
        transition start_join;
    }
    state start_join {
        transition select(h.h1.lastIndex) {
            32w0: accept;
            default: start;
        }
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top<Headers>(P()) main;

