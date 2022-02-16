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

typedef bit<16> Base_t;
typedef Base_t Base1_t;
typedef Base1_t Base2_t;
typedef Base2_t EthT;
header Ethernet {
    bit<48> src;
    bit<48> dest;
    EthT    type;
}

struct Headers {
    Ethernet eth;
}

parser prs(packet_in p, out Headers h) {
    @name("prs.e") Ethernet e_0;
    state start {
        e_0.setInvalid();
        p.extract<Ethernet>(e_0);
        transition select(e_0.type) {
            16w0x800: accept;
            16w0x806: accept;
            default: reject;
        }
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control c(inout Headers h) {
    @name("c.hasReturned") bool hasReturned;
    apply {
        hasReturned = false;
        if (h.eth.isValid()) {
            ;
        } else {
            hasReturned = true;
        }
        if (hasReturned) {
            ;
        } else if (h.eth.type == 16w0x800) {
            h.eth.setInvalid();
        } else {
            h.eth.type = 16w0;
        }
    }
}

parser p<H>(packet_in _p, out H h);
control ctr<H>(inout H h);
package top<H>(p<H> _p, ctr<H> _c);
top<Headers>(prs(), c()) main;

