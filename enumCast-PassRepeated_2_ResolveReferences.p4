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

enum bit<32> X {
    Zero = 32w0,
    One = 32w1
}

enum bit<8> E1 {
    e1 = 8w0,
    e2 = 8w1,
    e3 = 8w2
}

enum bit<8> E2 {
    e1 = 8w10,
    e2 = 8w11,
    e3 = 8w12
}

header B {
    X x;
}

header Opt {
    bit<16> b;
}

struct O {
    B   b;
    Opt opt;
}

parser p(packet_in packet, out O o) {
    state start {
        packet.extract<B>(o.b);
        transition select(o.b.x) {
            X.Zero &&& 32w0x1: accept;
            default: getopt;
        }
    }
    state getopt {
        packet.extract<Opt>(o.opt);
        transition accept;
    }
}

parser proto<T>(packet_in p, out T t);
package top<T>(proto<T> _p);
top<O>(p()) main;

