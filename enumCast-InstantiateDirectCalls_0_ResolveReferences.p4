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

enum bit<32> X {
    Zero = 0,
    One = 1
}

enum bit<8> E1 {
    e1 = 0,
    e2 = 1,
    e3 = 2
}

enum bit<8> E2 {
    e1 = 10,
    e2 = 11,
    e3 = 12
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
        X x = (X)0;
        bit<32> z = (bit<32>)X.One;
        bit<32> z1 = X.One;
        bool bb;
        E1 a = E1.e1;
        E2 b = E2.e2;
        bb = a == b;
        bb = bb && a == 0;
        bb = bb && b == 0;
        a = (E1)b;
        a = (E1)(E1.e1 + 1);
        a = (E1)(E2.e1 + E2.e2);
        packet.extract(o.b);
        transition select(o.b.x) {
            X.Zero &&& 0x1: accept;
            default: getopt;
        }
    }
    state getopt {
        packet.extract(o.opt);
        transition accept;
    }
}

parser proto<T>(packet_in p, out T t);
package top<T>(proto<T> _p);
top(p()) main;

