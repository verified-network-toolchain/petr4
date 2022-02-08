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

struct Headers {
    bit<8> a;
    bit<8> b;
}

bit<8> f(inout bit<8> x, in bit<8> z) {
    return 8w4;
}
bit<8> g(inout bit<8> z) {
    z = 8w3;
    return 8w1;
}
control ingress(inout Headers h) {
    bit<8> tmp;
    bool tmp_0;
    bit<8> tmp_1;
    bit<8> tmp_2;
    bit<8> tmp_3;
    bit<8> tmp_4;
    @name("a") action a_0() {
        h.b = 8w0;
    }
    @name("t") table t_0 {
        key = {
            h.b: exact @name("h.b") ;
        }
        actions = {
            a_0();
        }
        default_action = a_0();
    }
    apply {
        tmp = h.a;
        tmp_0 = t_0.apply().hit;
        if (tmp_0) {
            tmp_1 = h.a;
        } else {
            tmp_1 = h.b;
        }
        tmp_2 = tmp_1;
        f(tmp, tmp_2);
        h.a = tmp;
        tmp_3 = h.a;
        tmp_4 = g(h.a);
        f(tmp_3, tmp_4);
        h.a = tmp_3;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

