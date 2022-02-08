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

control ingress(inout Headers h) {
    @name("ingress.tmp_3") bit<8> tmp_3;
    @name("ingress.a") action a_1() {
        h.b = 8w0;
    }
    @name("ingress.t") table t_0 {
        key = {
            h.b: exact @name("h.b") ;
        }
        actions = {
            a_1();
        }
        default_action = a_1();
    }
    apply {
        t_0.apply();
        tmp_3 = h.a;
        h.a = 8w3;
        h.a = tmp_3;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

