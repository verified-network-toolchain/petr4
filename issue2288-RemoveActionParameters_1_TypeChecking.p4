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
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<8> retval_1;
    hasReturned_1 = false;
    {
        hasReturned_1 = true;
        retval_1 = 8w4;
    }
    return retval_1;
}
bit<8> g(inout bit<8> z) {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") bit<8> retval_2;
    hasReturned_2 = false;
    z = 8w3;
    {
        hasReturned_2 = true;
        retval_2 = 8w1;
    }
    return retval_2;
}
control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp_5;
    @name("tmp_0") bool tmp_6;
    @name("tmp_1") bit<8> tmp_7;
    @name("tmp_2") bit<8> tmp_8;
    @name("tmp_3") bit<8> tmp_9;
    @name("tmp_4") bit<8> tmp_10;
    @name("a") action a_0() {
        h.b = 8w0;
    }
    @name("t") table t {
        key = {
            h.b: exact @name("h.b") ;
        }
        actions = {
            a_0();
        }
        default_action = a_0();
    }
    apply {
        tmp_5 = h.a;
        tmp_6 = t.apply().hit;
        if (tmp_6) {
            tmp_7 = h.a;
        } else {
            tmp_7 = h.b;
        }
        tmp_8 = tmp_7;
        f(tmp_5, tmp_8);
        h.a = tmp_5;
        tmp_9 = h.a;
        tmp_10 = g(h.a);
        f(tmp_9, tmp_10);
        h.a = tmp_9;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

