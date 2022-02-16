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

@noWarn("unused") @name(".NoAction") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

control Ingress<H, M>(inout H hdr, inout M meta);
package test<H, M>(Ingress<H, M> ig);
header h_h {
    bit<16> f1;
    bit<8>  f2;
}

struct my_headers_t {
    h_h h;
}

struct my_meta_t {
}

control MyIngress(inout my_headers_t hdr, inout my_meta_t meta) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("hit") action hit_0(@name("p") bit<16> p_0) {
        hdr.h.f1 = p_0;
    }
    @name("hit") action hit(@name("p") bit<16> p_0) {
        hdr.h.f1 = p_0;
    }
    @name("t") table t_0 {
        key = {
            hdr.h.f1: ternary @name("hdr.h.f1") ;
        }
        actions = {
            hit();
            @defaultonly NoAction_1();
        }
        const entries = {
                        16w0x101 : hit(16w1);
                        16w0x101 &&& 16w0x505 : hit(16w5);
                        default : hit(16w0);
        }
        default_action = NoAction_1();
    }
    apply {
        t_0.apply();
    }
}

test<my_headers_t, my_meta_t>(MyIngress()) main;

