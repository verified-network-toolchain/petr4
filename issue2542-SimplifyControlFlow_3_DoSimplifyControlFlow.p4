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

header ethernet_t {
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

control ingress(inout Headers h) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("sub.dummy") table sub_dummy_0 {
        key = {
            16w2: exact @name("dummy_key") ;
        }
        actions = {
            @defaultonly NoAction_0();
        }
        default_action = NoAction_0();
    }
    apply {
        sub_dummy_0.apply();
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

