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

@noWarn("unused") action NoAction() {
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

control SubCtrl(bit<16> eth_type) {
    @name("dummy") table dummy_0 {
        key = {
            eth_type: exact @name("dummy_key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        dummy_0.apply();
    }
}

control ingress(inout Headers h) {
    @name("sub") SubCtrl() sub_0;
    @name("sub.dummy") table sub_dummy {
        key = {
            16w2: exact @name("dummy_key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        {
            sub_dummy.apply();
        }
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

