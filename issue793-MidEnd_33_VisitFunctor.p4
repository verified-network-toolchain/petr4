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

struct standard_metadata_t {
}

header data_h {
    bit<32> da;
    bit<32> db;
}

struct my_packet {
    data_h data;
}

control c(in my_packet hdr) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("c.nop") action nop() {
    }
    @name("c.t") table t_0 {
        actions = {
            nop();
            @defaultonly NoAction_1();
        }
        key = {
            hdr.data.db: exact @name("hdr.data.db") ;
        }
        default_action = NoAction_1();
    }
    apply {
        if (hdr.data.da == 32w1) {
            t_0.apply();
        }
    }
}

control C(in my_packet hdr);
package V1Switch(C vr);
V1Switch(c()) main;

