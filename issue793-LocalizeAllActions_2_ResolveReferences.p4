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
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("nop") action nop_0() {
    }
    @name("t") table t_0 {
        actions = {
            nop_0();
            @defaultonly NoAction_0();
        }
        key = {
            hdr.data.db: exact @name("hdr.data.db") ;
        }
        default_action = NoAction_0();
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

