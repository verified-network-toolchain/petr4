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
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    @name("simple_table_1") table simple_table {
        key = {
            48w1: exact @name("KOXpQP") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    bit<8> key_0;
    @name("simple_table_2") table simple_table_0 {
        key = {
            key_0: exact @name("key") ;
        }
        actions = {
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    bool tmp;
    bit<8> tmp_0;
    apply {
        {
            {
                tmp = simple_table.apply().hit;
                if (tmp) {
                    tmp_0 = 8w1;
                } else {
                    tmp_0 = 8w2;
                }
                key_0 = tmp_0;
            }
            if (simple_table_0.apply().hit) {
                h.eth_hdr.dst_addr = 48w1;
            }
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

