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

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<16> result;
}

struct Headers {
    ethernet_t eth_hdr;
    H          h;
}

extern Checksum {
    Checksum();
    void add<T>(in T data);
    void subtract<T>(in T data);
    bool verify();
    bit<16> get();
    bit<16> update<T>(in T data, @optional in bool zeros_as_ones);
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.h);
        transition accept;
    }
}

control ingress(inout Headers h) {
    apply {
    }
}

control egress(inout Headers h) {
    Checksum() ipv4_checksum;
    apply {
        h.h.result = ipv4_checksum.update({ h.eth_hdr.dst_addr, h.eth_hdr.src_addr, h.eth_hdr.eth_type });
    }
}

control deparser(packet_out pkt, in Headers h) {
    apply {
        pkt.emit(h);
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
control Egress(inout Headers hdr);
control Deparser(packet_out b, in Headers hdr);
package top(Parser p, Ingress ig, Egress eg, Deparser dep);
top(p(), ingress(), egress(), deparser()) main;

