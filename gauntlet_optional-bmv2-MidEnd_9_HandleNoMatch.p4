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
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        pkt.extract<H>(hdr.h);
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control ingress(inout Headers h) {
    apply {
    }
}

control egress(inout Headers h) {
    @name("egress.ipv4_checksum") Checksum() ipv4_checksum_0;
    apply {
        h.h.result = ipv4_checksum_0.update<tuple<bit<48>, bit<48>, bit<16>>>({ h.eth_hdr.dst_addr, h.eth_hdr.src_addr, h.eth_hdr.eth_type });
    }
}

control deparser(packet_out pkt, in Headers h) {
    apply {
        {
            pkt.emit<ethernet_t>(h.eth_hdr);
            pkt.emit<H>(h.h);
        }
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
control Egress(inout Headers hdr);
control Deparser(packet_out b, in Headers hdr);
package top(Parser p, Ingress ig, Egress eg, Deparser dep);
top(p(), ingress(), egress(), deparser()) main;

