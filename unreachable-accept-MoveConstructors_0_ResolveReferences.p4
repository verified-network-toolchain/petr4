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

header ethernet_h {
    bit<48> dst;
    bit<48> src;
    bit<16> type;
}

struct headers_t {
    ethernet_h ethernet;
}

parser Parser(packet_in pkt_in, out headers_t hdr) {
    state start {
        pkt_in.extract<ethernet_h>(hdr.ethernet);
        transition reject;
    }
}

control Deparser(in headers_t hdr, packet_out pkt_out) {
    apply {
        pkt_out.emit<ethernet_h>(hdr.ethernet);
    }
}

parser P<H>(packet_in pkt, out H hdr);
control D<H>(in H hdr, packet_out pkt);
package S<H>(P<H> p, D<H> d);
S<headers_t>(Parser(), Deparser()) main;

