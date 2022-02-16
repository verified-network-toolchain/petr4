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

extern ConditionalAccumulator<T> {
    ConditionalAccumulator(bit<32> size);
    void read(out T value);
    void write(in T value, in bool condition);
}

enum CounterType {
    packets,
    bytes,
    packets_and_bytes
}

extern Counter<T> {
    Counter(CounterType type);
    void count();
}

control proto<P, M>(inout P packet, in M meta);
package top<P, M>(proto<P, M> _p);
header H {
    bit<32> rtt;
}

struct Metadata {
    bit<32> pkt_len;
}

const bit<32> MAX_ALLOWABLE_RTT = 32w2500;
control ingress(inout H pkt_hdr, in Metadata metadata) {
    Counter<bit<32>>(CounterType.packets_and_bytes) input_traffic_bytes;
    ConditionalAccumulator<bit<32>>(32w1) sum_rtt_Tr;
    ConditionalAccumulator<bit<32>>(32w1) num_pkts_with_rtt;
    apply {
        @atomic {
            input_traffic_bytes.count();
            sum_rtt_Tr.write(pkt_hdr.rtt, pkt_hdr.rtt < 32w2500);
            num_pkts_with_rtt.write(32w1, pkt_hdr.rtt < 32w2500);
        }
    }
}

top<H, Metadata>(ingress()) main;

