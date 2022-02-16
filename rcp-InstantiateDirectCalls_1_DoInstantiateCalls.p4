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

extern Register<T> {
    Register(bit<32> size);
    void read(in bit<32> index, out T value);
    void write(in bit<32> index, in T value);
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
    Register<bit<32>>(1) input_traffic_bytes;
    Register<bit<32>>(1) sum_rtt_Tr;
    Register<bit<32>>(1) num_pkts_with_rtt;
    apply {
        @atomic {
            bit<32> input_traffic_bytes_tmp;
            input_traffic_bytes.read(0, input_traffic_bytes_tmp);
            input_traffic_bytes_tmp = input_traffic_bytes_tmp + metadata.pkt_len;
            input_traffic_bytes.write(input_traffic_bytes_tmp, 0);
            if (pkt_hdr.rtt < 32w2500) {
                bit<32> sum_rtt_Tr_tmp;
                sum_rtt_Tr.read(0, sum_rtt_Tr_tmp);
                sum_rtt_Tr_tmp = sum_rtt_Tr_tmp + pkt_hdr.rtt;
                sum_rtt_Tr.write(sum_rtt_Tr_tmp, 0);
                bit<32> num_pkts_with_rtt_tmp;
                num_pkts_with_rtt.read(0, num_pkts_with_rtt_tmp);
                num_pkts_with_rtt_tmp = num_pkts_with_rtt_tmp + 1;
                num_pkts_with_rtt.write(num_pkts_with_rtt_tmp, 0);
            }
        }
    }
}

top(ingress()) main;

