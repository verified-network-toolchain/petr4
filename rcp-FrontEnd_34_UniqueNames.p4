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

control ingress(inout H pkt_hdr, in Metadata metadata) {
    @name("input_traffic_bytes") Register<bit<32>>(32w1) input_traffic_bytes_0;
    @name("sum_rtt_Tr") Register<bit<32>>(32w1) sum_rtt_Tr_0;
    @name("num_pkts_with_rtt") Register<bit<32>>(32w1) num_pkts_with_rtt_0;
    apply {
        @atomic {
            @name("input_traffic_bytes_tmp") bit<32> input_traffic_bytes_tmp_0;
            input_traffic_bytes_0.read(32w0, input_traffic_bytes_tmp_0);
            input_traffic_bytes_tmp_0 = input_traffic_bytes_tmp_0 + metadata.pkt_len;
            input_traffic_bytes_0.write(input_traffic_bytes_tmp_0, 32w0);
            if (pkt_hdr.rtt < 32w2500) {
                @name("sum_rtt_Tr_tmp") bit<32> sum_rtt_Tr_tmp_0;
                sum_rtt_Tr_0.read(32w0, sum_rtt_Tr_tmp_0);
                sum_rtt_Tr_tmp_0 = sum_rtt_Tr_tmp_0 + pkt_hdr.rtt;
                sum_rtt_Tr_0.write(sum_rtt_Tr_tmp_0, 32w0);
                @name("num_pkts_with_rtt_tmp") bit<32> num_pkts_with_rtt_tmp_0;
                num_pkts_with_rtt_0.read(32w0, num_pkts_with_rtt_tmp_0);
                num_pkts_with_rtt_tmp_0 = num_pkts_with_rtt_tmp_0 + 32w1;
                num_pkts_with_rtt_0.write(num_pkts_with_rtt_tmp_0, 32w0);
            }
        }
    }
}

top<H, Metadata>(ingress()) main;

