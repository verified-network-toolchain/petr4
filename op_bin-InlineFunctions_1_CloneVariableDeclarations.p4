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

extern CounterArray {
    CounterArray(bit<32> max_index, bool sparse);
    void increment(in bit<32> index);
    void add(in bit<32> index, in bit<32> value);
}

extern array_table {
    array_table(bit<32> size);
}

extern hash_table {
    hash_table(bit<32> size);
}

parser parse<H>(packet_in packet, out H headers);
control filter<H>(inout H headers, out bool accept);
package ebpfFilter<H>(parse<H> prs, filter<H> filt);
typedef bit<48> EthernetAddress;
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header IPv6_h {
    bit<32>  ip_version_traffic_class_and_flow_label;
    bit<16>  payload_length;
    bit<8>   protocol;
    bit<8>   hop_limit;
    bit<128> src_address;
    bit<128> dst_address;
}

struct Headers_t {
    Ethernet_h ethernet;
    IPv6_h     ipv6;
}

parser prs(packet_in p, out Headers_t headers) {
    state start {
        p.extract<Ethernet_h>(headers.ethernet);
        transition select(headers.ethernet.etherType) {
            16w0x86dd: ipv6;
            default: reject;
        }
    }
    state ipv6 {
        p.extract<IPv6_h>(headers.ipv6);
        transition accept;
    }
}

control pipe(inout Headers_t headers, out bool xout) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("set_flowlabel") action set_flowlabel_0(@name("label") bit<20> label) {
        headers.ipv6.ip_version_traffic_class_and_flow_label[31:12] = label;
    }
    @name("filter_tbl") table filter_tbl {
        key = {
            headers.ipv6.src_address: exact @name("headers.ipv6.src_address") ;
        }
        actions = {
            set_flowlabel_0();
            @defaultonly NoAction_0();
        }
        const entries = {
                        128w0x200204200380deadbeeff00d0d090001 : set_flowlabel_0(20w52);
        }
        implementation = hash_table(32w8);
        default_action = NoAction_0();
    }
    apply {
        xout = true;
        filter_tbl.apply();
        if (headers.ipv6.isValid() && (headers.ethernet.etherType == 16w0x86dd || headers.ipv6.hop_limit == 8w255)) {
            headers.ipv6.protocol = 8w17;
        }
        if (headers.ethernet.etherType == 16w0x800) {
            headers.ipv6.protocol = 8w10;
        }
    }
}

ebpfFilter<Headers_t>(prs(), pipe()) main;

