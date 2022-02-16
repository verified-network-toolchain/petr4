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
@ethernetaddress typedef bit<48> EthernetAddress;
@ipv4address typedef bit<32> IPv4Address;
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header IPv4_h {
    bit<4>      version;
    bit<4>      ihl;
    bit<8>      diffserv;
    bit<16>     totalLen;
    bit<16>     identification;
    bit<3>      flags;
    bit<13>     fragOffset;
    bit<8>      ttl;
    bit<8>      protocol;
    bit<16>     hdrChecksum;
    IPv4Address srcAddr;
    IPv4Address dstAddr;
}

struct Headers_t {
    Ethernet_h ethernet;
    IPv4_h     ipv4;
}

parser prs(packet_in p, out Headers_t headers) {
    state start {
        p.extract<Ethernet_h>(headers.ethernet);
        transition select(headers.ethernet.etherType) {
            16w0x800: ip;
            default: reject;
        }
    }
    state ip {
        p.extract<IPv4_h>(headers.ipv4);
        transition accept;
    }
}

control pipe(inout Headers_t headers, out bool pass) {
    @name("Reject") action Reject_0(@name("add") IPv4Address add_0) {
        pass = false;
        headers.ipv4.srcAddr = add_0;
    }
    @name("Check_src_ip") table Check_src_ip_0 {
        key = {
            headers.ipv4.srcAddr: exact @name("headers.ipv4.srcAddr") ;
        }
        actions = {
            Reject_0();
            NoAction();
        }
        implementation = hash_table(32w1024);
        const default_action = NoAction();
    }
    apply {
        pass = true;
        if (headers.ipv4.isValid()) {
            ;
        } else {
            pass = false;
            return;
        }
        if (Check_src_ip_0.apply().hit) {
            pass = pass;
        }
    }
}

ebpfFilter<Headers_t>(prs(), pipe()) main;

