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

const bit<32> __ubpf_model_version = 32w20200515;
enum ubpf_action {
    ABORT,
    DROP,
    PASS,
    REDIRECT
}

struct standard_metadata {
    bit<32>     input_port;
    bit<32>     packet_length;
    ubpf_action output_action;
    bit<32>     output_port;
    bool        clone;
    bit<32>     clone_port;
}

extern void mark_to_drop();
extern void mark_to_pass();
extern Register<T, S> {
    Register(bit<32> size);
    T read(in S index);
    void write(in S index, in T value);
}

extern bit<48> ubpf_time_get_ns();
extern void truncate(in bit<32> len);
enum HashAlgorithm {
    lookup3
}

extern void hash<D>(out bit<32> result, in HashAlgorithm algo, in D data);
extern bit<16> csum_replace2(in bit<16> csum, in bit<16> old, in bit<16> new);
extern bit<16> csum_replace4(in bit<16> csum, in bit<32> old, in bit<32> new);
parser parse<H, M>(packet_in packet, out H headers, inout M meta, inout standard_metadata std);
control pipeline<H, M>(inout H headers, inout M meta, inout standard_metadata std);
@deparser control deparser<H>(packet_out b, in H headers);
package ubpf<H, M>(parse<H, M> prs, pipeline<H, M> p, deparser<H> dprs);
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

struct metadata {
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
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

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    action Reject(IPv4Address add) {
        mark_to_drop();
        headers.ipv4.srcAddr = add;
    }
    table Check_src_ip {
        key = {
            headers.ipv4.srcAddr : lpm @name("headers.ipv4.srcAddr") ;
            headers.ipv4.protocol: exact @name("headers.ipv4.protocol") ;
        }
        actions = {
            Reject();
            NoAction();
        }
        default_action = Reject(32w0);
    }
    apply {
        if (headers.ipv4.isValid()) {
            ;
        } else {
            headers.ipv4.setInvalid();
            headers.ipv4.setValid();
            mark_to_drop();
            return;
        }
        Check_src_ip.apply();
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit<Ethernet_h>(headers.ethernet);
        packet.emit<IPv4_h>(headers.ipv4);
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), dprs()) main;

