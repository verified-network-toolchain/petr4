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

@noWarn("unused") @name(".NoAction") action NoAction() {
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
extern Register<T, S> {
    Register(bit<32> size);
    T read(in S index);
    void write(in S index, in T value);
}

parser parse<H, M>(packet_in packet, out H headers, inout M meta, inout standard_metadata std);
control pipeline<H, M>(inout H headers, inout M meta, inout standard_metadata std);
@deparser control deparser<H>(packet_out b, in H headers);
package ubpf<H, M>(parse<H, M> prs, pipeline<H, M> p, deparser<H> dprs);
typedef bit<48> EthernetAddress;
typedef bit<32> IPv4Address;
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
    bit<8> qfi;
    bit<8> filt_dir;
    bit<8> reflec_qos;
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        p.extract<Ethernet_h>(headers.ethernet);
        transition select(headers.ethernet.etherType) {
            16w0x800: ipv4;
            default: reject;
        }
    }
    state ipv4 {
        p.extract<IPv4_h>(headers.ipv4);
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("Reject") action Reject_0() {
        mark_to_drop();
    }
    @name("Reject") action Reject() {
        mark_to_drop();
    }
    @name("filter_tbl") table filter_tbl_0 {
        key = {
            headers.ipv4.srcAddr: exact @name("headers.ipv4.srcAddr") ;
        }
        actions = {
            Reject();
            NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        if (headers.ipv4.isValid()) {
            filter_tbl_0.apply();
        }
        if (meta.qfi != 8w0 && (meta.filt_dir == 8w2 || meta.reflec_qos == 8w1)) {
            meta.qfi = 8w3;
        }
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit<Ethernet_h>(headers.ethernet);
        packet.emit<IPv4_h>(headers.ipv4);
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), dprs()) main;

