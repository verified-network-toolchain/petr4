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
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

struct Headers_t {
    Ethernet_h ethernet;
}

struct metadata {
    bit<16> etherType;
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        p.extract(headers.ethernet);
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    action fill_metadata() {
        meta.etherType = headers.ethernet.etherType;
    }
    table tbl {
        key = {
            headers.ethernet.etherType: exact;
        }
        actions = {
            fill_metadata();
            NoAction();
        }
        default_action = NoAction();
    }
    action change_etherType() {
        headers.ethernet.etherType = 0x86dd;
    }
    table meta_based_tbl {
        key = {
            meta.etherType: exact;
        }
        actions = {
            change_etherType();
            NoAction();
        }
        default_action = NoAction();
    }
    apply {
        tbl.apply();
        meta_based_tbl.apply();
    }
}

control DeparserImpl(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit(headers.ethernet);
    }
}

ubpf(prs(), pipe(), DeparserImpl()) main;

