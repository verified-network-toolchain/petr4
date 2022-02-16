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

extern Register<T, S> {
    Register(bit<32> size);
    T read(in S index);
    void write(in S index, in T value);
}

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
        p.extract<Ethernet_h>(headers.ethernet);
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_2() {
    }
    @name("pipe.fill_metadata") action fill_metadata() {
        meta.etherType = headers.ethernet.etherType;
    }
    @name("pipe.tbl") table tbl_0 {
        key = {
            headers.ethernet.etherType: exact @name("headers.ethernet.etherType") ;
        }
        actions = {
            fill_metadata();
            NoAction_1();
        }
        default_action = NoAction_1();
    }
    @name("pipe.change_etherType") action change_etherType() {
        headers.ethernet.etherType = 16w0x86dd;
    }
    @name("pipe.meta_based_tbl") table meta_based_tbl_0 {
        key = {
            meta.etherType: exact @name("meta.etherType") ;
        }
        actions = {
            change_etherType();
            NoAction_2();
        }
        default_action = NoAction_2();
    }
    apply {
        tbl_0.apply();
        meta_based_tbl_0.apply();
    }
}

control DeparserImpl(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit<Ethernet_h>(headers.ethernet);
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), DeparserImpl()) main;

