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
header hdr_t {
    bit<32> a;
    bit<32> b;
}

struct Headers_t {
    hdr_t h;
}

struct metadata {
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        p.extract<hdr_t>(headers.h);
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    @name("add") action add_0(@name("data") bit<32> data) {
        headers.h.b = headers.h.a + data;
    }
    @name("tbl_a") table tbl_a {
        actions = {
            add_0();
        }
        default_action = add_0(32w10);
    }
    apply {
        tbl_a.apply();
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit<hdr_t>(headers.h);
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), dprs()) main;

