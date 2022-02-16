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
header header_one {
    bit<8> type;
    bit<8> data;
}

header header_two {
    bit<8>  type;
    bit<16> data;
}

header header_four {
    bit<8>  type;
    bit<32> data;
}

struct Headers_t {
    header_one  one;
    header_two  two;
    header_four four;
}

struct metadata {
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    @name("prs.tmp") bit<8> tmp;
    @name("prs.tmp_0") bit<8> tmp_0;
    state start {
        transition parse_headers;
    }
    state parse_headers {
        tmp_0 = p.lookahead<bit<8>>();
        tmp = tmp_0;
        transition select(tmp) {
            8w1: parse_one;
            8w2: parse_two;
            8w4: parse_four;
            default: accept;
        }
    }
    state parse_one {
        p.extract<header_one>(headers.one);
        transition parse_headers;
    }
    state parse_two {
        p.extract<header_two>(headers.two);
        transition parse_headers;
    }
    state parse_four {
        p.extract<header_four>(headers.four);
        transition parse_headers;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    apply {
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit<header_one>(headers.one);
        packet.emit<header_two>(headers.two);
        packet.emit<header_four>(headers.four);
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), dprs()) main;

