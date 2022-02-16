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
    state start {
        transition parse_headers;
    }
    state parse_headers {
        transition select(p.lookahead<bit<8>>()) {
            1: parse_one;
            2: parse_two;
            4: parse_four;
            default: accept;
        }
    }
    state parse_one {
        p.extract(headers.one);
        transition parse_headers;
    }
    state parse_two {
        p.extract(headers.two);
        transition parse_headers;
    }
    state parse_four {
        p.extract(headers.four);
        transition parse_headers;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    apply {
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit(headers.one);
        packet.emit(headers.two);
        packet.emit(headers.four);
    }
}

ubpf(prs(), pipe(), dprs()) main;

