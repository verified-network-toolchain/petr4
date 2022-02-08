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

enum HashAlgorithm {
    lookup3
}

extern void hash<D>(out bit<32> result, in HashAlgorithm algo, in D data);
parser parse<H, M>(packet_in packet, out H headers, inout M meta, inout standard_metadata std);
control pipeline<H, M>(inout H headers, inout M meta, inout standard_metadata std);
@deparser control deparser<H>(packet_out b, in H headers);
package ubpf<H, M>(parse<H, M> prs, pipeline<H, M> p, deparser<H> dprs);
header test_t {
    bit<16> sa;
    bit<8>  da;
}

header test1_t {
    bit<8>  a;
    bit<16> b;
    bit<16> c;
    bit<8>  d;
}

header test2_t {
    bit<8> a;
}

struct Headers_t {
    test_t  test;
    test1_t test1;
    test2_t test2;
}

struct metadata {
    bit<32> output;
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    @name("a") action a_1() {
        hash<tuple<bit<16>, bit<8>>>(meta.output, HashAlgorithm.lookup3, { headers.test.sa, headers.test.da });
    }
    @name("b") action b_1() {
        hash<tuple<bit<8>, bit<16>, bit<16>, bit<8>>>(meta.output, HashAlgorithm.lookup3, { headers.test1.a, headers.test1.b, headers.test1.c, headers.test1.d });
    }
    @name("c") action c_1() {
        hash<tuple<bit<8>>>(meta.output, HashAlgorithm.lookup3, { headers.test2.a });
    }
    apply {
        a_1();
        b_1();
        c_1();
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), dprs()) main;

