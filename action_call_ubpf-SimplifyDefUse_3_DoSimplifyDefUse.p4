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

extern void mark_to_pass();
extern Register<T, S> {
    Register(bit<32> size);
    T read(in S index);
    void write(in S index, in T value);
}

extern bit<48> ubpf_time_get_ns();
parser parse<H, M>(packet_in packet, out H headers, inout M meta, inout standard_metadata std);
control pipeline<H, M>(inout H headers, inout M meta, inout standard_metadata std);
@deparser control deparser<H>(packet_out b, in H headers);
package ubpf<H, M>(parse<H, M> prs, pipeline<H, M> p, deparser<H> dprs);
struct Headers_t {
}

struct metadata {
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    @name("tmp") bit<48> tmp_0;
    @name("tmp") bit<48> tmp_1;
    @name("RejectConditional") action RejectConditional_0(bit<1> condition) {
    }
    @name("act_return") action act_return_0() {
        mark_to_pass();
        return;
        ubpf_time_get_ns();
    }
    @name("act_exit") action act_exit_0() {
        mark_to_pass();
        exit;
        ubpf_time_get_ns();
    }
    @name("tbl_a") table tbl_a_0 {
        actions = {
            RejectConditional_0();
            act_return_0();
            act_exit_0();
        }
        default_action = RejectConditional_0(1w0);
    }
    apply {
        tbl_a_0.apply();
        exit;
        return;
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
    }
}

ubpf<Headers_t, metadata>(prs(), pipe(), dprs()) main;

