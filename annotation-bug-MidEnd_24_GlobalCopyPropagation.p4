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

struct standard_metadata_t {
}

header ipv4_option_timestamp_t {
    bit<8>      len;
    @length((bit<32>)len) 
    varbit<304> data;
}

struct headers {
    ipv4_option_timestamp_t ipv4_option_timestamp;
}

struct tuple_0 {
    ipv4_option_timestamp_t field_12;
}

extern bit<16> get<T>(in T data);
control cc() {
    ipv4_option_timestamp_t hdr_0_ipv4_option_timestamp;
    ipv4_option_timestamp_t tmp_ipv4_option_timestamp;
    apply {
        hdr_0_ipv4_option_timestamp.setInvalid();
        {
            tmp_ipv4_option_timestamp = hdr_0_ipv4_option_timestamp;
        }
        get<headers>((headers){ipv4_option_timestamp = tmp_ipv4_option_timestamp});
    }
}

control C();
package top(C ck);
top(cc()) main;

