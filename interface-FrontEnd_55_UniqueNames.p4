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

extern Crc16<T> {
    Crc16();
    Crc16(int<32> x);
    void initialize<U>(in U input_data);
    T value();
    T make_index(in T size, in T base);
}

control p() {
    @name("crc0") Crc16<bit<32>>() crc0;
    @name("crc1") Crc16<int<32>>(32s0) crc1;
    @name("crc2") Crc16<int<32>>() crc2;
    apply {
    }
}

control empty();
package m(empty e);
m(p()) main;

