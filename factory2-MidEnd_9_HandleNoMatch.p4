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

extern widget<T> {
}

extern widget<T> createWidget<T, U>(U a, T b);
parser P();
parser p1()(widget<bit<8>> w) {
    state start {
        transition accept;
    }
    state noMatch {
        verify(false, error.NoMatch);
        transition reject;
    }
}

package sw0(P p);
sw0(p1(createWidget<bit<8>, bit<16>>(16w0, 8w0))) main;

