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

extern Stack<T> {
    Stack(int size);
}

extern StackAction<T, U> {
    StackAction(Stack<T> stack);
    U pop();
    @synchronous(pop) @optional abstract void underflow(inout T value, out U rv);
}

header data_t {
    bit<16> h1;
}

struct headers {
    data_t data;
}

control ingress(inout headers hdr) {
    @name("stack") Stack<bit<16>>(2048) stack_0;
    @name("read") StackAction<bit<16>, bit<16>>(stack_0) read_0 = {
        void underflow(inout bit<16> value, out bit<16> rv) {
            rv = 16w0xf0f0;
        }
    };
    apply {
        hdr.data.h1 = read_0.pop();
    }
}

control ctr<H>(inout H hdr);
package top<H>(ctr<H> ctrl);
top<headers>(ingress()) main;

