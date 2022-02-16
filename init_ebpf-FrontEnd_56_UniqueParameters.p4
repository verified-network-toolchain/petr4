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

extern CounterArray {
    CounterArray(bit<32> max_index, bool sparse);
    void increment(in bit<32> index);
    void add(in bit<32> index, in bit<32> value);
}

extern array_table {
    array_table(bit<32> size);
}

extern hash_table {
    hash_table(bit<32> size);
}

parser parse<H>(packet_in packet, out H headers);
control filter<H>(inout H headers, out bool accept);
package ebpfFilter<H>(parse<H> prs, filter<H> filt);
header Ethernet {
    bit<48> destination;
    bit<48> source;
    bit<16> protocol;
}

struct Headers_t {
    Ethernet ethernet;
}

parser prs(packet_in p, out Headers_t headers) {
    state start {
        p.extract<Ethernet>(headers.ethernet);
        transition accept;
    }
}

control pipe(inout Headers_t headers, out bool pass) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @name("match") action match_0(@name("act") bool act) {
        pass = act;
    }
    @name("tbl") table tbl {
        key = {
            headers.ethernet.protocol: exact @name("headers.ethernet.protocol") ;
        }
        actions = {
            match_0();
            NoAction_0();
        }
        const entries = {
                        16w0x800 : match_0(true);
                        16w0xd000 : match_0(false);
        }
        implementation = hash_table(32w64);
        default_action = NoAction_0();
    }
    apply {
        pass = true;
        tbl.apply();
    }
}

ebpfFilter<Headers_t>(prs(), pipe()) main;

