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
struct Headers_t {
}

parser prs(packet_in p, out Headers_t headers) {
    state start {
        transition accept;
    }
}

control pipe(inout Headers_t headers, out bool pass) {
    @name("Reject") action Reject_0(@name("rej") bit<8> rej_0, @name("bar") bit<8> bar_0) {
        if (rej_0 == 8w0) {
            pass = true;
        } else {
            pass = false;
        }
        if (bar_0 == 8w0) {
            pass = false;
        }
    }
    @name("Reject") action Reject(@name("rej") bit<8> rej_0, @name("bar") bit<8> bar_0) {
        if (rej_0 == 8w0) {
            pass = true;
        } else {
            pass = false;
        }
        if (bar_0 == 8w0) {
            pass = false;
        }
    }
    @name("t") table t_0 {
        actions = {
            Reject();
        }
        default_action = Reject(8w1, 8w0);
    }
    apply {
        t_0.apply();
    }
}

ebpfFilter<Headers_t>(prs(), pipe()) main;

