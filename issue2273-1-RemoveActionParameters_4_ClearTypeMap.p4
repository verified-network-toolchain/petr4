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
    U push();
    U pop();
    @synchronous(push, pop) abstract void apply(inout T value, @optional out U rv);
    @synchronous(push) @optional abstract void overflow(@optional inout T value, @optional out U rv);
    @synchronous(pop) @optional abstract void underflow(@optional inout T value, @optional out U rv);
}

header data_t {
    bit<32> f1;
    bit<32> f2;
    bit<16> h1;
    bit<8>  b1;
    bit<8>  b2;
}

struct headers {
    data_t data;
}

control ingress(inout headers hdr) {
    @noWarn("unused") @name(".NoAction") action NoAction_0() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_3() {
    }
    @name("stack") Stack<bit<16>>(2048) stack_1;
    @name("write") StackAction<bit<16>, bit<16>>(stack_1) write = {
        void apply(inout bit<16> value) {
            value = hdr.data.h1;
        }
        void overflow(inout bit<16> value, out bit<16> rv) {
            rv = 16w0xf0f;
        }
    };
    @name("read") StackAction<bit<16>, bit<16>>(stack_1) read = {
        void apply(inout bit<16> value, out bit<16> rv) {
            rv = value;
        }
        void underflow(inout bit<16> value, out bit<16> rv) {
            rv = 16w0xf0f0;
        }
    };
    @name("push") action push_0() {
        hdr.data.b1 = 8w0xff;
        write.push();
    }
    @name("do_push") table do_push {
        actions = {
            push_0();
            @defaultonly NoAction_0();
        }
        key = {
            hdr.data.f1: ternary @name("hdr.data.f1") ;
        }
        default_action = NoAction_0();
    }
    @name("pop") action pop_0() {
        hdr.data.b1 = 8w0xfe;
        hdr.data.h1 = read.pop();
    }
    @name("do_pop") table do_pop {
        actions = {
            pop_0();
            @defaultonly NoAction_3();
        }
        key = {
            hdr.data.f1: exact @name("hdr.data.f1") ;
        }
        default_action = NoAction_3();
    }
    apply {
        if (hdr.data.b1 == 8w0) {
            do_pop.apply();
        } else {
            do_push.apply();
        }
    }
}

control ctr<H>(inout H hdr);
package top<H>(ctr<H> ctrl);
top<headers>(ingress()) main;

