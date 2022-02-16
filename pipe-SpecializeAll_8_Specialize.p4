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

@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

match_kind {
    ternary,
    exact
}

typedef bit<9> BParamType;
struct TArg1 {
    bit<9> field1;
    bool   drop;
}

struct TArg2 {
    int<32> field2;
}

struct PArg1 {
    bit<32> f0;
    bool    drop;
}

struct QArg1 {
    bit<32> f1;
}

struct QArg2 {
    bit<32> f2;
}

extern bs {
}

struct Packet_data {
}

control T_host(inout TArg1 tArg1, in TArg2 aArg2)(bit<32> t2Size) {
    @name("B_action") action B_action_0(@name("barg") out bit<9> barg_0, @name("bData") BParamType bData_0) {
        barg_0 = bData_0;
    }
    @name("C_action") action C_action_0(@name("cData") bit<9> cData_0) {
        tArg1.field1 = cData_0;
    }
    @name("T") table T_0 {
        key = {
            tArg1.field1: ternary @name("tArg1.field1") ;
            aArg2.field2: exact @name("aArg2.field2") ;
        }
        actions = {
            B_action_0(tArg1.field1);
            C_action_0();
        }
        size = t2Size;
        const default_action = C_action_0(9w5);
    }
    apply {
        T_0.apply();
    }
}

control T_host_0(inout TArg1 tArg1, in TArg2 aArg2) {
    @name("B_action") action B_action_0(@name("barg") out bit<9> barg_0, @name("bData") BParamType bData_0) {
        barg_0 = bData_0;
    }
    @name("C_action") action C_action_0(@name("cData") bit<9> cData_0) {
        tArg1.field1 = cData_0;
    }
    @name("T") table T_0 {
        key = {
            tArg1.field1: ternary @name("tArg1.field1") ;
            aArg2.field2: exact @name("aArg2.field2") ;
        }
        actions = {
            B_action_0(tArg1.field1);
            C_action_0();
        }
        size = 32w5;
        const default_action = C_action_0(9w5);
    }
    apply {
        T_0.apply();
    }
}

control P_pipe_0(inout TArg1 pArg1, inout TArg2 pArg2) {
    @name("thost") T_host_0() thost_0;
    @name("Drop") action Drop_0() {
        pArg1.drop = true;
    }
    @name("Tinner") table Tinner_0 {
        key = {
            pArg1.field1: ternary @name("pArg1.field1") ;
        }
        actions = {
            Drop_0();
            NoAction();
        }
        const default_action = NoAction();
    }
    apply {
        thost_0.apply(pArg1, pArg2);
        thost_0.apply(pArg1, pArg2);
        Tinner_0.apply();
    }
}

control Q_pipe(inout TArg1 qArg1, inout TArg2 qArg2) {
    @name("p1") P_pipe_0() p1_0;
    apply {
        p1_0.apply(qArg1, qArg2);
    }
}

parser prs(bs b, out Packet_data p);
control pp(inout TArg1 arg1, inout TArg2 arg2);
package myswitch(prs prser, pp pipe);
parser my_parser(bs b, out Packet_data p) {
    state start {
        transition accept;
    }
}

myswitch(my_parser(), Q_pipe()) main;

