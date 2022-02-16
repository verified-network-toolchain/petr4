/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2956.p4
\n
#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    action simple_assign() {
        h.eth_hdr.eth_type = 1;
    }
    table dummy_table {
        key = {
            h.eth_hdr.src_addr: exact @name("key") ;
        }
        actions = {
            NoAction();
            simple_assign();
        }
    }
    apply {
        switch (dummy_table.apply().action_run) {
            simple_assign: {
                simple_assign();
            }
            NoAction: {
            }
        }
        simple_assign();
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

************************\n******** petr4 type checking result: ********\n************************\n
error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused")
action NoAction() { 
}
match_kind {
  exact, ternary, lpm
}
header ethernet_t {
  bit<48> dst_addr;
  bit<48> src_addr;
  bit<16> eth_type;
}
struct Headers {
  ethernet_t eth_hdr;
}
parser p(packet_in pkt, out Headers hdr) {
  state start {
    transition parse_hdrs;
  }
  state parse_hdrs {
    pkt.extract(hdr.eth_hdr);
    transition accept;
  }
}
control ingress(inout Headers h) {
  action simple_assign() {
    h.eth_hdr.eth_type = 1;
  }
  table dummy_table
    {
    key = {
      h.eth_hdr.src_addr: exact@name("key")
        ;
    }
    actions = {
      NoAction;simple_assign;
    }
  }
  apply {
    switch (dummy_table.apply().action_run) {
    simple_assign: {
    simple_assign();
    }
    NoAction: { 
    }
    }
    simple_assign();
  }
}
parser Parser (packet_in b, out Headers hdr);
control Ingress (inout Headers hdr);
package top (Parser p, Ingress ig);
top(p(), ingress()) main;

