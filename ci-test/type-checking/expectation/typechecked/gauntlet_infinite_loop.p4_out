/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4
\n
#include <core.p4>

header H {
    bit<8> a;
}

header padding {
    bit<8> p;
}

struct headers {
    H nop;
    padding p;
}

parser sub_parser(packet_in b, out headers hdr, out padding padding) {

    state start {
        transition next;
    }

    state next {
        transition select(padding.p) {
            0: parse_hdr;
            default: accept;
        }
    }
    state parse_hdr {
        b.extract(hdr.nop);
        transition next;
    }

}

parser p(packet_in packet, out headers hdr) {
    state start {
        sub_parser.apply(packet, hdr, hdr.p);
        transition accept;
    }

}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;
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
header H {
  bit<8> a;
}
header padding {
  bit<8> p;
}
struct headers {
  H nop;
  padding p;
}
parser sub_parser(packet_in b, out headers hdr, out padding padding) {
  state start {
    transition next;
  }
  state next {
    transition select(padding.p) {
      0: parse_hdr;
      default: accept;
    }
  }
  state parse_hdr {
    b.extract(hdr.nop);
    transition next;
  }
}
parser p(packet_in packet, out headers hdr) {
  state start {
    sub_parser.apply(packet, hdr, hdr.p);
    transition accept;
  }
}
parser Parser (packet_in b, out headers hdr);
package top (Parser p);
top(p()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(16): [--Wwarn=shadow] warning: 'padding' shadows 'header padding'
parser sub_parser(packet_in b, out headers hdr, out padding padding) {
                                                            ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(7)
header padding {
       ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(37): [--Wwarn=ordering] warning: hdr: 'out' argument has fields in common with hdr.p
        sub_parser.apply(packet, hdr, hdr.p);
                                 ^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(37)
        sub_parser.apply(packet, hdr, hdr.p);
                                      ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(37): [--Wwarn=ordering] warning: hdr.p: 'out' argument has fields in common with hdr
        sub_parser.apply(packet, hdr, hdr.p);
                                      ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(37)
        sub_parser.apply(packet, hdr, hdr.p);
                                 ^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(23): [--Wwarn=uninitialized_use] warning: padding.p may be uninitialized
        transition select(padding.p) {
                          ^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_infinite_loop.p4(23): [--Wwarn=invalid_header] warning: accessing a field of an invalid header padding
        transition select(padding.p) {
                          ^^^^^^^
