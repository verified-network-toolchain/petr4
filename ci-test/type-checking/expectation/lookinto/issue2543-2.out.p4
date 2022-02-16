/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2543-2.p4
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

bit<16> produce_val() {
    return 16w9;
}

Headers produce_hdr() {
    return { { 1, 1, produce_val() }};
}

control ingress(inout Headers h) {
    apply {
        h = produce_hdr();
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;

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
bit<16> produce_val () {
  return 16w9;
}
Headers produce_hdr () {
  return {{1, 1, produce_val()}};
}
control ingress(inout Headers h) {
  apply {
    h = produce_hdr();
  }
}
control Ingress (inout Headers hdr);
package top (Ingress ig);
top(ingress()) main;

************************\n******** p4c type checking result: ********\n************************\n
