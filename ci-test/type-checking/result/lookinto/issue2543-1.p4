/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2543-1.p4
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

bit<16> give_val() {
    return 16w1;
}

ethernet_t give_hdr() {
    return {1, 1, 1};
    bit<16> dummy = 16w1;
    return {1, 1, dummy };
}

control ingress(inout Headers h) {
    Headers foo = { { 1, 1, give_val() }};
    apply {
        give_hdr();
        foo.eth_hdr.eth_type[3:0] = 4w1;
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
bit<16> give_val () {
  return 16w1;
}
ethernet_t give_hdr ()
  {
  return {1, 1, 1};
  bit<16> dummy = 16w1;
  return {1, 1, dummy};
}
control ingress(inout Headers h) {
  Headers foo = {{1, 1, give_val()}};
  apply {
    give_hdr();
    foo.eth_hdr.eth_type[3:0] = 4w1;
  }
}
control Ingress (inout Headers hdr);
package top (Ingress ig);
top(ingress()) main;

