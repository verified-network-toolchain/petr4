/petr4/ci-test/type-checking/testdata/p4_16_samples/annotation-bug.p4
\n
#include <core.p4>

struct standard_metadata_t {}

header ipv4_option_timestamp_t {
    bit<8>      len;
    @length((bit<32>)len)
    varbit<304> data;
}

struct headers {
    ipv4_option_timestamp_t ipv4_option_timestamp;
}

struct tuple_0 {
    ipv4_option_timestamp_t field_12;
}

extern bit<16> get<T>(in T data);

control cc() {
    headers hdr;
    apply {
        get<headers>({ hdr.ipv4_option_timestamp });
    }
}

control C();
package top(C ck);

top(cc()) main;
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
struct standard_metadata_t {
  
}
header ipv4_option_timestamp_t {
  bit<8> len;
  @length(bit<32> len)
  varbit <304> data;
}
struct headers {
  ipv4_option_timestamp_t ipv4_option_timestamp;
}
struct tuple_0 {
  ipv4_option_timestamp_t field_12;
}
extern bit<16> get<T3>(in T3 data);
control cc() {
  headers hdr;
  apply {
    get<headers>({hdr.ipv4_option_timestamp});
  }
}
control C ();
package top (C ck);
top(cc()) main;

