/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2710.p4
\n
#include <core.p4>

control Wrapped(inout bit<8> valueSet) {
    @name("set") action set(bit<8> value) {
        valueSet = value;
    }
    @name("doSet") table doSet {
        actions = {
            set();
        }
        default_action = set(8w0);
    }
   apply {
        doSet.apply();
   }
}

control Wrapper(inout bit<8> value) {
   Wrapped() wrapped;
   apply { wrapped.apply(value); }
}

control c(inout bit<8> v);
package top(c _c);

top(Wrapper()) main;
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
control Wrapped(inout bit<8> valueSet) {
  @name("set")
  action set(bit<8> value) {
    valueSet = value;
  }
  @name("doSet")
    table doSet {
    actions = {
      set;
    }
    default_action = set(8w0);
  }
  apply {
    doSet.apply();
  }
}
control Wrapper(inout bit<8> value) {
  Wrapped() wrapped;
  apply {
    wrapped.apply(value);
  }
}
control c (inout bit<8> v);
package top (c _c);
top(Wrapper()) main;

************************\n******** p4c type checking result: ********\n************************\n
