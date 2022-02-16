/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2905.p4
\n
#include <core.p4>

control c() {
    action a() {}
    table t {
        key = {}
        actions = {
            a;
        }
        const entries = {}
    }

    apply {
    }
}
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
control c() {
  action a() { 
  }
  table t {
    key = {
      
    }
    actions = {
      a;
    }
    const entries = {
      
    }
  }
  apply { 
  }
}

************************\n******** p4c type checking result: ********\n************************\n
