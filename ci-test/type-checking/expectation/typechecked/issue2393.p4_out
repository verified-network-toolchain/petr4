/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2393.p4
\n
#include <core.p4>

header ethernet_t {
    bit<48> src_addr;
}

struct Headers {
    ethernet_t eth_hdr;
}

action do_global_action(in bool make_zero, out bool val_undefined) {
    bit<16> tmp;
    tmp = tmp *  (make_zero ? 16w0: 16w1);
}

control ingress(inout Headers h) {
    bool filler_bool = true;
    bool tmp_bool = false;
    action do_action() {
        do_global_action(tmp_bool, tmp_bool);
    }

    table simple_table {
        key = {
            h.eth_hdr.src_addr : exact;
        }
        actions = {
            do_action();
            do_global_action(true, filler_bool);
        }
    }
    apply {
        simple_table.apply();
    }
}

control c<H>(inout H h);
package top<H>(c<H> _c);

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
  bit<48> src_addr;
}
struct Headers {
  ethernet_t eth_hdr;
}
action do_global_action(in bool make_zero, out bool val_undefined)
  {
  bit<16> tmp;
  tmp = tmp*(make_zero ? 16w0 : 16w1);
}
control ingress(inout Headers h) {
  bool filler_bool = true;
  bool tmp_bool = false;
  action do_action() {
    do_global_action(tmp_bool, tmp_bool);
  }
  table simple_table
    {
    key = {
      h.eth_hdr.src_addr: exact;
    }
    actions = {
      do_action;do_global_action(true, filler_bool);
    }
  }
  apply {
    simple_table.apply();
  }
}
control c<H> (inout H h);
package top<H3> (c<H3> _c);
top(ingress()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2393.p4(11): [--Wwarn=unused] warning: 'val_undefined' is unused
action do_global_action(in bool make_zero, out bool val_undefined) {
                                                    ^^^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2393.p4(13): [--Wwarn=uninitialized_use] warning: tmp may be uninitialized
    tmp = tmp * (make_zero ? 16w0: 16w1);
          ^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2393.p4(11): [--Wwarn=uninitialized_out_param] warning: out parameter 'val_undefined' may be uninitialized when 'do_global_action' terminates
action do_global_action(in bool make_zero, out bool val_undefined) {
                                                    ^^^^^^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2393.p4(11)
action do_global_action(in bool make_zero, out bool val_undefined) {
       ^^^^^^^^^^^^^^^^
