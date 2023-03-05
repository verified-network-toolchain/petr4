#include <core.p4>
/*
 * merge.p4
 *
 * Tables sharing a key which can be merged.
 */
control c(inout bit<32> hdr) {
  action nop() { }
  action a0() { hdr = 0; }
  action a1() { hdr = 1; }
  table t1 {
    key = { hdr : exact; }
    actions = { a0(); a1(); nop(); }
    const default_action = nop();
    const entries = {
      0x99: a0();
    }
  }
  table t2 {
    key = { hdr : exact; }
    actions = { a0(); a1(); nop(); }
    const default_action = nop();
    const entries = {
      0x98: a1();
    }
  }
  apply {
    t1.apply();
    t2.apply();
  }
}

control ctrl<T>(inout T h);
package p<T>(ctrl<T> ctrl);
p(c()) main;