/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4
\n
/*
Copyright 2016 VMware, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <core.p4>

header Header {
    bit<32> data1;
    bit<32> data2;
    bit<32> data3;
}

extern void func(in Header h);
extern bit<32> g(inout bit<32> v, in bit<32> w);

parser p1(packet_in p, out Header h) {
    Header[2] stack;
    bool b;
    bool c;
    bool d;
    state start {
        h.data1 = 0;
        func(h);  // uninitialized
        g(h.data2, g(h.data2, h.data2));  // uninitialized
        transition next;
    }

    state next {
        h.data2 = h.data3 + 1;  // uninitialized
        stack[0] = stack[1];  // uninitialized
        b = stack[1].isValid();
        transition select (h.isValid()) {
            true: next1;
            false: next2;
        }
    }

    state next1 {
        d = false;
        transition next3;
    }

    state next2 {
        c = true;
        d = c;
        transition next3;
    }

    state next3 {
        c = !c;  // uninitialized;
        d = !d;
        transition accept;
    }
}

control c(out bit<32> v) {  // uninitialized
    bit<32> b;
    bit<32> d = 1;
    bit<32> setByAction;

    action a1() { setByAction = 1; }
    action a2() { setByAction = 1; }

    table t {
        actions = { a1; a2; }
        default_action = a1();
    }

    apply {
        b = b + 1;  // uninitialized
        d = d + 1;
        bit<32> e;
        bit<32> f;
        if (e > 0) {  // uninitialized
            e = 1;
            f = 2;
        } else {
            f = 3;
        }
        e = e + 1;  // uninitialized
        bool touched;
        switch (t.apply().action_run) {
            a1: { touched = true; }
        }
        touched = !touched;  // uninitialized
        if (e > 0)
            t.apply();
        else
            a1();
        setByAction = setByAction + 1;
    }
}

parser proto(packet_in p, out Header h);
control cproto(out bit<32> v);
package top(proto _p, cproto _c);

top(p1(), c()) main;
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
header Header {
  bit<32> data1;
  bit<32> data2;
  bit<32> data3;
}
extern void func(in Header h);
extern bit<32> g(inout bit<32> v, in bit<32> w);
parser p1(packet_in p, out Header h) {
  Header[2] stack;
  bool b;
  bool c;
  bool d;
  state start {
    h.data1 = 0;
    func(h);
    g(h.data2, g(h.data2, h.data2));
    transition next;
  }
  state next
    {
    h.data2 = h.data3+1;
    stack[0] = stack[1];
    b = stack[1].isValid();
    transition select(h.isValid()) {
      true: next1;
      false: next2;
    }
  }
  state next1 {
    d = false;
    transition next3;
  }
  state next2 {
    c = true;
    d = c;
    transition next3;
  }
  state next3 {
    c = !c;
    d = !d;
    transition accept;
  }
}
control c(out bit<32> v) {
  bit<32> b;
  bit<32> d = 1;
  bit<32> setByAction;
  action a1() {
    setByAction = 1;
  }
  action a2() {
    setByAction = 1;
  }
  table t {
    actions = {
      a1;a2;
    }
    default_action = a1();
  }
  apply {
    b = b+1;
    d = d+1;
    bit<32> e;
    bit<32> f;
    if (e>0) {
      e = 1;
      f = 2;
    }else {
    f = 3;
    }
    e = e+1;
    bool touched;
    switch (t.apply().action_run) {
    a1:
    {
    touched = true;
    }
    }
    touched = !touched;
    if (e>0) 
      t.apply();
      else
        a1();
    setByAction = setByAction+1;
  }
}
parser proto (packet_in p, out Header h);
control cproto (out bit<32> v);
package top (proto _p, cproto _c);
top(p1(), c()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=ordering] warning: h.data2: 'out' argument has fields in common with h.data2
        g(h.data2, g(h.data2, h.data2)); // uninitialized
          ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36)
        g(h.data2, g(h.data2, h.data2)); // uninitialized
                     ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(35): [--Wwarn=uninitialized_use] warning: h may not be completely initialized
        func(h); // uninitialized
             ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=uninitialized_use] warning: h.data2 may be uninitialized
        g(h.data2, g(h.data2, h.data2)); // uninitialized
          ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=uninitialized_use] warning: h.data2 may be uninitialized
        g(h.data2, g(h.data2, h.data2)); // uninitialized
                              ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=uninitialized_use] warning: h.data2 may be uninitialized
        g(h.data2, g(h.data2, h.data2)); // uninitialized
                     ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(41): [--Wwarn=uninitialized_use] warning: h.data3 may be uninitialized
        h.data2 = h.data3 + 1; // uninitialized
                  ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(42): [--Wwarn=uninitialized_use] warning: stack[1] may not be completely initialized
        stack[0] = stack[1]; // uninitialized
                   ^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(62): [--Wwarn=uninitialized_use] warning: c may be uninitialized
        c = !c; // uninitialized;
             ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(34): [--Wwarn=invalid_header] warning: accessing a field of an invalid header h
        h.data1 = 0;
        ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=invalid_header] warning: accessing a field of an invalid header h
        g(h.data2, g(h.data2, h.data2)); // uninitialized
          ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=invalid_header] warning: accessing a field of an invalid header h
        g(h.data2, g(h.data2, h.data2)); // uninitialized
                              ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(36): [--Wwarn=invalid_header] warning: accessing a field of an invalid header h
        g(h.data2, g(h.data2, h.data2)); // uninitialized
                     ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(41): [--Wwarn=invalid_header] warning: accessing a field of an invalid header h
        h.data2 = h.data3 + 1; // uninitialized
        ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(41): [--Wwarn=invalid_header] warning: accessing a field of an invalid header h
        h.data2 = h.data3 + 1; // uninitialized
                  ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(82): [--Wwarn=uninitialized_use] warning: b may be uninitialized
        b = b + 1; // uninitialized
            ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(86): [--Wwarn=uninitialized_use] warning: e may be uninitialized
        if (e > 0) { // uninitialized
            ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(92): [--Wwarn=uninitialized_use] warning: e may be uninitialized
        e = e + 1; // uninitialized
            ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(97): [--Wwarn=uninitialized_use] warning: touched may be uninitialized
        touched = !touched; // uninitialized
                   ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(68): [--Wwarn=uninitialized_out_param] warning: out parameter 'v' may be uninitialized when 'c' terminates
control c(out bit<32> v) { // uninitialized
                      ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/uninit.p4(68)
control c(out bit<32> v) { // uninitialized
        ^
