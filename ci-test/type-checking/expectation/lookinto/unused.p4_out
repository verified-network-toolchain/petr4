/petr4/ci-test/type-checking/testdata/p4_16_samples/unused.p4
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

struct S {
    Header h;
}

extern E {
    E();
    bit<32> get<T>(in T b);
}

control c(inout S s) {
    E() e;
    apply {
        if (s.h.isValid())
            s.h.data3 = 0;
        if (s.h.data2 == 0)
            s.h.data1 = e.get(s.h.data2);
    }
}

parser proto(packet_in p, out Header h);
control cproto<T>(inout T v);
package top(cproto<_> _c);

top(c()) main;
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
struct S {
  Header h;
}
extern E {
  E();
  bit<32> get<T3>(in T3 b);
}

control c(inout S s) {
  E() e;
  apply
    {
    if (s.h.isValid()) 
      s.h.data3 = 0;
    if (s.h.data2==0) 
      s.h.data1 = e.get(s.h.data2);
  }
}
parser proto (packet_in p, out Header h);
control cproto<T4> (inout T4 v);
package top (cproto<_> _c);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
