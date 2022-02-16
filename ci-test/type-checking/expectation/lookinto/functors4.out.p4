/petr4/ci-test/type-checking/testdata/p4_16_samples/functors4.p4
\n
/*
Copyright 2013-present Barefoot Networks, Inc.

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

parser p1(out bit z1)(bit b1) {
    state start {
        z1 = b1;
        transition accept;
    }
}

parser p(out bit z) {
   p1(1w0) p1i;

   state start {
        p1i.apply(z);
        transition accept;
   }
}

parser simple(out bit z);
package m(simple n);

m(p()) main;
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
parser p1(out bit<1> z1)(bit<1> b1) {
  state start {
    z1 = b1;
    transition accept;
  }
}
parser p(out bit<1> z) {
  p1(1w0) p1i;
  state start {
    p1i.apply(z);
    transition accept;
  }
}
parser simple (out bit<1> z);
package m (simple n);
m(p()) main;

************************\n******** p4c type checking result: ********\n************************\n
