/petr4/ci-test/type-checking/testdata/p4_16_samples/factory2.p4
\n
/*
Copyright 2018 Barefoot Networks, Inc.

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

extern widget<T> { }

extern widget<T> createWidget<T, U>(U a, T b);

parser P();
parser p1()(widget<bit<8>> w) {
    state start { transition accept; } }

package sw0(P p);

sw0(p1(createWidget(16w0, 8w0))) main;
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
extern widget <T3> {
  }
extern widget<T4> createWidget<T4, U>(U a, T4 b);
parser P ();
parser p1()(widget<bit<8>> w) {
  state start {
    transition accept;
  }
}
package sw0 (P p);
sw0(p1(createWidget(16w0, 8w0))) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/factory2.p4(18): [--Wwarn=unused] warning: 'T' is unused
extern widget<T> { }
              ^