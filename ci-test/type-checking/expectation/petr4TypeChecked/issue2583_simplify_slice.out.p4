/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2583_simplify_slice.p4
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
    bit<32> data;
}

parser p(packet_in pckt, out Header h) {
    state start {

        h.data = 0;
        h.data[3:0] = 2;    // skipped

        h.data = 7;
        h.data[7:0] = 4;    // skipped
        h.data[7:0] = 3;    // skipped
        h.data[15:0] = 8;   // stays
        h.data[31:16] = 5;  // stays

        transition accept;
    }
}

parser proto(packet_in pckt, out Header h);
package top(proto _p);

top(p()) main;
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
  bit<32> data;
}
parser p(packet_in pckt, out Header h) {
  state start
    {
    h.data = 0;
    h.data[3:0] = 2;
    h.data = 7;
    h.data[7:0] = 4;
    h.data[7:0] = 3;
    h.data[15:0] = 8;
    h.data[31:16] = 5;
    transition accept;
  }
}
parser proto (packet_in pckt, out Header h);
package top (proto _p);
top(p()) main;

************************\n******** p4c type checking result: ********\n************************\n
