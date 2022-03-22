/petr4/ci-test/type-checking/testdata/p4_16_samples/chain1.p4
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

parser p1(packet_in p, out Header h) {
    bit x;
    state start {
        transition select (x) {
            0: chain1;
            1: chain2;
        }
    }

    state chain1 {
        p.extract(h);
        transition next1;
    }

    state next1 {
        transition endchain;
    }

    state chain2 {
        p.extract(h);
        transition next2;
    }

    state next2 {
        transition endchain;
    }

    state endchain {
        transition accept;
    }
}

parser proto(packet_in p, out Header h);
package top(proto _p);

top(p1()) main;
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
parser p1(packet_in p, out Header h) {
  bit<1> x;
  state start {
    transition select(x) {
      0: chain1;
      1: chain2;
    }
  }
  state chain1 {
    p.extract(h);
    transition next1;
  }
  state next1 {
    transition endchain;
  }
  state chain2 {
    p.extract(h);
    transition next2;
  }
  state next2 {
    transition endchain;
  }
  state endchain {
    transition accept;
  }
}
parser proto (packet_in p, out Header h);
package top (proto _p);
top(p1()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/chain1.p4(26): [--Wwarn=uninitialized_use] warning: x may be uninitialized
        transition select (x) {
                           ^
