/petr4/ci-test/type-checking/testdata/p4_16_samples/states.p4
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

parser parse<H>(packet_in packet, out H headers);
package ebpfFilter<H>(parse<H> prs);

header Ethernet_h
{
    bit<64> dstAddr;
    bit<64> srcAddr;
    bit<16> etherType;
}

struct Headers_t
{
    Ethernet_h ethernet;
}

parser prs(packet_in p, out Headers_t headers)
{
    state start
    {
        p.extract(headers.ethernet);
        transition select(headers.ethernet.etherType)
        {
            16w0x800 : ip;
            default : reject;
        }
    }

    state ip
    {
        transition accept;
    }
}

ebpfFilter(prs()) main;
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
parser parse<H> (packet_in packet, out H headers);
package ebpfFilter<H3> (parse<H3> prs);
header Ethernet_h {
  bit<64> dstAddr;
  bit<64> srcAddr;
  bit<16> etherType;
}
struct Headers_t {
  Ethernet_h ethernet;
}
parser prs(packet_in p, out Headers_t headers) {
  state start
    {
    p.extract(headers.ethernet);
    transition select(headers.ethernet.etherType) {
      16w2048: ip;
      default: reject;
    }
  }
  state ip {
    transition accept;
  }
}
ebpfFilter(prs()) main;

************************\n******** p4c type checking result: ********\n************************\n
