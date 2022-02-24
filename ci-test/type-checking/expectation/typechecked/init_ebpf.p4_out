/petr4/ci-test/type-checking/testdata/p4_16_samples/init_ebpf.p4
\n
/*
Copyright 2018 VMware, Inc.

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
#include <ebpf_model.p4>

header Ethernet {
    bit<48> destination;
    bit<48> source;
    bit<16> protocol;
}

struct Headers_t {
    Ethernet ethernet;
}

parser prs(packet_in p, out Headers_t headers) {
    state start {
        p.extract(headers.ethernet);
        transition accept;
    }
}

control pipe(inout Headers_t headers, out bool pass) {
    action match(bool act)
    {
        pass = act;
    }

    table tbl {
        key = { headers.ethernet.protocol : exact; }
        actions = {
            match; NoAction;
        }

        const entries = {
            (0x0800) : match(true);
            (0xD000) : match(false);
        }

        implementation = hash_table(64);
    }

    apply {
        pass = true;
        tbl.apply();
    }
}

ebpfFilter(prs(), pipe()) main;
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
extern CounterArray {
  CounterArray(bit<32> max_index, bool sparse);
  void increment(in bit<32> index);
  void add(in bit<32> index, in bit<32> value);
}

extern array_table {
  array_table(bit<32> size);
}

extern hash_table {
  hash_table(bit<32> size);
}

parser parse<H> (packet_in packet, out H headers);
control filter<H3> (inout H3 headers, out bool accept);
package ebpfFilter<H4> (parse<H4> prs, filter<H4> filt);
header Ethernet {
  bit<48> destination;
  bit<48> source;
  bit<16> protocol;
}
struct Headers_t {
  Ethernet ethernet;
}
parser prs(packet_in p, out Headers_t headers) {
  state start {
    p.extract(headers.ethernet);
    transition accept;
  }
}
control pipe(inout Headers_t headers, out bool pass) {
  action match(bool act) {
    pass = act;
  }
  table tbl
    {
    key = {
      headers.ethernet.protocol: exact;
    }
    actions = {
      match;NoAction;
    }
    const entries = {
      2048: match(true);
      53248: match(false);
    }
    implementation = hash_table(64);
  }
  apply {
    pass = true;
    tbl.apply();
  }
}
ebpfFilter(prs(), pipe()) main;

************************\n******** p4c type checking result: ********\n************************\n
