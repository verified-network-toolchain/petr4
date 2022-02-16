/petr4/ci-test/type-checking/testdata/p4_16_samples/value-sets.p4
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

header Ethernet_h {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

struct Parsed_packet {
    Ethernet_h ethernet;
}

extern ValueSet {
    ValueSet(bit<32> size);
    bit<8> index(in bit<16> proto);
}

#define ETH_KIND_TRILL 1
#define ETH_KIND_TPID  2

parser TopParser(packet_in b, out Parsed_packet p) {
    ValueSet(5) ethtype_kinds;
    state start {
        b.extract(p.ethernet);
        transition select(p.ethernet.etherType) {
            16w0x0800: parse_ipv4;
            16w0x0806: parse_arp;
            16w0x86DD: parse_ipv6;
            default: dispatch_value_sets;
        }
    }

    state dispatch_value_sets {
        bit<8> setIndex = ethtype_kinds.index(p.ethernet.etherType);
        transition select(setIndex) {
            ETH_KIND_TRILL: parse_trill;
            ETH_KIND_TPID: parse_vlan_tag;
        }
    }

    state parse_ipv4     { transition accept; }
    state parse_arp      { transition accept; }
    state parse_ipv6     { transition accept; }
    state parse_trill    { transition accept; }
    state parse_vlan_tag { transition accept; }
}

parser proto<T>(packet_in p, out T h);
package top<T>(proto<T> _p);

top(TopParser()) main;
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
header Ethernet_h {
  bit<48> dstAddr;
  bit<48> srcAddr;
  bit<16> etherType;
}
struct Parsed_packet {
  Ethernet_h ethernet;
}
extern ValueSet {
  ValueSet(bit<32> size);
  bit<8> index(in bit<16> proto);
}

parser TopParser(packet_in b, out Parsed_packet p) {
  ValueSet(5) ethtype_kinds;
  state start
    {
    b.extract(p.ethernet);
    transition select(p.ethernet.etherType) {
      16w2048: parse_ipv4;
      16w2054: parse_arp;
      16w34525: parse_ipv6;
      default: dispatch_value_sets;
    }
  }
  state dispatch_value_sets
    {
    bit<8> setIndex = ethtype_kinds.index(p.ethernet.etherType);
    transition select(setIndex) {
      1: parse_trill;
      2: parse_vlan_tag;
    }
  }
  state parse_ipv4 {
    transition accept;
  }
  state parse_arp {
    transition accept;
  }
  state parse_ipv6 {
    transition accept;
  }
  state parse_trill {
    transition accept;
  }
  state parse_vlan_tag {
    transition accept;
  }
}
parser proto<T3> (packet_in p, out T3 h);
package top<T4> (proto<T4> _p);
top(TopParser()) main;

************************\n******** p4c type checking result: ********\n************************\n
