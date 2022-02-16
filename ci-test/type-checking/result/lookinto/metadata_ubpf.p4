/petr4/ci-test/type-checking/testdata/p4_16_samples/metadata_ubpf.p4
\n
/*
Copyright 2019 Orange

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
#define UBPF_MODEL_VERSION 20200515
#include <ubpf_model.p4>

@ethernetaddress typedef bit<48> EthernetAddress;

// standard Ethernet header
header Ethernet_h
{
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16> etherType;
}

struct Headers_t
{
    Ethernet_h ethernet;
}

struct metadata {
    bit<16> etherType;
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        p.extract(headers.ethernet);
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {

    action fill_metadata() {
        meta.etherType = headers.ethernet.etherType;
    }

    table tbl {
        key = {
            headers.ethernet.etherType : exact;
        }
        actions = {
            fill_metadata;
            NoAction;
        }
    }

    action change_etherType() {
        // set etherType to IPv6. Just to show that metadata works.
        headers.ethernet.etherType = 0x86DD;
    }

    table meta_based_tbl {
        key = {
            meta.etherType : exact;
        }
        actions = {
            change_etherType;
            NoAction;
        }
    }

    apply {
        tbl.apply();
        meta_based_tbl.apply();
    }

}

control DeparserImpl(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit(headers.ethernet);
    }
}

ubpf(prs(), pipe(), DeparserImpl()) main;

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
const bit<32> __ubpf_model_version = 20200515;
enum ubpf_action {
  ABORT, 
  DROP, 
  PASS, 
  REDIRECT
}
struct standard_metadata {
  bit<32> input_port;
  bit<32> packet_length;
  ubpf_action output_action;
  bit<32> output_port;
  bool clone;
  bit<32> clone_port;
}
extern void mark_to_drop();
extern void mark_to_pass();
extern Register<T3, S> {
  Register(bit<32> size);
  T3 read(in S index);
  void write(in S index, in T3 value);
}

extern bit<48> ubpf_time_get_ns();
extern void truncate(in bit<32> len);
enum HashAlgorithm {
  lookup3
}
extern void hash<D>(out bit<32> result, in HashAlgorithm algo, in D data);
extern bit<16> csum_replace2(in bit<16> csum, in bit<16> old,
                             in bit<16> new);
extern bit<16> csum_replace4(in bit<16> csum, in bit<32> old,
                             in bit<32> new);
parser parse<H, M>
  (packet_in packet, out H headers, inout M meta, inout standard_metadata std);
control pipeline<H4, M5>
  (inout H4 headers, inout M5 meta, inout standard_metadata std);
@deparser
control deparser<H6> (packet_out b, in H6 headers);
package ubpf<H7, M8>
  (parse<H7, M8> prs, pipeline<H7, M8> p, deparser<H7> dprs);
@ethernetaddress
typedef bit<48> EthernetAddress;
header Ethernet_h {
  EthernetAddress dstAddr;
  EthernetAddress srcAddr;
  bit<16> etherType;
}
struct Headers_t {
  Ethernet_h ethernet;
}
struct metadata {
  bit<16> etherType;
}
parser prs(packet_in p, out Headers_t headers, inout metadata meta,
           inout standard_metadata std_meta) {
  state start {
    p.extract(headers.ethernet);
    transition accept;
  }
}
control pipe(inout Headers_t headers, inout metadata meta,
             inout standard_metadata std_meta) {
  action fill_metadata() {
    meta.etherType = headers.ethernet.etherType;
  }
  table tbl
    {
    key = {
      headers.ethernet.etherType: exact;
    }
    actions = {
      fill_metadata;NoAction;
    }
  }
  action change_etherType() {
    headers.ethernet.etherType = 34525;
  }
  table meta_based_tbl
    {
    key = {
      meta.etherType: exact;
    }
    actions = {
      change_etherType;NoAction;
    }
  }
  apply {
    tbl.apply();
    meta_based_tbl.apply();
  }
}
control DeparserImpl(packet_out packet, in Headers_t headers) {
  apply {
    packet.emit(headers.ethernet);
  }
}
ubpf(prs(), pipe(), DeparserImpl()) main;

