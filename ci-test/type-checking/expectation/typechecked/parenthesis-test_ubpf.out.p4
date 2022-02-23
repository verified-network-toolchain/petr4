/petr4/ci-test/type-checking/testdata/p4_16_samples/parenthesis-test_ubpf.p4
\n
/*
Copyright 2020 MNK Labs & Consulting

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

#include <ubpf_model.p4>

typedef bit<48> EthernetAddress;
typedef bit<32>     IPv4Address;

header Ethernet_h
{
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16> etherType;
}

header IPv4_h {
    bit<4>       version;
    bit<4>       ihl;
    bit<8>       diffserv;
    bit<16>      totalLen;
    bit<16>      identification;
    bit<3>       flags;
    bit<13>      fragOffset;
    bit<8>       ttl;
    bit<8>       protocol;
    bit<16>      hdrChecksum;
    IPv4Address  srcAddr;
    IPv4Address  dstAddr;
}

struct Headers_t
{
    Ethernet_h ethernet;
    IPv4_h     ipv4;
}

struct metadata {
    bit<8> qfi;
    bit<8> filt_dir;
    bit<8> reflec_qos;
}

parser prs(packet_in p, out Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {
    state start {
        p.extract(headers.ethernet);
        transition select(headers.ethernet.etherType) {
            16w0x800 : ipv4;
            default : reject;
        }
    }

    state ipv4 {
        p.extract(headers.ipv4);
        transition accept;
    }
}

control pipe(inout Headers_t headers, inout metadata meta, inout standard_metadata std_meta) {

    action Reject() {
        mark_to_drop();
    }

    table filter_tbl {
        key = {
            headers.ipv4.srcAddr : exact;
        }
        actions = {
            Reject;
            NoAction;
        }

        default_action = NoAction;
    }

    apply {
        if (headers.ipv4.isValid())
            filter_tbl.apply();
        if ((meta.qfi != 0) &&
            ((meta.filt_dir == 2) ||
             (meta.reflec_qos == 1)))
	     meta.qfi = 3;
    }
}

control dprs(packet_out packet, in Headers_t headers) {
    apply {
        packet.emit(headers.ethernet);
        packet.emit(headers.ipv4);
    }
}


ubpf(prs(), pipe(), dprs()) main;
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
typedef bit<48> EthernetAddress;
typedef bit<32> IPv4Address;
header Ethernet_h {
  EthernetAddress dstAddr;
  EthernetAddress srcAddr;
  bit<16> etherType;
}
header IPv4_h {
  bit<4> version;
  bit<4> ihl;
  bit<8> diffserv;
  bit<16> totalLen;
  bit<16> identification;
  bit<3> flags;
  bit<13> fragOffset;
  bit<8> ttl;
  bit<8> protocol;
  bit<16> hdrChecksum;
  IPv4Address srcAddr;
  IPv4Address dstAddr;
}
struct Headers_t {
  Ethernet_h ethernet;
  IPv4_h ipv4;
}
struct metadata {
  bit<8> qfi;
  bit<8> filt_dir;
  bit<8> reflec_qos;
}
parser prs(packet_in p, out Headers_t headers, inout metadata meta,
           inout standard_metadata std_meta) {
  state start
    {
    p.extract(headers.ethernet);
    transition select(headers.ethernet.etherType) {
      16w2048: ipv4;
      default: reject;
    }
  }
  state ipv4 {
    p.extract(headers.ipv4);
    transition accept;
  }
}
control pipe(inout Headers_t headers, inout metadata meta,
             inout standard_metadata std_meta) {
  action Reject() {
    mark_to_drop();
  }
  table filter_tbl
    {
    key = {
      headers.ipv4.srcAddr: exact;
    }
    actions = {
      Reject;NoAction;
    }
    default_action = NoAction;
  }
  apply
    {
    if (headers.ipv4.isValid()) 
      filter_tbl.apply();
    if (meta.qfi!=0 && meta.filt_dir==2 || meta.reflec_qos==1) 
      meta.qfi = 3;
  }
}
control dprs(packet_out packet, in Headers_t headers) {
  apply {
    packet.emit(headers.ethernet);
    packet.emit(headers.ipv4);
  }
}
ubpf(prs(), pipe(), dprs()) main;

************************\n******** p4c type checking result: ********\n************************\n
