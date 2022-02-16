/petr4/ci-test/type-checking/testdata/p4_16_samples/vss-example.p4
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

// include the very simple switch declaration from the previous section
#include "very_simple_model.p4"

// This program processes packets composed of an Ethernet and
// an IPv4 header, performing forwarding based on the
// destination IP address

typedef bit<48>  EthernetAddress;
typedef bit<32>  IPv4Address;

// standard Ethernet header
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

// IPv4 header without options
header Ipv4_h {
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

// Parser section

// Declare user-defined errors that may be signaled during parsing
error {
    IPv4OptionsNotSupported,
    IPv4IncorrectVersion,
    IPv4ChecksumError
}

// List of all recognized headers
struct Parsed_packet {
    Ethernet_h ethernet;
    Ipv4_h     ip;
}

parser TopParser(packet_in b, out Parsed_packet p) {
    Ck16() ck;  // instantiate checksum unit

    state start {
        b.extract(p.ethernet);
        transition select(p.ethernet.etherType) {
            0x0800 : parse_ipv4;
            // no default rule: all other packets rejected
        }
    }

    state parse_ipv4 {
        b.extract(p.ip);
        verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
        verify(p.ip.ihl == 4w5, error.IPv4OptionsNotSupported);
        ck.clear();
        ck.update(p.ip);
        // Verify that packet checksum is zero
        verify(ck.get() == 16w0, error.IPv4ChecksumError);
        transition accept;
    }
}

// match-action pipeline section

control TopPipe(inout Parsed_packet headers,
                in error parseError, // parser error
                in InControl inCtrl, // input port
                out OutControl outCtrl) {
     /**
      * Indicates that a packet is dropped by setting the
      * output port to the DROP_PORT
      */
      action Drop_action()
      { outCtrl.outputPort = DROP_PORT; }

      IPv4Address nextHop;

     /**
      * Set the next hop and the output port.
      * Decrements ipv4 ttl field.
      * @param ivp4_dest ipv4 address of next hop
      * @param port output port
      */
      action Set_nhop(IPv4Address ipv4_dest, PortId port) {
          nextHop = ipv4_dest;
          headers.ip.ttl = headers.ip.ttl-1;
          outCtrl.outputPort = port;
      }

     /**
      * Computes address of next Ipv4 hop and output port
      * based on the Ipv4 destination of the current packet.
      * Decrements packet Ipv4 TTL.
      */
     table ipv4_match {
         key = { headers.ip.dstAddr : lpm; }
         actions = {
              Drop_action;
              Set_nhop;
         }

         size = 1024;
         default_action = Drop_action;
     }

     /**
      * Send the packet to the CPU port
      */
      action Send_to_cpu()
      { outCtrl.outputPort = CPU_OUT_PORT; }

     /**
      * Check packet TTL and send to CPU if expired.
      */
     table check_ttl {
         key = { headers.ip.ttl : exact; }
         actions = { Send_to_cpu; NoAction; }
         const default_action = NoAction; // defined in core.p4
     }

     /**
      * Set the destination MAC address of the packet
      * @param dmac destination MAC address.
      */
      action Set_dmac(EthernetAddress dmac)
      { headers.ethernet.dstAddr = dmac; }
     /**
      * Set the destination Ethernet address of the packet
      * based on the next hop IP address.
      */
      table dmac {
          key = { nextHop : exact; }
          actions = {
               Drop_action;
               Set_dmac;
          }
          size = 1024;
          default_action = Drop_action;
      }

      /**
       * Set the source MAC address.
       * @param smac: source MAC address to use
       */
       action Set_smac(EthernetAddress smac)
       { headers.ethernet.srcAddr = smac; }

      /**
       * Set the source mac address based on the output port.
       */
      table smac {
           key = { outCtrl.outputPort : exact; }
           actions = {
                Drop_action;
                Set_smac;
          }
          size = 16;
          default_action = Drop_action;
      }

      apply {
          if (parseError != error.NoError) {
               Drop_action();  // invoke drop directly
               return;
          }

          ipv4_match.apply(); // Match result will go into nextHop
          if (outCtrl.outputPort == DROP_PORT) return;

          check_ttl.apply();
          if (outCtrl.outputPort == CPU_OUT_PORT) return;

          dmac.apply();
          if (outCtrl.outputPort == DROP_PORT) return;

          smac.apply();
    }
}

// deparser section
control TopDeparser(inout Parsed_packet p, packet_out b) {
    Ck16() ck;
    apply {
        b.emit(p.ethernet);
        if (p.ip.isValid()) {
            ck.clear();                // prepare checksum unit
            p.ip.hdrChecksum = 16w0;   // clear checksum
            ck.update(p.ip);           // compute new checksum.
            p.ip.hdrChecksum = ck.get();
        }
        b.emit(p.ip);
    }
}

// Instantiate the top-level VSS package.
// use TopParser for the p Parser, etc.
VSS(TopParser(),
    TopPipe(),
    TopDeparser()) main;
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
typedef bit<4> PortId;
const PortId REAL_PORT_COUNT = 4w8;
struct InControl {
  PortId inputPort;
}
const PortId RECIRCULATE_IN_PORT = 13;
const PortId CPU_IN_PORT = 14;
struct OutControl {
  PortId outputPort;
}
const PortId DROP_PORT = 15;
const PortId CPU_OUT_PORT = 14;
const PortId RECIRCULATE_OUT_PORT = 13;
parser Parser<H> (packet_in b, out H parsedHeaders);
control Pipe<H3>
  (inout H3 headers,
   in error parseError,
   in InControl inCtrl,
   out OutControl outCtrl);
control Deparser<H4> (inout H4 outputHeaders, packet_out b);
package VSS<H5> (Parser<H5> p, Pipe<H5> map, Deparser<H5> d);
extern Ck16 {
  Ck16();
  void clear();
  void update<T6>(in T6 data);
  bit<16> get();
}

typedef bit<48> EthernetAddress;
typedef bit<32> IPv4Address;
header Ethernet_h {
  EthernetAddress dstAddr;
  EthernetAddress srcAddr;
  bit<16> etherType;
}
header Ipv4_h {
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
error {
  IPv4OptionsNotSupported, IPv4IncorrectVersion, IPv4ChecksumError
}
struct Parsed_packet {
  Ethernet_h ethernet;
  Ipv4_h ip;
}
parser TopParser(packet_in b, out Parsed_packet p) {
  Ck16() ck;
  state start
    {
    b.extract(p.ethernet);
    transition select(p.ethernet.etherType) {
      2048: parse_ipv4;
    }
  }
  state parse_ipv4
    {
    b.extract(p.ip);
    verify(p.ip.version==4w4, IPv4IncorrectVersion);
    verify(p.ip.ihl==4w5, IPv4OptionsNotSupported);
    ck.clear();
    ck.update(p.ip);
    verify(ck.get()==16w0, IPv4ChecksumError);
    transition accept;
  }
}
control TopPipe(inout Parsed_packet headers, in error parseError,
                in InControl inCtrl, out OutControl outCtrl) {
  action Drop_action() {
    outCtrl.outputPort = DROP_PORT;
  }
  IPv4Address nextHop;
  action Set_nhop(IPv4Address ipv4_dest, PortId port)
    {
    nextHop = ipv4_dest;
    headers.ip.ttl = headers.ip.ttl-1;
    outCtrl.outputPort = port;
  }
  table ipv4_match
    {
    key = {
      headers.ip.dstAddr: lpm;
    }
    actions = {
      Drop_action;Set_nhop;
    }
    size = 1024;
    default_action = Drop_action;
  }
  action Send_to_cpu() {
    outCtrl.outputPort = CPU_OUT_PORT;
  }
  table check_ttl
    {
    key = {
      headers.ip.ttl: exact;
    }
    actions = {
      Send_to_cpu;NoAction;
    }
    const default_action = NoAction;
  }
  action Set_dmac(EthernetAddress dmac) {
    headers.ethernet.dstAddr = dmac;
  }
  table dmac
    {
    key = {
      nextHop: exact;
    }
    actions = {
      Drop_action;Set_dmac;
    }
    size = 1024;
    default_action = Drop_action;
  }
  action Set_smac(EthernetAddress smac) {
    headers.ethernet.srcAddr = smac;
  }
  table smac
    {
    key = {
      outCtrl.outputPort: exact;
    }
    actions = {
      Drop_action;Set_smac;
    }
    size = 16;
    default_action = Drop_action;
  }
  apply
    {
    if (parseError!=NoError) {
      Drop_action();
      return;
    }
    ipv4_match.apply();
    if (outCtrl.outputPort==DROP_PORT) 
      return;
    check_ttl.apply();
    if (outCtrl.outputPort==CPU_OUT_PORT) 
      return;
    dmac.apply();
    if (outCtrl.outputPort==DROP_PORT) 
      return;
    smac.apply();
  }
}
control TopDeparser(inout Parsed_packet p, packet_out b) {
  Ck16() ck;
  apply
    {
    b.emit(p.ethernet);
    if (p.ip.isValid())
      {
      ck.clear();
      p.ip.hdrChecksum = 16w0;
      ck.update(p.ip);
      p.ip.hdrChecksum = ck.get();
    }
    b.emit(p.ip);
  }
}
VSS(TopParser(), TopPipe(), TopDeparser()) main;

