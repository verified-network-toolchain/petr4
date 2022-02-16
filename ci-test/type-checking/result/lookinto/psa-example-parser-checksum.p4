/petr4/ci-test/type-checking/testdata/p4_16_samples/psa-example-parser-checksum.p4
\n
/*
Copyright 2017 Cisco Systems, Inc.

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
#include <bmv2/psa.p4>


typedef bit<48>  EthernetAddress;

header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}

header tcp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<32> seqNo;
    bit<32> ackNo;
    bit<4>  dataOffset;
    bit<3>  res;
    bit<3>  ecn;
    bit<6>  ctrl;
    bit<16> window;
    bit<16> checksum;
    bit<16> urgentPtr;
}

struct empty_metadata_t {
}

struct fwd_metadata_t {
}

struct metadata {
    fwd_metadata_t fwd_metadata;
}

struct headers {
    ethernet_t       ethernet;
    ipv4_t           ipv4;
    tcp_t            tcp;
}


// BEGIN:Parse_Error_Example
// Define additional error values, one of them for packets with
// incorrect IPv4 header checksums.
error {
    UnhandledIPv4Options,
    BadIPv4HeaderChecksum
}

typedef bit<32> PacketCounter_t;
typedef bit<8>  ErrorIndex_t;

const bit<9> NUM_ERRORS = 256;

parser IngressParserImpl(packet_in buffer,
                         out headers hdr,
                         inout metadata user_meta,
                         in psa_ingress_parser_input_metadata_t istd,
                         in empty_metadata_t resubmit_meta,
                         in empty_metadata_t recirculate_meta)
{
    InternetChecksum() ck;
    state start {
        buffer.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            0x0800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        buffer.extract(hdr.ipv4);
        // TBD: It would be good to enhance this example to
        // demonstrate checking of IPv4 header checksums for IPv4
        // headers with options, but this example does not handle such
        // packets.
        verify(hdr.ipv4.ihl == 5, error.UnhandledIPv4Options);
        ck.clear();
        ck.add({
            /* 16-bit word  0   */ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv,
            /* 16-bit word  1   */ hdr.ipv4.totalLen,
            /* 16-bit word  2   */ hdr.ipv4.identification,
            /* 16-bit word  3   */ hdr.ipv4.flags, hdr.ipv4.fragOffset,
            /* 16-bit word  4   */ hdr.ipv4.ttl, hdr.ipv4.protocol,
            /* 16-bit word  5 skip hdr.ipv4.hdrChecksum, */
            /* 16-bit words 6-7 */ hdr.ipv4.srcAddr,
            /* 16-bit words 8-9 */ hdr.ipv4.dstAddr
            });
        // The verify statement below will cause the parser to enter
        // the reject state, and thus terminate parsing immediately,
        // if the IPv4 header checksum is wrong.  It will also record
        // the error error.BadIPv4HeaderChecksum, which will be
        // available in a metadata field in the ingress control block.
        verify(ck.get() == hdr.ipv4.hdrChecksum,
               error.BadIPv4HeaderChecksum);
        transition select(hdr.ipv4.protocol) {
            6: parse_tcp;
            default: accept;
        }
    }
    state parse_tcp {
        buffer.extract(hdr.tcp);
        transition accept;
    }
}

control ingress(inout headers hdr,
                inout metadata user_meta,
                in    psa_ingress_input_metadata_t  istd,
                inout psa_ingress_output_metadata_t ostd)
{
    // Table parser_error_count_and_convert below shows one way to
    // count the number of times each parser error was encountered.
    // Although it is not used in this example program, it also shows
    // how to convert the error value into a unique bit vector value
    // 'error_idx', which can be useful if you wish to put a bit
    // vector encoding of an error into a packet header, e.g. for a
    // packet sent to the control CPU.

    DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts;
    ErrorIndex_t error_idx;

    action set_error_idx (ErrorIndex_t idx) {
        error_idx = idx;
        parser_error_counts.count();
    }
    table parser_error_count_and_convert {
        key = {
            istd.parser_error : exact;
        }
        actions = {
            set_error_idx;
        }
        default_action = set_error_idx(0);
        const entries = {
            error.NoError               : set_error_idx(1);
            error.PacketTooShort        : set_error_idx(2);
            error.NoMatch               : set_error_idx(3);
            error.StackOutOfBounds      : set_error_idx(4);
            error.HeaderTooShort        : set_error_idx(5);
            error.ParserTimeout         : set_error_idx(6);
            error.BadIPv4HeaderChecksum : set_error_idx(7);
            error.UnhandledIPv4Options  : set_error_idx(8);
        }
        psa_direct_counter = parser_error_counts;
    }
    apply {
        if (istd.parser_error != error.NoError) {
            // Example code showing how to count number of times each
            // kind of parser error was seen.
            parser_error_count_and_convert.apply();
            ingress_drop(ostd);
            exit;
        }
        // Do normal packet processing here.
    }
}
// END:Parse_Error_Example

parser EgressParserImpl(packet_in buffer,
                        out headers hdr,
                        inout metadata user_meta,
                        in psa_egress_parser_input_metadata_t istd,
                        in empty_metadata_t normal_meta,
                        in empty_metadata_t clone_i2e_meta,
                        in empty_metadata_t clone_e2e_meta)
{
    state start {
        transition accept;
    }
}

control egress(inout headers hdr,
               inout metadata user_meta,
               in    psa_egress_input_metadata_t  istd,
               inout psa_egress_output_metadata_t ostd)
{
    apply { }
}

control IngressDeparserImpl(packet_out packet,
                            out empty_metadata_t clone_i2e_meta,
                            out empty_metadata_t resubmit_meta,
                            out empty_metadata_t normal_meta,
                            inout headers hdr,
                            in metadata meta,
                            in psa_ingress_output_metadata_t istd)
{
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.tcp);
    }
}

// BEGIN:Compute_New_IPv4_Checksum_Example
control EgressDeparserImpl(packet_out packet,
                           out empty_metadata_t clone_e2e_meta,
                           out empty_metadata_t recirculate_meta,
                           inout headers hdr,
                           in metadata meta,
                           in psa_egress_output_metadata_t istd,
                           in psa_egress_deparser_input_metadata_t edstd)
{
    InternetChecksum() ck;
    apply {
        ck.clear();
        ck.add({
            /* 16-bit word  0   */ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv,
            /* 16-bit word  1   */ hdr.ipv4.totalLen,
            /* 16-bit word  2   */ hdr.ipv4.identification,
            /* 16-bit word  3   */ hdr.ipv4.flags, hdr.ipv4.fragOffset,
            /* 16-bit word  4   */ hdr.ipv4.ttl, hdr.ipv4.protocol,
            /* 16-bit word  5 skip hdr.ipv4.hdrChecksum, */
            /* 16-bit words 6-7 */ hdr.ipv4.srcAddr,
            /* 16-bit words 8-9 */ hdr.ipv4.dstAddr
            });
        hdr.ipv4.hdrChecksum = ck.get();
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.tcp);
    }
}
// END:Compute_New_IPv4_Checksum_Example

IngressPipeline(IngressParserImpl(),
                ingress(),
                IngressDeparserImpl()) ip;

EgressPipeline(EgressParserImpl(),
               egress(),
               EgressDeparserImpl()) ep;

PSA_Switch(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;
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
typedef bit<32> PortIdUint_t;
typedef bit<32> MulticastGroupUint_t;
typedef bit<16> CloneSessionIdUint_t;
typedef bit<8> ClassOfServiceUint_t;
typedef bit<16> PacketLengthUint_t;
typedef bit<16> EgressInstanceUint_t;
typedef bit<64> TimestampUint_t;
@p4runtime_translation("p4.org/psa/v1/PortId_t", 32)
  type PortIdUint_t PortId_t;
@p4runtime_translation("p4.org/psa/v1/MulticastGroup_t", 32)
  type MulticastGroupUint_t MulticastGroup_t;
@p4runtime_translation("p4.org/psa/v1/CloneSessionId_t", 16)
  type CloneSessionIdUint_t CloneSessionId_t;
@p4runtime_translation("p4.org/psa/v1/ClassOfService_t", 8)
  type ClassOfServiceUint_t ClassOfService_t;
@p4runtime_translation("p4.org/psa/v1/PacketLength_t", 16)
  type PacketLengthUint_t PacketLength_t;
@p4runtime_translation("p4.org/psa/v1/EgressInstance_t", 16)
  type EgressInstanceUint_t EgressInstance_t;
@p4runtime_translation("p4.org/psa/v1/Timestamp_t", 64)
  type TimestampUint_t Timestamp_t;
typedef error ParserError_t;
const PortId_t PSA_PORT_RECIRCULATE = (PortId_t) 4294967290;
const PortId_t PSA_PORT_CPU = (PortId_t) 4294967293;
const CloneSessionId_t PSA_CLONE_SESSION_TO_CPU = (CloneSessionId_t) 0;
typedef bit<32> PortIdInHeaderUint_t;
typedef bit<32> MulticastGroupInHeaderUint_t;
typedef bit<16> CloneSessionIdInHeaderUint_t;
typedef bit<8> ClassOfServiceInHeaderUint_t;
typedef bit<16> PacketLengthInHeaderUint_t;
typedef bit<16> EgressInstanceInHeaderUint_t;
typedef bit<64> TimestampInHeaderUint_t;
@p4runtime_translation("p4.org/psa/v1/PortIdInHeader_t", 32)
  type PortIdInHeaderUint_t PortIdInHeader_t;
@p4runtime_translation("p4.org/psa/v1/MulticastGroupInHeader_t", 32)
  type MulticastGroupInHeaderUint_t MulticastGroupInHeader_t;
@p4runtime_translation("p4.org/psa/v1/CloneSessionIdInHeader_t", 16)
  type CloneSessionIdInHeaderUint_t CloneSessionIdInHeader_t;
@p4runtime_translation("p4.org/psa/v1/ClassOfServiceInHeader_t", 8)
  type ClassOfServiceInHeaderUint_t ClassOfServiceInHeader_t;
@p4runtime_translation("p4.org/psa/v1/PacketLengthInHeader_t", 16)
  type PacketLengthInHeaderUint_t PacketLengthInHeader_t;
@p4runtime_translation("p4.org/psa/v1/EgressInstanceInHeader_t", 16)
  type EgressInstanceInHeaderUint_t EgressInstanceInHeader_t;
@p4runtime_translation("p4.org/psa/v1/TimestampInHeader_t", 64)
  type TimestampInHeaderUint_t TimestampInHeader_t;
PortId_t psa_PortId_header_to_int (in PortIdInHeader_t x)
  {
  return (PortId_t) (PortIdUint_t) (PortIdInHeaderUint_t) x;
}
MulticastGroup_t psa_MulticastGroup_header_to_int
  (in MulticastGroupInHeader_t x)
  {
  return
  (MulticastGroup_t) (MulticastGroupUint_t) (MulticastGroupInHeaderUint_t) x;
}
CloneSessionId_t psa_CloneSessionId_header_to_int
  (in CloneSessionIdInHeader_t x)
  {
  return
  (CloneSessionId_t) (CloneSessionIdUint_t) (CloneSessionIdInHeaderUint_t) x;
}
ClassOfService_t psa_ClassOfService_header_to_int
  (in ClassOfServiceInHeader_t x)
  {
  return
  (ClassOfService_t) (ClassOfServiceUint_t) (ClassOfServiceInHeaderUint_t) x;
}
PacketLength_t psa_PacketLength_header_to_int (in PacketLengthInHeader_t x)
  {
  return
  (PacketLength_t) (PacketLengthUint_t) (PacketLengthInHeaderUint_t) x;
}
EgressInstance_t psa_EgressInstance_header_to_int
  (in EgressInstanceInHeader_t x)
  {
  return
  (EgressInstance_t) (EgressInstanceUint_t) (EgressInstanceInHeaderUint_t) x;
}
Timestamp_t psa_Timestamp_header_to_int (in TimestampInHeader_t x)
  {
  return (Timestamp_t) (TimestampUint_t) (TimestampInHeaderUint_t) x;
}
PortIdInHeader_t psa_PortId_int_to_header (in PortId_t x)
  {
  return (PortIdInHeader_t) (PortIdInHeaderUint_t) (PortIdUint_t) x;
}
MulticastGroupInHeader_t psa_MulticastGroup_int_to_header
  (in MulticastGroup_t x)
  {
  return
  (MulticastGroupInHeader_t) (MulticastGroupInHeaderUint_t) (MulticastGroupUint_t) x;
}
CloneSessionIdInHeader_t psa_CloneSessionId_int_to_header
  (in CloneSessionId_t x)
  {
  return
  (CloneSessionIdInHeader_t) (CloneSessionIdInHeaderUint_t) (CloneSessionIdUint_t) x;
}
ClassOfServiceInHeader_t psa_ClassOfService_int_to_header
  (in ClassOfService_t x)
  {
  return
  (ClassOfServiceInHeader_t) (ClassOfServiceInHeaderUint_t) (ClassOfServiceUint_t) x;
}
PacketLengthInHeader_t psa_PacketLength_int_to_header (in PacketLength_t x)
  {
  return
  (PacketLengthInHeader_t) (PacketLengthInHeaderUint_t) (PacketLengthUint_t) x;
}
EgressInstanceInHeader_t psa_EgressInstance_int_to_header
  (in EgressInstance_t x)
  {
  return
  (EgressInstanceInHeader_t) (EgressInstanceInHeaderUint_t) (EgressInstanceUint_t) x;
}
TimestampInHeader_t psa_Timestamp_int_to_header (in Timestamp_t x)
  {
  return (TimestampInHeader_t) (TimestampInHeaderUint_t) (TimestampUint_t) x;
}
enum PSA_IdleTimeout_t {
  NO_TIMEOUT, 
  NOTIFY_CONTROL
}
enum PSA_PacketPath_t {
  NORMAL, 
  NORMAL_UNICAST, 
  NORMAL_MULTICAST, 
  CLONE_I2E, 
  CLONE_E2E, 
  RESUBMIT, 
  RECIRCULATE
}
struct psa_ingress_parser_input_metadata_t {
  PortId_t ingress_port;
  PSA_PacketPath_t packet_path;
}
struct psa_egress_parser_input_metadata_t {
  PortId_t egress_port;
  PSA_PacketPath_t packet_path;
}
struct psa_ingress_input_metadata_t {
  PortId_t ingress_port;
  PSA_PacketPath_t packet_path;
  Timestamp_t ingress_timestamp;
  ParserError_t parser_error;
}
struct psa_ingress_output_metadata_t {
  ClassOfService_t class_of_service;
  bool clone;
  CloneSessionId_t clone_session_id;
  bool drop;
  bool resubmit;
  MulticastGroup_t multicast_group;
  PortId_t egress_port;
}
struct psa_egress_input_metadata_t {
  ClassOfService_t class_of_service;
  PortId_t egress_port;
  PSA_PacketPath_t packet_path;
  EgressInstance_t instance;
  Timestamp_t egress_timestamp;
  ParserError_t parser_error;
}
struct psa_egress_deparser_input_metadata_t {
  PortId_t egress_port;
}
struct psa_egress_output_metadata_t {
  bool clone;
  CloneSessionId_t clone_session_id;
  bool drop;
}
@pure
extern bool psa_clone_i2e(in psa_ingress_output_metadata_t istd);
@pure
extern bool psa_resubmit(in psa_ingress_output_metadata_t istd);
@pure
extern bool psa_normal(in psa_ingress_output_metadata_t istd);
@pure
extern bool psa_clone_e2e(in psa_egress_output_metadata_t istd);
@pure
extern bool psa_recirculate(in psa_egress_output_metadata_t istd,
                            in psa_egress_deparser_input_metadata_t edstd);
extern void assert(in bool check);
extern void assume(in bool check);
match_kind {
  range, selector, optional
}
@noWarnUnused
action
  send_to_port(inout psa_ingress_output_metadata_t meta,
               in PortId_t egress_port)
  {
  meta.drop = false;
  meta.multicast_group = (MulticastGroup_t) 0;
  meta.egress_port = egress_port;
}
@noWarnUnused
action
  multicast(inout psa_ingress_output_metadata_t meta,
            in MulticastGroup_t multicast_group)
  {
  meta.drop = false;
  meta.multicast_group = multicast_group;
}
@noWarnUnused
action ingress_drop(inout psa_ingress_output_metadata_t meta)
  {
  meta.drop = true;
}
@noWarnUnused
action egress_drop(inout psa_egress_output_metadata_t meta)
  {
  meta.drop = true;
}
extern PacketReplicationEngine {
  PacketReplicationEngine();
}

extern BufferingQueueingEngine {
  BufferingQueueingEngine();
}

enum PSA_HashAlgorithm_t {
  IDENTITY, 
  CRC32, 
  CRC32_CUSTOM, 
  CRC16, 
  CRC16_CUSTOM, 
  ONES_COMPLEMENT16, 
  TARGET_DEFAULT
}
extern Hash<O> {
  Hash(PSA_HashAlgorithm_t algo);
  @pure
  O get_hash<D>(in D data);
  @pure
  O get_hash<T3, D4>(in T3 base, in D4 data, in T3 max);
}

extern Checksum<W> {
  Checksum(PSA_HashAlgorithm_t hash);
  void clear();
  void update<T5>(in T5 data);
  @noSideEffects
  W get();
}

extern InternetChecksum {
  InternetChecksum();
  void clear();
  void add<T6>(in T6 data);
  void subtract<T7>(in T7 data);
  @noSideEffects
  bit<16> get();
  @noSideEffects
  bit<16> get_state();
  void set_state(in bit<16> checksum_state);
}

enum PSA_CounterType_t {
  PACKETS, 
  BYTES, 
  PACKETS_AND_BYTES
}
extern Counter<W8, S> {
  Counter(bit<32> n_counters, PSA_CounterType_t type);
  void count(in S index);
}

extern DirectCounter<W9> {
  DirectCounter(PSA_CounterType_t type);
  void count();
}

enum PSA_MeterType_t {
  PACKETS, 
  BYTES
}
enum PSA_MeterColor_t {
  RED, 
  GREEN, 
  YELLOW
}
extern Meter<S10> {
  Meter(bit<32> n_meters, PSA_MeterType_t type);
  PSA_MeterColor_t execute(in S10 index, in PSA_MeterColor_t color);
  PSA_MeterColor_t execute(in S10 index);
}

extern DirectMeter {
  DirectMeter(PSA_MeterType_t type);
  PSA_MeterColor_t execute(in PSA_MeterColor_t color);
  PSA_MeterColor_t execute();
}

extern Register<T11, S12> {
  Register(bit<32> size);
  Register(bit<32> size, T11 initial_value);
  @noSideEffects
  T11 read(in S12 index);
  void write(in S12 index, in T11 value);
}

extern Random<T13> {
  Random(T13 min, T13 max);
  T13 read();
}

extern ActionProfile {
  ActionProfile(bit<32> size);
}

extern ActionSelector {
  ActionSelector(PSA_HashAlgorithm_t algo, bit<32> size, bit<32> outputWidth);
}

extern Digest<T14> {
  Digest();
  void pack(in T14 data);
}

parser IngressParser<H, M, RESUBM, RECIRCM>
  (packet_in buffer,
   out H parsed_hdr,
   inout M user_meta,
   in psa_ingress_parser_input_metadata_t istd,
   in RESUBM resubmit_meta,
   in RECIRCM recirculate_meta);
control Ingress<H15, M16>
  (inout H15 hdr,
   inout M16 user_meta,
   in psa_ingress_input_metadata_t istd,
   inout psa_ingress_output_metadata_t ostd);
control IngressDeparser<H17, M18, CI2EM, RESUBM19, NM>
  (packet_out buffer,
   out CI2EM clone_i2e_meta,
   out RESUBM19 resubmit_meta,
   out NM normal_meta,
   inout H17 hdr,
   in M18 meta,
   in psa_ingress_output_metadata_t istd);
parser EgressParser<H20, M21, NM22, CI2EM23, CE2EM>
  (packet_in buffer,
   out H20 parsed_hdr,
   inout M21 user_meta,
   in psa_egress_parser_input_metadata_t istd,
   in NM22 normal_meta,
   in CI2EM23 clone_i2e_meta,
   in CE2EM clone_e2e_meta);
control Egress<H24, M25>
  (inout H24 hdr,
   inout M25 user_meta,
   in psa_egress_input_metadata_t istd,
   inout psa_egress_output_metadata_t ostd);
control EgressDeparser<H26, M27, CE2EM28, RECIRCM29>
  (packet_out buffer,
   out CE2EM28 clone_e2e_meta,
   out RECIRCM29 recirculate_meta,
   inout H26 hdr,
   in M27 meta,
   in psa_egress_output_metadata_t istd,
   in psa_egress_deparser_input_metadata_t edstd);
package IngressPipeline<IH, IM, NM30, CI2EM31, RESUBM32, RECIRCM33>
  (IngressParser<IH, IM, RESUBM32, RECIRCM33> ip,
   Ingress<IH, IM> ig,
   IngressDeparser<IH, IM, CI2EM31, RESUBM32, NM30> id);
package EgressPipeline<EH, EM, NM34, CI2EM35, CE2EM36, RECIRCM37>
  (EgressParser<EH, EM, NM34, CI2EM35, CE2EM36> ep,
   Egress<EH, EM> eg,
   EgressDeparser<EH, EM, CE2EM36, RECIRCM37> ed);
package PSA_Switch<IH38, IM39, EH40, EM41, NM42, CI2EM43, CE2EM44, RESUBM45,
  RECIRCM46>
  (IngressPipeline<IH38, IM39, NM42, CI2EM43, RESUBM45, RECIRCM46> ingress,
   PacketReplicationEngine pre,
   EgressPipeline<EH40, EM41, NM42, CI2EM43, CE2EM44, RECIRCM46> egress,
   BufferingQueueingEngine bqe);
typedef bit<48> EthernetAddress;
header ethernet_t {
  EthernetAddress dstAddr;
  EthernetAddress srcAddr;
  bit<16> etherType;
}
header ipv4_t {
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
  bit<32> srcAddr;
  bit<32> dstAddr;
}
header tcp_t {
  bit<16> srcPort;
  bit<16> dstPort;
  bit<32> seqNo;
  bit<32> ackNo;
  bit<4> dataOffset;
  bit<3> res;
  bit<3> ecn;
  bit<6> ctrl;
  bit<16> window;
  bit<16> checksum;
  bit<16> urgentPtr;
}
struct empty_metadata_t {
  
}
struct fwd_metadata_t {
  
}
struct metadata {
  fwd_metadata_t fwd_metadata;
}
struct headers {
  ethernet_t ethernet;
  ipv4_t ipv4;
  tcp_t tcp;
}
error {
  UnhandledIPv4Options, BadIPv4HeaderChecksum
}
typedef bit<32> PacketCounter_t;
typedef bit<8> ErrorIndex_t;
const bit<9> NUM_ERRORS = 256;
parser IngressParserImpl(packet_in buffer, out headers hdr,
                         inout metadata user_meta,
                         in psa_ingress_parser_input_metadata_t istd,
                         in empty_metadata_t resubmit_meta,
                         in empty_metadata_t recirculate_meta) {
  InternetChecksum() ck;
  state start
    {
    buffer.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType) {
      2048: parse_ipv4;
      default: accept;
    }
  }
  state parse_ipv4
    {
    buffer.extract(hdr.ipv4);
    verify(hdr.ipv4.ihl==5, UnhandledIPv4Options);
    ck.clear();
    ck.add({hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv,
             hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags,
             hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol,
             hdr.ipv4.srcAddr, hdr.ipv4.dstAddr});
    verify(ck.get()==hdr.ipv4.hdrChecksum, BadIPv4HeaderChecksum);
    transition select(hdr.ipv4.protocol) {
      6: parse_tcp;
      default: accept;
    }
  }
  state parse_tcp {
    buffer.extract(hdr.tcp);
    transition accept;
  }
}
control ingress(inout headers hdr, inout metadata user_meta,
                in psa_ingress_input_metadata_t istd,
                inout psa_ingress_output_metadata_t ostd) {
  DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS)
    parser_error_counts;
  ErrorIndex_t error_idx;
  action set_error_idx(ErrorIndex_t idx)
    {
    error_idx = idx;
    parser_error_counts.count();
  }
  table parser_error_count_and_convert
    {
    key = {
      istd.parser_error: exact;
    }
    actions = {
      set_error_idx;
    }
    default_action = set_error_idx(0);
    const entries =
      {
      NoError: set_error_idx(1);
      PacketTooShort: set_error_idx(2);
      NoMatch: set_error_idx(3);
      StackOutOfBounds: set_error_idx(4);
      HeaderTooShort: set_error_idx(5);
      ParserTimeout: set_error_idx(6);
      BadIPv4HeaderChecksum: set_error_idx(7);
      UnhandledIPv4Options: set_error_idx(8);
    }
    psa_direct_counter = parser_error_counts;
  }
  apply
    {
    if (istd.parser_error!=NoError)
      {
      parser_error_count_and_convert.apply();
      ingress_drop(ostd);
      exit;
    }
  }
}
parser EgressParserImpl(packet_in buffer, out headers hdr,
                        inout metadata user_meta,
                        in psa_egress_parser_input_metadata_t istd,
                        in empty_metadata_t normal_meta,
                        in empty_metadata_t clone_i2e_meta,
                        in empty_metadata_t clone_e2e_meta) {
  state start {
    transition accept;
  }
}
control egress(inout headers hdr, inout metadata user_meta,
               in psa_egress_input_metadata_t istd,
               inout psa_egress_output_metadata_t ostd) {
  apply { 
  }
}
control IngressDeparserImpl(packet_out packet,
                            out empty_metadata_t clone_i2e_meta,
                            out empty_metadata_t resubmit_meta,
                            out empty_metadata_t normal_meta,
                            inout headers hdr, in metadata meta,
                            in psa_ingress_output_metadata_t istd) {
  apply
    {
    packet.emit(hdr.ethernet);
    packet.emit(hdr.ipv4);
    packet.emit(hdr.tcp);
  }
}
control EgressDeparserImpl(packet_out packet,
                           out empty_metadata_t clone_e2e_meta,
                           out empty_metadata_t recirculate_meta,
                           inout headers hdr, in metadata meta,
                           in psa_egress_output_metadata_t istd,
                           in psa_egress_deparser_input_metadata_t edstd) {
  InternetChecksum() ck;
  apply
    {
    ck.clear();
    ck.add({hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv,
             hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags,
             hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol,
             hdr.ipv4.srcAddr, hdr.ipv4.dstAddr});
    hdr.ipv4.hdrChecksum = ck.get();
    packet.emit(hdr.ethernet);
    packet.emit(hdr.ipv4);
    packet.emit(hdr.tcp);
  }
}
IngressPipeline(IngressParserImpl(), ingress(), IngressDeparserImpl()) ip;
EgressPipeline(EgressParserImpl(), egress(), EgressDeparserImpl()) ep;
PSA_Switch(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine())
  main;

