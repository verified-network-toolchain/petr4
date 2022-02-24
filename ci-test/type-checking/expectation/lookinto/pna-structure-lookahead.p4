/petr4/ci-test/type-checking/testdata/p4_16_samples/pna-structure-lookahead.p4
\n
/*
Copyright 2021 Intel Corporation

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
#include <pna.p4>

struct my_struct_t {
    bit<8> type1;
    bit<8> type2;
}

header my_header_t {
    bit<8> type1;
    bit<8> type2;
    bit<8> value;
}

struct main_metadata_t {
}

struct headers_t {
    my_header_t h;
}

parser MainParserImpl(
          packet_in                        pkt,
    out   headers_t                        hdr,
    inout main_metadata_t                  main_meta,
    in    pna_main_parser_input_metadata_t istd)
{
    state start {
        my_struct_t tmp = pkt.lookahead<my_struct_t>();
        transition select(tmp.type2) {
            8w01: parse_header;
            default: accept;
        }
    }

    state parse_header {
        pkt.extract(hdr.h);
        transition accept;
    }
}

control PreControlImpl(
    in    headers_t                 hdr,
    inout main_metadata_t           meta,
    in    pna_pre_input_metadata_t  istd,
    inout pna_pre_output_metadata_t ostd)
{
    apply {}
}

control MainControlImpl(
    inout headers_t                  hdr,
    inout main_metadata_t            user_meta,
    in    pna_main_input_metadata_t  istd,
    inout pna_main_output_metadata_t ostd)
{
    apply {
    }
}

control MainDeparserImpl(
       packet_out                 pkt,
    in headers_t                  hdr,
    in main_metadata_t            user_meta,
    in pna_main_output_metadata_t ostd)
{
    apply {
    }
}

PNA_NIC(
    MainParserImpl(),
    PreControlImpl(),
    MainControlImpl(),
    MainDeparserImpl()
    ) main;
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
typedef bit<32> InterfaceIdUint_t;
typedef bit<32> MulticastGroupUint_t;
typedef bit<16> MirrorSessionIdUint_t;
typedef bit<8> MirrorSlotIdUint_t;
typedef bit<8> ClassOfServiceUint_t;
typedef bit<16> PacketLengthUint_t;
typedef bit<16> MulticastInstanceUint_t;
typedef bit<64> TimestampUint_t;
typedef bit<32> FlowIdUint_t;
typedef bit<8> ExpireTimeProfileIdUint_t;
typedef bit<3> PassNumberUint_t;
typedef bit<32> SecurityAssocIdUint_t;
@p4runtime_translation("p4.org/pna/v1/PortId_t", 32)
  type PortIdUint_t PortId_t;
@p4runtime_translation("p4.org/pna/v1/InterfaceId_t", 32)
  type InterfaceIdUint_t InterfaceId_t;
@p4runtime_translation("p4.org/pna/v1/MulticastGroup_t", 32)
  type MulticastGroupUint_t MulticastGroup_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSessionId_t", 16)
  type MirrorSessionIdUint_t MirrorSessionId_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSlotId_t", 8)
  type MirrorSlotIdUint_t MirrorSlotId_t;
@p4runtime_translation("p4.org/pna/v1/ClassOfService_t", 8)
  type ClassOfServiceUint_t ClassOfService_t;
@p4runtime_translation("p4.org/pna/v1/PacketLength_t", 16)
  type PacketLengthUint_t PacketLength_t;
@p4runtime_translation("p4.org/pna/v1/MulticastInstance_t", 16)
  type MulticastInstanceUint_t MulticastInstance_t;
@p4runtime_translation("p4.org/pna/v1/Timestamp_t", 64)
  type TimestampUint_t Timestamp_t;
@p4runtime_translation("p4.org/pna/v1/FlowId_t", 32)
  type FlowIdUint_t FlowId_t;
@p4runtime_translation("p4.org/pna/v1/ExpireTimeProfileId_t", 8)
  type ExpireTimeProfileIdUint_t ExpireTimeProfileId_t;
@p4runtime_translation("p4.org/pna/v1/PassNumber_t", 8)
  type PassNumberUint_t PassNumber_t;
@p4runtime_translation("p4.org/pna/v1/SecurityAssocId_t", 64)
  type SecurityAssocIdUint_t SecurityAssocId_t;
typedef error ParserError_t;
const InterfaceId_t PNA_PORT_CPU = (InterfaceId_t) 4294967293;
const MirrorSessionId_t PNA_MIRROR_SESSION_TO_CPU = (MirrorSessionId_t) 0;
typedef bit<32> PortIdInHeaderUint_t;
typedef bit<32> InterfaceIdInHeaderUint_t;
typedef bit<32> MulticastGroupInHeaderUint_t;
typedef bit<16> MirrorSessionIdInHeaderUint_t;
typedef bit<8> MirrorSlotIdInHeaderUint_t;
typedef bit<8> ClassOfServiceInHeaderUint_t;
typedef bit<16> PacketLengthInHeaderUint_t;
typedef bit<16> MulticastInstanceInHeaderUint_t;
typedef bit<64> TimestampInHeaderUint_t;
typedef bit<32> FlowIdInHeaderUint_t;
typedef bit<8> ExpireTimeProfileIdInHeaderUint_t;
typedef bit<8> PassNumberInHeaderUint_t;
typedef bit<32> SecurityAssocIdInHeaderUint_t;
@p4runtime_translation("p4.org/pna/v1/PortIdInHeader_t", 32)
  type PortIdInHeaderUint_t PortIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/InterfaceIdInHeader_t", 32)
  type InterfaceIdInHeaderUint_t InterfaceIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MulticastGroupInHeader_t", 32)
  type MulticastGroupInHeaderUint_t MulticastGroupInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSessionIdInHeader_t", 16)
  type MirrorSessionIdInHeaderUint_t MirrorSessionIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSlotIdInHeader_t", 8)
  type MirrorSlotIdInHeaderUint_t MirrorSlotIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/ClassOfServiceInHeader_t", 8)
  type ClassOfServiceInHeaderUint_t ClassOfServiceInHeader_t;
@p4runtime_translation("p4.org/pna/v1/PacketLengthInHeader_t", 16)
  type PacketLengthInHeaderUint_t PacketLengthInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MulticastInstanceInHeader_t", 16)
  type MulticastInstanceInHeaderUint_t MulticastInstanceInHeader_t;
@p4runtime_translation("p4.org/pna/v1/TimestampInHeader_t", 64)
  type TimestampInHeaderUint_t TimestampInHeader_t;
@p4runtime_translation("p4.org/pna/v1/FlowIdInHeader_t", 32)
  type FlowIdInHeaderUint_t FlowIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/ExpireTimeProfileIdInHeader_t", 8)
  type ExpireTimeProfileIdInHeaderUint_t ExpireTimeProfileIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/PassNumberInHeader_t", 8)
  type PassNumberInHeaderUint_t PassNumberInHeader_t;
@p4runtime_translation("p4.org/pna/v1/SecurityAssocIdInHeader_t", 64)
  type SecurityAssocIdInHeaderUint_t SecurityAssocIdInHeader_t;
PortId_t pna_PortId_header_to_int (in PortIdInHeader_t x)
  {
  return (PortId_t) (PortIdUint_t) (PortIdInHeaderUint_t) x;
}
InterfaceId_t pna_InterfaceId_header_to_int (in InterfaceIdInHeader_t x)
  {
  return (InterfaceId_t) (InterfaceIdUint_t) (InterfaceIdInHeaderUint_t) x;
}
MulticastGroup_t pna_MulticastGroup_header_to_int
  (in MulticastGroupInHeader_t x)
  {
  return
  (MulticastGroup_t) (MulticastGroupUint_t) (MulticastGroupInHeaderUint_t) x;
}
MirrorSessionId_t pna_MirrorSessionId_header_to_int
  (in MirrorSessionIdInHeader_t x)
  {
  return
  (MirrorSessionId_t) (MirrorSessionIdUint_t) (MirrorSessionIdInHeaderUint_t) x;
}
ClassOfService_t pna_ClassOfService_header_to_int
  (in ClassOfServiceInHeader_t x)
  {
  return
  (ClassOfService_t) (ClassOfServiceUint_t) (ClassOfServiceInHeaderUint_t) x;
}
PacketLength_t pna_PacketLength_header_to_int (in PacketLengthInHeader_t x)
  {
  return
  (PacketLength_t) (PacketLengthUint_t) (PacketLengthInHeaderUint_t) x;
}
MulticastInstance_t pna_MulticastInstance_header_to_int
  (in MulticastInstanceInHeader_t x)
  {
  return
  (MulticastInstance_t) (MulticastInstanceUint_t) (MulticastInstanceInHeaderUint_t) x;
}
Timestamp_t pna_Timestamp_header_to_int (in TimestampInHeader_t x)
  {
  return (Timestamp_t) (TimestampUint_t) (TimestampInHeaderUint_t) x;
}
FlowId_t pna_FlowId_header_to_int (in FlowIdInHeader_t x)
  {
  return (FlowId_t) (FlowIdUint_t) (FlowIdInHeaderUint_t) x;
}
ExpireTimeProfileId_t pna_ExpireTimeProfileId_header_to_int
  (in ExpireTimeProfileIdInHeader_t x)
  {
  return
  (ExpireTimeProfileId_t) (ExpireTimeProfileIdUint_t) (ExpireTimeProfileIdInHeaderUint_t) x;
}
PassNumber_t pna_PassNumber_header_to_int (in PassNumberInHeader_t x)
  {
  return (PassNumber_t) (PassNumberUint_t) (PassNumberInHeaderUint_t) x;
}
PortIdInHeader_t pna_PortId_int_to_header (in PortId_t x)
  {
  return (PortIdInHeader_t) (PortIdInHeaderUint_t) (PortIdUint_t) x;
}
InterfaceIdInHeader_t pna_InterfaceId_int_to_header (in InterfaceId_t x)
  {
  return
  (InterfaceIdInHeader_t) (InterfaceIdInHeaderUint_t) (InterfaceIdUint_t) x;
}
MulticastGroupInHeader_t pna_MulticastGroup_int_to_header
  (in MulticastGroup_t x)
  {
  return
  (MulticastGroupInHeader_t) (MulticastGroupInHeaderUint_t) (MulticastGroupUint_t) x;
}
MirrorSessionIdInHeader_t pna_MirrorSessionId_int_to_header
  (in MirrorSessionId_t x)
  {
  return
  (MirrorSessionIdInHeader_t) (MirrorSessionIdInHeaderUint_t) (MirrorSessionIdUint_t) x;
}
ClassOfServiceInHeader_t pna_ClassOfService_int_to_header
  (in ClassOfService_t x)
  {
  return
  (ClassOfServiceInHeader_t) (ClassOfServiceInHeaderUint_t) (ClassOfServiceUint_t) x;
}
PacketLengthInHeader_t pna_PacketLength_int_to_header (in PacketLength_t x)
  {
  return
  (PacketLengthInHeader_t) (PacketLengthInHeaderUint_t) (PacketLengthUint_t) x;
}
MulticastInstanceInHeader_t pna_MulticastInstance_int_to_header
  (in MulticastInstance_t x)
  {
  return
  (MulticastInstanceInHeader_t) (MulticastInstanceInHeaderUint_t) (MulticastInstanceUint_t) x;
}
TimestampInHeader_t pna_Timestamp_int_to_header (in Timestamp_t x)
  {
  return (TimestampInHeader_t) (TimestampInHeaderUint_t) (TimestampUint_t) x;
}
FlowIdInHeader_t pna_FlowId_int_to_header (in FlowId_t x)
  {
  return (FlowIdInHeader_t) (FlowIdInHeaderUint_t) (FlowIdUint_t) x;
}
ExpireTimeProfileIdInHeader_t pna_ExpireTimeProfileId_int_to_header
  (in ExpireTimeProfileId_t x)
  {
  return
  (ExpireTimeProfileIdInHeader_t) (ExpireTimeProfileIdInHeaderUint_t) (ExpireTimeProfileIdUint_t) x;
}
PassNumberInHeader_t pna_PassNumber_int_to_header (in PassNumber_t x)
  {
  return
  (PassNumberInHeader_t) (PassNumberInHeaderUint_t) (PassNumberUint_t) x;
}
enum PNA_IdleTimeout_t {
  NO_TIMEOUT, 
  NOTIFY_CONTROL
}
match_kind {
  range, selector
}
enum PNA_HashAlgorithm_t {
  TARGET_DEFAULT
}
extern Hash<O> {
  Hash(PNA_HashAlgorithm_t algo);
  O get_hash<D>(in D data);
  O get_hash<T3, D4>(in T3 base, in D4 data, in T3 max);
}

extern Checksum<W> {
  Checksum(PNA_HashAlgorithm_t hash);
  void clear();
  void update<T5>(in T5 data);
  W get();
}

extern InternetChecksum {
  InternetChecksum();
  void clear();
  void add<T6>(in T6 data);
  void subtract<T7>(in T7 data);
  bit<16> get();
  bit<16> get_state();
  void set_state(in bit<16> checksum_state);
}

enum PNA_CounterType_t {
  PACKETS, 
  BYTES, 
  PACKETS_AND_BYTES
}
extern Counter<W8, S> {
  Counter(bit<32> n_counters, PNA_CounterType_t type);
  void count(in S index);
}

extern DirectCounter<W9> {
  DirectCounter(PNA_CounterType_t type);
  void count();
}

enum PNA_MeterType_t {
  PACKETS, 
  BYTES
}
enum PNA_MeterColor_t {
  RED, 
  GREEN, 
  YELLOW
}
extern Meter<S10> {
  Meter(bit<32> n_meters, PNA_MeterType_t type);
  PNA_MeterColor_t execute(in S10 index, in PNA_MeterColor_t color);
  PNA_MeterColor_t execute(in S10 index);
}

extern DirectMeter {
  DirectMeter(PNA_MeterType_t type);
  PNA_MeterColor_t execute(in PNA_MeterColor_t color);
  PNA_MeterColor_t execute();
}

extern Register<T11, S12> {
  Register(bit<32> size);
  Register(bit<32> size, T11 initial_value);
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
  ActionSelector(PNA_HashAlgorithm_t algo, bit<32> size, bit<32> outputWidth);
}

extern Digest<T14> {
  Digest();
  void pack(in T14 data);
}

enum PNA_Direction_t {
  NET_TO_HOST, 
  HOST_TO_NET
}
enum PNA_PacketPath_t {
  FROM_NET_PORT, 
  FROM_NET_LOOPEDBACK, 
  FROM_NET_RECIRCULATED, 
  FROM_HOST, 
  FROM_HOST_LOOPEDBACK, 
  FROM_HOST_RECIRCULATED
}
struct pna_pre_input_metadata_t {
  PortId_t input_port;
  ParserError_t parser_error;
  PNA_Direction_t direction;
  PassNumber_t pass;
  bool loopedback;
}
struct pna_pre_output_metadata_t {
  bool decrypt;
  SecurityAssocId_t said;
  bit<16> decrypt_start_offset;
}
struct pna_main_parser_input_metadata_t {
  PNA_Direction_t direction;
  PassNumber_t pass;
  bool loopedback;
  PortId_t input_port;
}
struct pna_main_input_metadata_t {
  PNA_Direction_t direction;
  PassNumber_t pass;
  bool loopedback;
  Timestamp_t timestamp;
  ParserError_t parser_error;
  ClassOfService_t class_of_service;
  PortId_t input_port;
}
struct pna_main_output_metadata_t {
  ClassOfService_t class_of_service;
}
extern void drop_packet();
extern void send_to_port(PortId_t dest_port);
extern void mirror_packet(MirrorSlotId_t mirror_slot_id,
                          MirrorSessionId_t mirror_session_id);
extern bool add_entry<T15>(string action_name, in T15 action_params);
extern FlowId_t allocate_flow_id();
extern void set_entry_expire_time(in ExpireTimeProfileId_t
                                  expire_time_profile_id);
extern void restart_expire_timer();
@pure
extern T16 SelectByDirection<T16>(in PNA_Direction_t direction,
                                  in T16 n2h_value, in T16 h2n_value);
control PreControlT<PH, PM>
  (in PH pre_hdr,
   inout PM pre_user_meta,
   in pna_pre_input_metadata_t istd,
   inout pna_pre_output_metadata_t ostd);
parser MainParserT<PM17, MH, MM>
  (packet_in pkt,
   out MH main_hdr,
   inout MM main_user_meta,
   in pna_main_parser_input_metadata_t istd);
control MainControlT<PM18, MH19, MM20>
  (inout MH19 main_hdr,
   inout MM20 main_user_meta,
   in pna_main_input_metadata_t istd,
   inout pna_main_output_metadata_t ostd);
control MainDeparserT<MH21, MM22>
  (packet_out pkt,
   in MH21 main_hdr,
   in MM22 main_user_meta,
   in pna_main_output_metadata_t ostd);
package PNA_NIC<PH23, PM24, MH25, MM26>
  (MainParserT<PM24, MH25, MM26> main_parser,
   PreControlT<PH23, PM24> pre_control,
   MainControlT<PM24, MH25, MM26> main_control,
   MainDeparserT<MH25, MM26> main_deparser);
struct my_struct_t {
  bit<8> type1;
  bit<8> type2;
}
header my_header_t {
  bit<8> type1;
  bit<8> type2;
  bit<8> value;
}
struct main_metadata_t {
  
}
struct headers_t {
  my_header_t h;
}
parser MainParserImpl(packet_in pkt, out headers_t hdr,
                      inout main_metadata_t main_meta,
                      in pna_main_parser_input_metadata_t istd) {
  state start
    {
    my_struct_t tmp = pkt.lookahead<my_struct_t>();
    transition select(tmp.type2) {
      8w1: parse_header;
      default: accept;
    }
  }
  state parse_header {
    pkt.extract(hdr.h);
    transition accept;
  }
}
control PreControlImpl(in headers_t hdr, inout main_metadata_t meta,
                       in pna_pre_input_metadata_t istd,
                       inout pna_pre_output_metadata_t ostd) {
  apply { 
  }
}
control MainControlImpl(inout headers_t hdr, inout main_metadata_t user_meta,
                        in pna_main_input_metadata_t istd,
                        inout pna_main_output_metadata_t ostd) {
  apply { 
  }
}
control MainDeparserImpl(packet_out pkt, in headers_t hdr,
                         in main_metadata_t user_meta,
                         in pna_main_output_metadata_t ostd) {
  apply { 
  }
}
PNA_NIC(MainParserImpl(), PreControlImpl(), MainControlImpl(),
          MainDeparserImpl())
  main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/p4include/pna.p4(373): [--Wwarn=unused] warning: 'W' is unused
extern Counter<W, S> {
               ^
/petr4/ci-test/type-checking/p4include/pna.p4(380): [--Wwarn=unused] warning: 'W' is unused
extern DirectCounter<W> {
                     ^
/petr4/ci-test/type-checking/p4include/pna.p4(673): [--Wwarn=unused] warning: 'PM' is unused
parser MainParserT<PM, MH, MM>(
                   ^^
/petr4/ci-test/type-checking/p4include/pna.p4(680): [--Wwarn=unused] warning: 'PM' is unused
control MainControlT<PM, MH, MM>(
                     ^^
