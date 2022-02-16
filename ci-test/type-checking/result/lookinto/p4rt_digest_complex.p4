/petr4/ci-test/type-checking/testdata/p4_16_samples/p4rt_digest_complex.p4
\n
#include <core.p4>
#include <bmv2/psa.p4>

struct EMPTY { };

struct s_t {
    bit<8> f8;
    bit<16> f16;
}

header h_t {
    s_t s;
    bit<32> f32;
}

struct headers { h_t h; }

parser MyIP(
    packet_in buffer,
    out headers hdr,
    inout EMPTY b,
    in psa_ingress_parser_input_metadata_t c,
    in EMPTY d,
    in EMPTY e) {

    state start {
        buffer.extract(hdr.h);
        transition accept;
    }
}

parser MyEP(
    packet_in buffer,
    out EMPTY a,
    inout EMPTY b,
    in psa_egress_parser_input_metadata_t c,
    in EMPTY d,
    in EMPTY e,
    in EMPTY f) {
    state start {
        transition accept;
    }
}

control MyIC(
    inout headers hdr,
    inout EMPTY b,
    in psa_ingress_input_metadata_t c,
    inout psa_ingress_output_metadata_t d) {
    apply {
        d.egress_port = c.ingress_port;
    }
}

control MyEC(
    inout EMPTY a,
    inout EMPTY b,
    in psa_egress_input_metadata_t c,
    inout psa_egress_output_metadata_t d) {
    apply { }
}

struct digest_t {
    h_t h;
    PortId_t port;
}

control MyID(
    packet_out buffer,
    out EMPTY a,
    out EMPTY b,
    out EMPTY c,
    inout headers hdr,
    in EMPTY e,
    in psa_ingress_output_metadata_t f) {
    Digest<digest_t>() digest;
    apply {
        digest.pack({hdr.h, f.egress_port});
    }
}

control MyED(
    packet_out buffer,
    out EMPTY a,
    out EMPTY b,
    inout EMPTY c,
    in EMPTY d,
    in psa_egress_output_metadata_t e,
    in psa_egress_deparser_input_metadata_t f) {
    apply { }
}

IngressPipeline(MyIP(), MyIC(), MyID()) ip;
EgressPipeline(MyEP(), MyEC(), MyED()) ep;

PSA_Switch(
    ip,
    PacketReplicationEngine(),
    ep,
    BufferingQueueingEngine()) main;
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
struct EMPTY {
  
}
struct s_t {
  bit<8> f8;
  bit<16> f16;
}
header h_t {
  s_t s;
  bit<32> f32;
}
struct headers {
  h_t h;
}
parser MyIP(packet_in buffer, out headers hdr, inout EMPTY b,
            in psa_ingress_parser_input_metadata_t c, in EMPTY d, in EMPTY e) {
  state start {
    buffer.extract(hdr.h);
    transition accept;
  }
}
parser MyEP(packet_in buffer, out EMPTY a, inout EMPTY b,
            in psa_egress_parser_input_metadata_t c, in EMPTY d, in EMPTY e,
            in EMPTY f) {
  state start {
    transition accept;
  }
}
control MyIC(inout headers hdr, inout EMPTY b,
             in psa_ingress_input_metadata_t c,
             inout psa_ingress_output_metadata_t d) {
  apply {
    d.egress_port = c.ingress_port;
  }
}
control MyEC(inout EMPTY a, inout EMPTY b, in psa_egress_input_metadata_t c,
             inout psa_egress_output_metadata_t d) {
  apply { 
  }
}
struct digest_t {
  h_t h;
  PortId_t port;
}
control MyID(packet_out buffer, out EMPTY a, out EMPTY b, out EMPTY c,
             inout headers hdr, in EMPTY e,
             in psa_ingress_output_metadata_t f) {
  Digest<digest_t>() digest;
  apply {
    digest.pack({hdr.h, f.egress_port});
  }
}
control MyED(packet_out buffer, out EMPTY a, out EMPTY b, inout EMPTY c,
             in EMPTY d, in psa_egress_output_metadata_t e,
             in psa_egress_deparser_input_metadata_t f) {
  apply { 
  }
}
IngressPipeline(MyIP(), MyIC(), MyID()) ip;
EgressPipeline(MyEP(), MyEC(), MyED()) ep;
PSA_Switch(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine())
  main;

************************\n******** p4c type checking result: ********\n************************\n
