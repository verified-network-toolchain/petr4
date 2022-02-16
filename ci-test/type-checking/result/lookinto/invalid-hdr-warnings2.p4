/petr4/ci-test/type-checking/testdata/p4_16_samples/invalid-hdr-warnings2.p4
\n
#include <core.p4>
#define V1MODEL_VERSION 20200408
#include <v1model.p4>

header Header {
    bit<32> data;
}

struct H {
    Header h1;
    Header h2;
}

struct M { }

parser ParserI(packet_in pkt, out H hdr, inout M meta, inout standard_metadata_t smeta) {
    state start {
        transition accept;
    }
}

control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    Header h1;
    Header h2;
    H s1;
    H s2;

    action invalid_H(inout H s) {
        s.h1.setInvalid();
        s.h2.setInvalid();
    }

    apply {
        h1 = { 1 };
        if (hdr.h1.data == 0) {
            h2 = h1;
        } else {
            h2.setValid();
            h2.data = 0;
        }

        hdr.h1.data = h1.data;      // h1 valid at this point
        hdr.h2.data = h2.data;      // h2 valid at this point

        if (h2.data == 1) {
            h1.setInvalid();
        }

        hdr.h1.data = h1.data;      // h1 potentially invalid at this point
        h1 = h2;                    // h1 valid again

        if (h1.data == 1) {
            s1 = { h1, h2 };
            s2 = s1;
            if (s2.h1.data == 0 && s2.h2.data == 0) {
                if (s1.h1.data > 0)
                    s1.h1.setInvalid();
                else
                    s1.h1.setInvalid();
                hdr.h1.data = s1.h1.data;   // s1.h1 invalid at this point
            } else {
                s1.h1.setValid();
            }
            hdr.h2.data = s1.h1.data;       // s1.h1 potentially invalid at this point
        }

        invalid_H(hdr);

        hdr.h1.data = 1;            //  hdr.h1 invalid at this point
        hdr.h2.data = 1;            //  hdr.h2 invalid at this point
    }
}

control EgressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
    apply {
    }
}

control DeparserI(packet_out pk, in H hdr) {
    apply {
    }
}

control VerifyChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}

control ComputeChecksumI(inout H hdr, inout M meta) {
    apply {
    }
}

V1Switch(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;

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
match_kind {
  range, optional, selector
}
const bit<32> __v1model_version = 20200408;
typedef bit<9> PortId_t;
@metadata
@name("standard_metadata")
struct standard_metadata_t {
  PortId_t ingress_port;
  PortId_t egress_spec;
  PortId_t egress_port;
  bit<32> instance_type;
  bit<32> packet_length;
  @alias("queueing_metadata.enq_timestamp")
  bit<32> enq_timestamp;
  @alias("queueing_metadata.enq_qdepth")
  bit<19> enq_qdepth;
  @alias("queueing_metadata.deq_timedelta")
  bit<32> deq_timedelta;
  @alias("queueing_metadata.deq_qdepth")
  bit<19>
  deq_qdepth;
  @alias("intrinsic_metadata.ingress_global_timestamp")
  bit<48>
  ingress_global_timestamp;
  @alias("intrinsic_metadata.egress_global_timestamp")
  bit<48>
  egress_global_timestamp;
  @alias("intrinsic_metadata.mcast_grp")
  bit<16> mcast_grp;
  @alias("intrinsic_metadata.egress_rid")
  bit<16> egress_rid;
  bit<1> checksum_error;
  error parser_error;
  @alias("intrinsic_metadata.priority")
  bit<3> priority;
}
enum CounterType {
  packets, 
  bytes, 
  packets_and_bytes
}
enum MeterType {
  packets, 
  bytes
}
extern counter<I> {
  counter(bit<32> size, CounterType type);
  void count(in I index);
}

extern direct_counter {
  direct_counter(CounterType type);
  void count();
}

extern meter<I3> {
  meter(bit<32> size, MeterType type);
  void execute_meter<T4>(in I3 index, out T4 result);
}

extern direct_meter<T5> {
  direct_meter(MeterType type);
  void read(out T5 result);
}

extern register<T6, I7> {
  register(bit<32> size);
  @noSideEffects
  void read(out T6 result, in I7 index);
  void write(in I7 index, in T6 value);
}

extern action_profile {
  action_profile(bit<32> size);
}

extern void random<T8>(out T8 result, in T8 lo, in T8 hi);
extern void digest<T9>(in bit<32> receiver, in T9 data);
enum HashAlgorithm {
  crc32, 
  crc32_custom, 
  crc16, 
  crc16_custom, 
  random, 
  identity, 
  csum16, 
  xor16
}
@deprecated("Please use mark_to_drop(standard_metadata) instead.")
extern void mark_to_drop();
@pure
extern void mark_to_drop(inout standard_metadata_t standard_metadata);
@pure
extern void hash<O, T10, D, M11>(out O result, in HashAlgorithm algo,
                                 in T10 base, in D data, in M11 max);
extern action_selector {
  action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

enum CloneType {
  I2E, 
  E2E
}
@deprecated("Please use verify_checksum/update_checksum instead.")
extern Checksum16 {
  Checksum16();
  bit<16> get<D12>(in D12 data);
}

extern void verify_checksum<T13, O14>(in bool condition, in T13 data,
                                      in O14 checksum, HashAlgorithm algo);
@pure
extern void update_checksum<T15, O16>(in bool condition, in T15 data,
                                      inout O16 checksum,
                                      HashAlgorithm algo);
extern void verify_checksum_with_payload<T17, O18>(in bool condition,
                                                   in T17 data,
                                                   in O18 checksum,
                                                   HashAlgorithm algo);
@noSideEffects
extern void update_checksum_with_payload<T19, O20>(in bool condition,
                                                   in T19 data,
                                                   inout O20 checksum,
                                                   HashAlgorithm algo);
extern void clone(in CloneType type, in bit<32> session);
@deprecated("Please use 'resubmit_preserving_field_list' instead")
extern void resubmit<T21>(in T21 data);
extern void resubmit_preserving_field_list(bit<8> index);
@deprecated("Please use 'recirculate_preserving_field_list' instead")
extern void recirculate<T22>(in T22 data);
extern void recirculate_preserving_field_list(bit<8> index);
@deprecated("Please use 'clone_preserving_field_list' instead")
extern void clone3<T23>(in CloneType type, in bit<32> session, in T23 data);
extern void clone_preserving_field_list(in CloneType type,
                                        in bit<32> session, bit<8> index);
extern void truncate(in bit<32> length);
extern void assert(in bool check);
extern void assume(in bool check);
extern void log_msg(string msg);
extern void log_msg<T24>(string msg, in T24 data);
parser Parser<H25, M26>
  (packet_in b,
   out H25 parsedHdr,
   inout M26 meta,
   inout standard_metadata_t standard_metadata);
control VerifyChecksum<H27, M28> (inout H27 hdr, inout M28 meta);
@pipeline
control Ingress<H29, M30>
  (inout H29 hdr, inout M30 meta, inout standard_metadata_t standard_metadata);
@pipeline
control Egress<H31, M32>
  (inout H31 hdr, inout M32 meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H33, M34> (inout H33 hdr, inout M34 meta);
@deparser
control Deparser<H35> (packet_out b, in H35 hdr);
package V1Switch<H36, M37>
  (Parser<H36, M37> p,
   VerifyChecksum<H36, M37> vr,
   Ingress<H36, M37> ig,
   Egress<H36, M37> eg,
   ComputeChecksum<H36, M37> ck,
   Deparser<H36> dep);
header Header {
  bit<32> data;
}
struct H {
  Header h1;
  Header h2;
}
struct M {
  
}
parser ParserI(packet_in pkt, out H hdr, inout M meta,
               inout standard_metadata_t smeta) {
  state start {
    transition accept;
  }
}
control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
  Header h1;
  Header h2;
  H s1;
  H s2;
  action invalid_H(inout H s) {
    s.h1.setInvalid();
    s.h2.setInvalid();
  }
  apply {
    h1 = {1};
    if (hdr.h1.data==0) {
      h2 = h1;
    }else
    {
    h2.setValid();
    h2.data = 0;
    }
    hdr.h1.data = h1.data;
    hdr.h2.data = h2.data;
    if (h2.data==1) {
      h1.setInvalid();
    }
    hdr.h1.data = h1.data;
    h1 = h2;
    if (h1.data==1)
      {
      s1 = {h1, h2};
      s2 = s1;
      if (s2.h1.data==0 && s2.h2.data==0)
        {
        if (s1.h1.data>0) 
          s1.h1.setInvalid();
          else
            s1.h1.setInvalid();
        hdr.h1.data = s1.h1.data;
      }else {
      s1.h1.setValid();
      }
      hdr.h2.data = s1.h1.data;
    }
    invalid_H(hdr);
    hdr.h1.data = 1;
    hdr.h2.data = 1;
  }
}
control EgressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
  apply { 
  }
}
control DeparserI(packet_out pk, in H hdr) {
  apply { 
  }
}
control VerifyChecksumI(inout H hdr, inout M meta) {
  apply { 
  }
}
control ComputeChecksumI(inout H hdr, inout M meta) {
  apply { 
  }
}
V1Switch(ParserI(), VerifyChecksumI(), IngressI(), EgressI(),
           ComputeChecksumI(), DeparserI())
  main;

