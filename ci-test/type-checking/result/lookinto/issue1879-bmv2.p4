/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1879-bmv2.p4
\n
/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>


const bit<6> TYPE_ADDR_IPV4 = 0x1;

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

header preamble_t {
    bit<336>  data;
}


#define LEN_ADDR_IPV4 32

header prot_common_t {
    bit<4>    version;
    bit<6>    dstType;
    bit<6>    srcType;
    bit<16>   totalLen;
    bit<8>    hdrLen;
    bit<8>    curri;
    bit<8>    currh;
    bit<8>    nextHdr;
}

header prot_addr_common_t {
    bit<128> data;
}

header prot_host_addr_ipv4_t {
    bit<LEN_ADDR_IPV4>  addr;
}


header_union prot_host_addr_t {
    prot_host_addr_ipv4_t  ipv4;
}

header prot_host_addr_padding_t {
    varbit<32>   padding;
}

header prot_i_t {
    bit<7> data;
    bit       upDirection;
    bit<48> data2;
    bit<8>    segLen;
}

header prot_h_t {
    bit<64> data;
}

struct currenti_t {
    bit       upDirection;
}

struct metadata {
    bit<8>    headerLen;
    bit<8>    hLeft;
    bit<9>    addrLen;
    bit<8>    currPos;
    currenti_t currenti;
}

struct headers {
    preamble_t preamble;
    prot_common_t            prot_common;
    prot_addr_common_t       prot_addr_common;
    prot_host_addr_t         prot_host_addr_dst;
    prot_host_addr_t         prot_host_addr_src;
    prot_host_addr_padding_t prot_host_addr_padding;
    prot_i_t     prot_inf_0;
    prot_h_t[10] prot_h_0;
    prot_i_t     prot_inf_1;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

parser SubParser(packet_in packet,
                   out prot_i_t inf,
                   inout metadata meta,
                   in bool currentISelected,
                   in bit<8> currI) {
    state start {
        packet.extract(inf);

        bool currentISelected2 = currI == meta.currPos;

//        meta.currenti.upDirection = meta.currenti.upDirection + (bit<1>)currentISelected * inf.upDirection;//WORKS
        meta.currenti.upDirection = meta.currenti.upDirection + (bit<1>)currentISelected2 * inf.upDirection;//DOES NOT WORK

        meta.hLeft = inf.segLen;
        meta.currPos = meta.currPos + 1;

        transition accept;
    }
}

parser PROTParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    SubParser() subParser;

    state start {
        packet.extract(hdr.preamble);
        packet.extract(hdr.prot_common);
        packet.extract(hdr.prot_addr_common);
        meta.headerLen = hdr.prot_common.hdrLen;

        transition parse_prot_host_addr_dst_ipv4;
    }

    state parse_prot_host_addr_dst_ipv4 {
        packet.extract(hdr.prot_host_addr_dst.ipv4);
        meta.addrLen = LEN_ADDR_IPV4;
        transition parse_prot_host_addr_src_select;
    }

    state parse_prot_host_addr_src_select {
        transition select(hdr.prot_common.srcType) {
            TYPE_ADDR_IPV4: parse_prot_host_addr_src_ipv4;
       }
    }

    state parse_prot_host_addr_src_ipv4 {
        packet.extract(hdr.prot_host_addr_src.ipv4);
        meta.addrLen = meta.addrLen + LEN_ADDR_IPV4;
        transition parse_prot_addr_padding;
    }

    state parse_prot_addr_padding {
        bit<9> paddingLen = (64 - (meta.addrLen % 64)) % 64;
        packet.extract(hdr.prot_host_addr_padding, (bit<32>)paddingLen);
        meta.addrLen = meta.addrLen + paddingLen;
        transition parse_prot_inf_0;
    }

    state parse_prot_inf_0 {
        meta.currPos = (bit<8>)(1 + 2 + meta.addrLen / 64);

        bool currentISelected = hdr.prot_common.curri == meta.currPos;
        subParser.apply(packet, hdr.prot_inf_0, meta, currentISelected, hdr.prot_common.curri);

        transition parse_prot_h_0_pre;
    }

    state parse_prot_h_0_pre {
        transition select(meta.hLeft) {
            0: parse_prot_1;
            default: parse_prot_h_0;
        }
    }

    state parse_prot_h_0 {
        packet.extract(hdr.prot_h_0.next);

        meta.hLeft = meta.hLeft - 1;
        meta.currPos = meta.currPos + 1;

        transition parse_prot_h_0_pre;
    }

    state parse_prot_1 {
        bit<8> hdrLeft = meta.headerLen - meta.currPos;
        transition select(hdrLeft) {
            0: accept;
            default: parse_prot_inf_1;
        }
    }

    state parse_prot_inf_1 {
        bool currentISelected = meta.currPos == hdr.prot_common.curri;
        subParser.apply(packet, hdr.prot_inf_1, meta, currentISelected, hdr.prot_common.curri);

        transition accept;
    }
}


/*************************************************************************
************   C H E C K S U M    V E R I F I C A T I O N   *************
*************************************************************************/

control PROTVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control PROTIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        if (meta.currenti.upDirection == 0) {
            mark_to_drop(standard_metadata);
        }
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control PROTEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
   apply {
    }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control PROTComputeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}


/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control PROTDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr);
    }
}

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
PROTParser(),
PROTVerifyChecksum(),
PROTIngress(),
PROTEgress(),
PROTComputeChecksum(),
PROTDeparser()
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
match_kind {
  range, optional, selector
}
const bit<32> __v1model_version = 20180101;
@metadata
@name("standard_metadata")
struct standard_metadata_t {
  bit<9> ingress_port;
  bit<9> egress_spec;
  bit<9> egress_port;
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
extern counter {
  counter(bit<32> size, CounterType type);
  void count(in bit<32> index);
}

extern direct_counter {
  direct_counter(CounterType type);
  void count();
}

extern meter {
  meter(bit<32> size, MeterType type);
  void execute_meter<T3>(in bit<32> index, out T3 result);
}

extern direct_meter<T4> {
  direct_meter(MeterType type);
  void read(out T4 result);
}

extern register<T5> {
  register(bit<32> size);
  @noSideEffects
  void read(out T5 result, in bit<32> index);
  void write(in bit<32> index, in T5 value);
}

extern action_profile {
  action_profile(bit<32> size);
}

extern void random<T6>(out T6 result, in T6 lo, in T6 hi);
extern void digest<T7>(in bit<32> receiver, in T7 data);
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
extern void hash<O, T8, D, M>(out O result, in HashAlgorithm algo,
                              in T8 base, in D data, in M max);
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
  bit<16> get<D9>(in D9 data);
}

extern void verify_checksum<T10, O11>(in bool condition, in T10 data,
                                      in O11 checksum, HashAlgorithm algo);
@pure
extern void update_checksum<T12, O13>(in bool condition, in T12 data,
                                      inout O13 checksum,
                                      HashAlgorithm algo);
extern void verify_checksum_with_payload<T14, O15>(in bool condition,
                                                   in T14 data,
                                                   in O15 checksum,
                                                   HashAlgorithm algo);
@noSideEffects
extern void update_checksum_with_payload<T16, O17>(in bool condition,
                                                   in T16 data,
                                                   inout O17 checksum,
                                                   HashAlgorithm algo);
extern void clone(in CloneType type, in bit<32> session);
@deprecated("Please use 'resubmit_preserving_field_list' instead")
extern void resubmit<T18>(in T18 data);
extern void resubmit_preserving_field_list(bit<8> index);
@deprecated("Please use 'recirculate_preserving_field_list' instead")
extern void recirculate<T19>(in T19 data);
extern void recirculate_preserving_field_list(bit<8> index);
@deprecated("Please use 'clone_preserving_field_list' instead")
extern void clone3<T20>(in CloneType type, in bit<32> session, in T20 data);
extern void clone_preserving_field_list(in CloneType type,
                                        in bit<32> session, bit<8> index);
extern void truncate(in bit<32> length);
extern void assert(in bool check);
extern void assume(in bool check);
extern void log_msg(string msg);
extern void log_msg<T21>(string msg, in T21 data);
parser Parser<H, M22>
  (packet_in b,
   out H parsedHdr,
   inout M22 meta,
   inout standard_metadata_t standard_metadata);
control VerifyChecksum<H23, M24> (inout H23 hdr, inout M24 meta);
@pipeline
control Ingress<H25, M26>
  (inout H25 hdr, inout M26 meta, inout standard_metadata_t standard_metadata);
@pipeline
control Egress<H27, M28>
  (inout H27 hdr, inout M28 meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H29, M30> (inout H29 hdr, inout M30 meta);
@deparser
control Deparser<H31> (packet_out b, in H31 hdr);
package V1Switch<H32, M33>
  (Parser<H32, M33> p,
   VerifyChecksum<H32, M33> vr,
   Ingress<H32, M33> ig,
   Egress<H32, M33> eg,
   ComputeChecksum<H32, M33> ck,
   Deparser<H32> dep);
const bit<6> TYPE_ADDR_IPV4 = 1;
header preamble_t {
  bit<336> data;
}
header prot_common_t {
  bit<4> version;
  bit<6> dstType;
  bit<6> srcType;
  bit<16> totalLen;
  bit<8> hdrLen;
  bit<8> curri;
  bit<8> currh;
  bit<8> nextHdr;
}
header prot_addr_common_t {
  bit<128> data;
}
header prot_host_addr_ipv4_t {
  bit<32> addr;
}
header_union prot_host_addr_t {
  prot_host_addr_ipv4_t ipv4;
}
header prot_host_addr_padding_t {
  varbit <32> padding;
}
header prot_i_t {
  bit<7> data;
  bit<1> upDirection;
  bit<48> data2;
  bit<8> segLen;
}
header prot_h_t {
  bit<64> data;
}
struct currenti_t {
  bit<1> upDirection;
}
struct metadata {
  bit<8> headerLen;
  bit<8> hLeft;
  bit<9> addrLen;
  bit<8> currPos;
  currenti_t currenti;
}
struct headers {
  preamble_t preamble;
  prot_common_t prot_common;
  prot_addr_common_t prot_addr_common;
  prot_host_addr_t prot_host_addr_dst;
  prot_host_addr_t prot_host_addr_src;
  prot_host_addr_padding_t prot_host_addr_padding;
  prot_i_t prot_inf_0;
  prot_h_t[10] prot_h_0;
  prot_i_t prot_inf_1;
}
parser SubParser(packet_in packet, out prot_i_t inf, inout metadata meta,
                 in bool currentISelected, in bit<8> currI) {
  state start
    {
    packet.extract(inf);
    bool currentISelected2 = currI==meta.currPos;
    meta.currenti.upDirection =
    meta.currenti.upDirection+(bit<1>) currentISelected2*inf.upDirection;
    meta.hLeft = inf.segLen;
    meta.currPos = meta.currPos+1;
    transition accept;
  }
}
parser PROTParser(packet_in packet, out headers hdr, inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
  SubParser() subParser;
  state start
    {
    packet.extract(hdr.preamble);
    packet.extract(hdr.prot_common);
    packet.extract(hdr.prot_addr_common);
    meta.headerLen = hdr.prot_common.hdrLen;
    transition parse_prot_host_addr_dst_ipv4;
  }
  state parse_prot_host_addr_dst_ipv4
    {
    packet.extract(hdr.prot_host_addr_dst.ipv4);
    meta.addrLen = 32;
    transition parse_prot_host_addr_src_select;
  }
  state parse_prot_host_addr_src_select
    {
    transition select(hdr.prot_common.srcType) {
      TYPE_ADDR_IPV4: parse_prot_host_addr_src_ipv4;
    }
  }
  state parse_prot_host_addr_src_ipv4
    {
    packet.extract(hdr.prot_host_addr_src.ipv4);
    meta.addrLen = meta.addrLen+32;
    transition parse_prot_addr_padding;
  }
  state parse_prot_addr_padding
    {
    bit<9> paddingLen = 64-meta.addrLen%64%64;
    packet.extract(hdr.prot_host_addr_padding, (bit<32>) paddingLen);
    meta.addrLen = meta.addrLen+paddingLen;
    transition parse_prot_inf_0;
  }
  state parse_prot_inf_0
    {
    meta.currPos = (bit<8>) 1+2+meta.addrLen/64;
    bool currentISelected = hdr.prot_common.curri==meta.currPos;
    subParser.apply(packet, hdr.prot_inf_0, meta, currentISelected,
                      hdr.prot_common.curri);
    transition parse_prot_h_0_pre;
  }
  state parse_prot_h_0_pre
    {
    transition select(meta.hLeft) {
      0: parse_prot_1;
      default: parse_prot_h_0;
    }
  }
  state parse_prot_h_0
    {
    packet.extract(hdr.prot_h_0.next);
    meta.hLeft = meta.hLeft-1;
    meta.currPos = meta.currPos+1;
    transition parse_prot_h_0_pre;
  }
  state parse_prot_1
    {
    bit<8> hdrLeft = meta.headerLen-meta.currPos;
    transition select(hdrLeft) {
      0: accept;
      default: parse_prot_inf_1;
    }
  }
  state parse_prot_inf_1
    {
    bool currentISelected = meta.currPos==hdr.prot_common.curri;
    subParser.apply(packet, hdr.prot_inf_1, meta, currentISelected,
                      hdr.prot_common.curri);
    transition accept;
  }
}
control PROTVerifyChecksum(inout headers hdr, inout metadata meta) {
  apply { 
  }
}
control PROTIngress(inout headers hdr, inout metadata meta,
                    inout standard_metadata_t standard_metadata) {
  apply {
    if (meta.currenti.upDirection==0) {
      mark_to_drop(standard_metadata);
    }
  }
}
control PROTEgress(inout headers hdr, inout metadata meta,
                   inout standard_metadata_t standard_metadata) {
  apply { 
  }
}
control PROTComputeChecksum(inout headers hdr, inout metadata meta) {
  apply { 
  }
}
control PROTDeparser(packet_out packet, in headers hdr) {
  apply {
    packet.emit(hdr);
  }
}
V1Switch(PROTParser(), PROTVerifyChecksum(), PROTIngress(), PROTEgress(),
           PROTComputeChecksum(), PROTDeparser())
  main;

