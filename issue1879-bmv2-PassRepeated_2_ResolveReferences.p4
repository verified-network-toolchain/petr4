error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument
}

extern packet_in {
    void extract<T>(out T hdr);
    void extract<T>(out T variableSizeHeader, in bit<32> variableFieldSizeInBits);
    T lookahead<T>();
    void advance(in bit<32> sizeInBits);
    bit<32> length();
}

extern packet_out {
    void emit<T>(in T hdr);
}

match_kind {
    exact,
    ternary,
    lpm
}

match_kind {
    range,
    optional,
    selector
}

const bit<32> __v1model_version = 32w20180101;
@metadata @name("standard_metadata") struct standard_metadata_t {
    bit<9>  ingress_port;
    bit<9>  egress_spec;
    bit<9>  egress_port;
    bit<32> instance_type;
    bit<32> packet_length;
    @alias("queueing_metadata.enq_timestamp") 
    bit<32> enq_timestamp;
    @alias("queueing_metadata.enq_qdepth") 
    bit<19> enq_qdepth;
    @alias("queueing_metadata.deq_timedelta") 
    bit<32> deq_timedelta;
    @alias("queueing_metadata.deq_qdepth") 
    bit<19> deq_qdepth;
    @alias("intrinsic_metadata.ingress_global_timestamp") 
    bit<48> ingress_global_timestamp;
    @alias("intrinsic_metadata.egress_global_timestamp") 
    bit<48> egress_global_timestamp;
    @alias("intrinsic_metadata.mcast_grp") 
    bit<16> mcast_grp;
    @alias("intrinsic_metadata.egress_rid") 
    bit<16> egress_rid;
    bit<1>  checksum_error;
    error   parser_error;
    @alias("intrinsic_metadata.priority") 
    bit<3>  priority;
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
    void execute_meter<T>(in bit<32> index, out T result);
}

extern direct_meter<T> {
    direct_meter(MeterType type);
    void read(out T result);
}

extern register<T> {
    register(bit<32> size);
    @noSideEffects void read(out T result, in bit<32> index);
    void write(in bit<32> index, in T value);
}

extern action_profile {
    action_profile(bit<32> size);
}

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

@pure extern void mark_to_drop(inout standard_metadata_t standard_metadata);
extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
header preamble_t {
    bit<336> data;
}

header prot_common_t {
    bit<4>  version;
    bit<6>  dstType;
    bit<6>  srcType;
    bit<16> totalLen;
    bit<8>  hdrLen;
    bit<8>  curri;
    bit<8>  currh;
    bit<8>  nextHdr;
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
    varbit<32> padding;
}

header prot_i_t {
    bit<7>  data;
    bit<1>  upDirection;
    bit<48> data2;
    bit<8>  segLen;
}

header prot_h_t {
    bit<64> data;
}

struct currenti_t {
    bit<1> upDirection;
}

struct metadata {
    bit<8>     headerLen;
    bit<8>     hLeft;
    bit<9>     addrLen;
    bit<8>     currPos;
    currenti_t currenti;
}

struct headers {
    preamble_t               preamble;
    prot_common_t            prot_common;
    prot_addr_common_t       prot_addr_common;
    prot_host_addr_t         prot_host_addr_dst;
    prot_host_addr_t         prot_host_addr_src;
    prot_host_addr_padding_t prot_host_addr_padding;
    prot_i_t                 prot_inf_0;
    prot_h_t[10]             prot_h_0;
    prot_i_t                 prot_inf_1;
}

parser SubParser(packet_in packet, out prot_i_t inf, inout metadata meta, in bool currentISelected, in bit<8> currI) {
    @name("currentISelected2") bool currentISelected2_0;
    state start {
        packet.extract<prot_i_t>(inf);
        currentISelected2_0 = currI == meta.currPos;
        meta.currenti.upDirection = meta.currenti.upDirection + (bit<1>)currentISelected2_0 * inf.upDirection;
        meta.hLeft = inf.segLen;
        meta.currPos = meta.currPos + 8w1;
        transition accept;
    }
}

parser PROTParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("paddingLen") bit<9> paddingLen_0;
    @name("currentISelected") bool currentISelected_0;
    @name("hdrLeft") bit<8> hdrLeft_0;
    @name("currentISelected") bool currentISelected_1;
    prot_i_t inf_0;
    metadata meta_0;
    bool currentISelected_2;
    bit<8> currI_0;
    @name("subParser.currentISelected2") bool subParser_currentISelected2;
    state start {
        packet.extract<preamble_t>(hdr.preamble);
        packet.extract<prot_common_t>(hdr.prot_common);
        packet.extract<prot_addr_common_t>(hdr.prot_addr_common);
        meta.headerLen = hdr.prot_common.hdrLen;
        packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_dst.ipv4);
        meta.addrLen = 9w32;
        transition select(hdr.prot_common.srcType) {
            6w0x1: parse_prot_host_addr_src_ipv4;
        }
    }
    state parse_prot_host_addr_src_ipv4 {
        packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_src.ipv4);
        meta.addrLen = meta.addrLen + 9w32;
        paddingLen_0 = 9w64 - (meta.addrLen & 9w63) & 9w63;
        packet.extract<prot_host_addr_padding_t>(hdr.prot_host_addr_padding, (bit<32>)paddingLen_0);
        meta.addrLen = meta.addrLen + paddingLen_0;
        meta.currPos = (bit<8>)(9w3 + (meta.addrLen >> 6));
        currentISelected_0 = hdr.prot_common.curri == meta.currPos;
        inf_0.setInvalid();
        meta_0 = meta;
        currentISelected_2 = currentISelected_0;
        currI_0 = hdr.prot_common.curri;
        transition SubParser_start;
    }
    state SubParser_start {
        packet.extract<prot_i_t>(inf_0);
        subParser_currentISelected2 = currI_0 == meta_0.currPos;
        meta_0.currenti.upDirection = meta_0.currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
        meta_0.hLeft = inf_0.segLen;
        meta_0.currPos = meta_0.currPos + 8w1;
        transition parse_prot_host_addr_src_ipv4_0;
    }
    state parse_prot_host_addr_src_ipv4_0 {
        hdr.prot_inf_0 = inf_0;
        meta = meta_0;
        transition parse_prot_h_0_pre;
    }
    state parse_prot_h_0_pre {
        transition select(meta.hLeft) {
            8w0: parse_prot_1;
            default: parse_prot_h_0;
        }
    }
    state parse_prot_h_0 {
        packet.extract<prot_h_t>(hdr.prot_h_0.next);
        meta.hLeft = meta.hLeft + 8w255;
        meta.currPos = meta.currPos + 8w1;
        transition parse_prot_h_0_pre;
    }
    state parse_prot_1 {
        hdrLeft_0 = meta.headerLen - meta.currPos;
        transition select(hdrLeft_0) {
            8w0: accept;
            default: parse_prot_inf_1;
        }
    }
    state parse_prot_inf_1 {
        currentISelected_1 = meta.currPos == hdr.prot_common.curri;
        inf_0.setInvalid();
        meta_0 = meta;
        currentISelected_2 = currentISelected_1;
        currI_0 = hdr.prot_common.curri;
        transition SubParser_start_0;
    }
    state SubParser_start_0 {
        packet.extract<prot_i_t>(inf_0);
        subParser_currentISelected2 = currI_0 == meta_0.currPos;
        meta_0.currenti.upDirection = meta_0.currenti.upDirection + (bit<1>)subParser_currentISelected2 * inf_0.upDirection;
        meta_0.hLeft = inf_0.segLen;
        meta_0.currPos = meta_0.currPos + 8w1;
        transition parse_prot_inf;
    }
    state parse_prot_inf {
        hdr.prot_inf_1 = inf_0;
        meta = meta_0;
        transition accept;
    }
}

control PROTVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control PROTIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
        if (meta.currenti.upDirection == 1w0) {
            mark_to_drop(standard_metadata);
        }
    }
}

control PROTEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control PROTComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control PROTDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit<headers>(hdr);
    }
}

V1Switch<headers, metadata>(PROTParser(), PROTVerifyChecksum(), PROTIngress(), PROTEgress(), PROTComputeChecksum(), PROTDeparser()) main;

