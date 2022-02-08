error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument,
    IPv4HeaderTooShort,
    TCPHeaderTooShort,
    IPv4IncorrectVersion,
    IPv4ChecksumError
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

extern void verify(in bool check, in error toSignal);
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

extern action_selector {
    action_selector(HashAlgorithm algorithm, bit<32> size, bit<32> outputWidth);
}

@deprecated("Please use verify_checksum/update_checksum instead.") extern Checksum16 {
    Checksum16();
    bit<16> get<D>(in D data);
}

extern void verify_checksum<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@pure extern void update_checksum<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
extern void verify_checksum_with_payload<T, O>(in bool condition, in T data, in O checksum, HashAlgorithm algo);
@noSideEffects extern void update_checksum_with_payload<T, O>(in bool condition, in T data, inout O checksum, HashAlgorithm algo);
parser Parser<H, M>(packet_in b, out H parsedHdr, inout M meta, inout standard_metadata_t standard_metadata);
control VerifyChecksum<H, M>(inout H hdr, inout M meta);
@pipeline control Ingress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
@pipeline control Egress<H, M>(inout H hdr, inout M meta, inout standard_metadata_t standard_metadata);
control ComputeChecksum<H, M>(inout H hdr, inout M meta);
@deparser control Deparser<H>(packet_out b, in H hdr);
package V1Switch<H, M>(Parser<H, M> p, VerifyChecksum<H, M> vr, Ingress<H, M> ig, Egress<H, M> eg, ComputeChecksum<H, M> ck, Deparser<H> dep);
typedef bit<32> IPv4Address;
header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header ipv4_t {
    bit<4>      version;
    bit<4>      ihl;
    bit<8>      diffserv;
    bit<16>     totalLen;
    bit<16>     identification;
    bit<3>      flags;
    bit<13>     fragOffset;
    bit<8>      ttl;
    bit<8>      protocol;
    bit<16>     hdrChecksum;
    IPv4Address srcAddr;
    IPv4Address dstAddr;
    varbit<320> options;
}

header tcp_t {
    bit<16>     srcPort;
    bit<16>     dstPort;
    bit<32>     seqNo;
    bit<32>     ackNo;
    bit<4>      dataOffset;
    bit<3>      res;
    bit<3>      ecn;
    bit<6>      ctrl;
    bit<16>     window;
    bit<16>     checksum;
    bit<16>     urgentPtr;
    varbit<320> options;
}

header udp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<16> length_;
    bit<16> checksum;
}

header IPv4_up_to_ihl_only_h {
    bit<4> version;
    bit<4> ihl;
}

header tcp_upto_data_offset_only_h {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<32> seqNo;
    bit<32> ackNo;
    bit<4>  dataOffset;
    bit<4>  dontCare;
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
    tcp_t      tcp;
    udp_t      udp;
}

struct mystruct1_t {
    bit<4> a;
    bit<4> b;
}

struct metadata {
    mystruct1_t mystruct1;
    bit<16>     l4Len;
}

parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    @name("parserI.tmp") IPv4_up_to_ihl_only_h tmp;
    @name("parserI.tmp_0") bit<9> tmp_0;
    @name("parserI.tmp_1") bit<9> tmp_1;
    @name("parserI.tmp_2") bit<9> tmp_2;
    @name("parserI.tmp_3") bit<32> tmp_3;
    @name("parserI.tmp_4") tcp_upto_data_offset_only_h tmp_4;
    @name("parserI.tmp_5") bit<9> tmp_5;
    @name("parserI.tmp_6") bit<9> tmp_6;
    @name("parserI.tmp_7") bit<9> tmp_7;
    @name("parserI.tmp_8") bit<32> tmp_8;
    bit<8> tmp_9;
    bit<104> tmp_10;
    state start {
        pkt.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        {
            tmp_9 = pkt.lookahead<bit<8>>();
            tmp.setValid();
            tmp.version = tmp_9[7:4];
            tmp.ihl = tmp_9[3:0];
        }
        tmp_0 = (bit<9>)tmp.ihl << 2;
        tmp_1 = tmp_0 + 9w492;
        tmp_2 = tmp_1 << 3;
        tmp_3 = (bit<32>)tmp_2;
        pkt.extract<ipv4_t>(hdr.ipv4, tmp_3);
        verify(hdr.ipv4.version == 4w4, error.IPv4IncorrectVersion);
        verify(hdr.ipv4.ihl >= 4w5, error.IPv4HeaderTooShort);
        meta.l4Len = hdr.ipv4.totalLen - ((bit<16>)hdr.ipv4.ihl << 2);
        transition select(hdr.ipv4.protocol) {
            8w6: parse_tcp;
            8w17: parse_udp;
            default: accept;
        }
    }
    state parse_tcp {
        {
            tmp_10 = pkt.lookahead<bit<104>>();
            tmp_4.setValid();
            tmp_4.srcPort = tmp_10[103:88];
            tmp_4.dstPort = tmp_10[87:72];
            tmp_4.seqNo = tmp_10[71:40];
            tmp_4.ackNo = tmp_10[39:8];
            tmp_4.dataOffset = tmp_10[7:4];
            tmp_4.dontCare = tmp_10[3:0];
        }
        tmp_5 = (bit<9>)tmp_4.dataOffset << 2;
        tmp_6 = tmp_5 + 9w492;
        tmp_7 = tmp_6 << 3;
        tmp_8 = (bit<32>)tmp_7;
        pkt.extract<tcp_t>(hdr.tcp, tmp_8);
        verify(hdr.tcp.dataOffset >= 4w5, error.TCPHeaderTooShort);
        transition accept;
    }
    state parse_udp {
        pkt.extract<udp_t>(hdr.udp);
        transition accept;
    }
}

control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_2() {
    }
    @name("cIngress.foot") action foot() {
        hdr.tcp.srcPort = hdr.tcp.srcPort + 16w1;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
        hdr.ipv4.dstAddr = hdr.ipv4.dstAddr + 32w4;
    }
    @name("cIngress.foou") action foou() {
        hdr.udp.srcPort = hdr.udp.srcPort + 16w1;
        hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
        hdr.ipv4.dstAddr = hdr.ipv4.dstAddr + 32w4;
    }
    @name("cIngress.guh") table guh_0 {
        key = {
            hdr.tcp.dstPort: exact @name("hdr.tcp.dstPort") ;
        }
        actions = {
            foot();
            NoAction_1();
        }
        const default_action = NoAction_1();
        const entries = {
                        16w80 : foot();
        }
    }
    @name("cIngress.huh") table huh_0 {
        key = {
            hdr.udp.dstPort: exact @name("hdr.udp.dstPort") ;
        }
        actions = {
            foou();
            NoAction_2();
        }
        const default_action = NoAction_2();
        const entries = {
                        16w80 : foou();
        }
    }
    apply {
        if (hdr.tcp.isValid()) {
            guh_0.apply();
        }
        if (hdr.udp.isValid()) {
            huh_0.apply();
        }
    }
}

control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}

struct tuple_0 {
    bit<4>      f0;
    bit<4>      f1;
    bit<8>      f2;
    bit<16>     f3;
    bit<16>     f4;
    bit<3>      f5;
    bit<13>     f6;
    bit<8>      f7;
    bit<8>      f8;
    bit<32>     f9;
    bit<32>     f10;
    varbit<320> f11;
}

struct tuple_1 {
    bit<32>     f0;
    bit<32>     f1;
    bit<8>      f2;
    bit<8>      f3;
    bit<16>     f4;
    bit<16>     f5;
    bit<16>     f6;
    bit<32>     f7;
    bit<32>     f8;
    bit<4>      f9;
    bit<3>      f10;
    bit<3>      f11;
    bit<6>      f12;
    bit<16>     f13;
    bit<16>     f14;
    varbit<320> f15;
}

struct tuple_2 {
    bit<32> f0;
    bit<32> f1;
    bit<8>  f2;
    bit<8>  f3;
    bit<16> f4;
    bit<16> f5;
    bit<16> f6;
    bit<16> f7;
}

control vc(inout headers hdr, inout metadata meta) {
    apply {
        verify_checksum<tuple_0, bit<16>>(true, (tuple_0){f0 = hdr.ipv4.version,f1 = hdr.ipv4.ihl,f2 = hdr.ipv4.diffserv,f3 = hdr.ipv4.totalLen,f4 = hdr.ipv4.identification,f5 = hdr.ipv4.flags,f6 = hdr.ipv4.fragOffset,f7 = hdr.ipv4.ttl,f8 = hdr.ipv4.protocol,f9 = hdr.ipv4.srcAddr,f10 = hdr.ipv4.dstAddr,f11 = hdr.ipv4.options}, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
        verify_checksum_with_payload<tuple_1, bit<16>>(hdr.tcp.isValid(), (tuple_1){f0 = hdr.ipv4.srcAddr,f1 = hdr.ipv4.dstAddr,f2 = 8w0,f3 = hdr.ipv4.protocol,f4 = meta.l4Len,f5 = hdr.tcp.srcPort,f6 = hdr.tcp.dstPort,f7 = hdr.tcp.seqNo,f8 = hdr.tcp.ackNo,f9 = hdr.tcp.dataOffset,f10 = hdr.tcp.res,f11 = hdr.tcp.ecn,f12 = hdr.tcp.ctrl,f13 = hdr.tcp.window,f14 = hdr.tcp.urgentPtr,f15 = hdr.tcp.options}, hdr.tcp.checksum, HashAlgorithm.csum16);
        verify_checksum_with_payload<tuple_2, bit<16>>(hdr.udp.isValid(), (tuple_2){f0 = hdr.ipv4.srcAddr,f1 = hdr.ipv4.dstAddr,f2 = 8w0,f3 = hdr.ipv4.protocol,f4 = meta.l4Len,f5 = hdr.udp.srcPort,f6 = hdr.udp.dstPort,f7 = hdr.udp.length_}, hdr.udp.checksum, HashAlgorithm.csum16);
    }
}

control uc(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum<tuple_0, bit<16>>(true, (tuple_0){f0 = hdr.ipv4.version,f1 = hdr.ipv4.ihl,f2 = hdr.ipv4.diffserv,f3 = hdr.ipv4.totalLen,f4 = hdr.ipv4.identification,f5 = hdr.ipv4.flags,f6 = hdr.ipv4.fragOffset,f7 = hdr.ipv4.ttl,f8 = hdr.ipv4.protocol,f9 = hdr.ipv4.srcAddr,f10 = hdr.ipv4.dstAddr,f11 = hdr.ipv4.options}, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
        update_checksum_with_payload<tuple_1, bit<16>>(hdr.tcp.isValid(), (tuple_1){f0 = hdr.ipv4.srcAddr,f1 = hdr.ipv4.dstAddr,f2 = 8w0,f3 = hdr.ipv4.protocol,f4 = meta.l4Len,f5 = hdr.tcp.srcPort,f6 = hdr.tcp.dstPort,f7 = hdr.tcp.seqNo,f8 = hdr.tcp.ackNo,f9 = hdr.tcp.dataOffset,f10 = hdr.tcp.res,f11 = hdr.tcp.ecn,f12 = hdr.tcp.ctrl,f13 = hdr.tcp.window,f14 = hdr.tcp.urgentPtr,f15 = hdr.tcp.options}, hdr.tcp.checksum, HashAlgorithm.csum16);
        update_checksum_with_payload<tuple_2, bit<16>>(hdr.udp.isValid(), (tuple_2){f0 = hdr.ipv4.srcAddr,f1 = hdr.ipv4.dstAddr,f2 = 8w0,f3 = hdr.ipv4.protocol,f4 = meta.l4Len,f5 = hdr.udp.srcPort,f6 = hdr.udp.dstPort,f7 = hdr.udp.length_}, hdr.udp.checksum, HashAlgorithm.csum16);
    }
}

control DeparserI(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
        packet.emit<tcp_t>(hdr.tcp);
        packet.emit<udp_t>(hdr.udp);
    }
}

V1Switch<headers, metadata>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;

