error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument,
    UnhandledIPv4Options,
    BadIPv4HeaderChecksum
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

typedef bit<32> PortIdUint_t;
typedef bit<32> MulticastGroupUint_t;
typedef bit<16> CloneSessionIdUint_t;
typedef bit<8> ClassOfServiceUint_t;
typedef bit<16> EgressInstanceUint_t;
typedef bit<64> TimestampUint_t;
typedef PortIdUint_t PortId_t;
typedef MulticastGroupUint_t MulticastGroup_t;
typedef CloneSessionIdUint_t CloneSessionId_t;
typedef ClassOfServiceUint_t ClassOfService_t;
typedef EgressInstanceUint_t EgressInstance_t;
typedef TimestampUint_t Timestamp_t;
typedef error ParserError_t;
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
    PortId_t         ingress_port;
    PSA_PacketPath_t packet_path;
}

struct psa_egress_parser_input_metadata_t {
    PortId_t         egress_port;
    PSA_PacketPath_t packet_path;
}

struct psa_ingress_input_metadata_t {
    PortId_t         ingress_port;
    PSA_PacketPath_t packet_path;
    Timestamp_t      ingress_timestamp;
    ParserError_t    parser_error;
}

struct psa_ingress_output_metadata_t {
    ClassOfService_t class_of_service;
    bool             clone;
    CloneSessionId_t clone_session_id;
    bool             drop;
    bool             resubmit;
    MulticastGroup_t multicast_group;
    PortId_t         egress_port;
}

struct psa_egress_input_metadata_t {
    ClassOfService_t class_of_service;
    PortId_t         egress_port;
    PSA_PacketPath_t packet_path;
    EgressInstance_t instance;
    Timestamp_t      egress_timestamp;
    ParserError_t    parser_error;
}

struct psa_egress_deparser_input_metadata_t {
    PortId_t egress_port;
}

struct psa_egress_output_metadata_t {
    bool             clone;
    CloneSessionId_t clone_session_id;
    bool             drop;
}

match_kind {
    range,
    selector,
    optional
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
    @pure O get_hash<D>(in D data);
    @pure O get_hash<T, D>(in T base, in D data, in T max);
}

extern Checksum<W> {
    Checksum(PSA_HashAlgorithm_t hash);
    void clear();
    void update<T>(in T data);
    @noSideEffects W get();
}

extern InternetChecksum {
    InternetChecksum();
    void clear();
    void add<T>(in T data);
    void subtract<T>(in T data);
    @noSideEffects bit<16> get();
    @noSideEffects bit<16> get_state();
    void set_state(in bit<16> checksum_state);
}

enum PSA_CounterType_t {
    PACKETS,
    BYTES,
    PACKETS_AND_BYTES
}

extern Counter<W, S> {
    Counter(bit<32> n_counters, PSA_CounterType_t type);
    void count(in S index);
}

extern DirectCounter<W> {
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

extern Meter<S> {
    Meter(bit<32> n_meters, PSA_MeterType_t type);
    PSA_MeterColor_t execute(in S index, in PSA_MeterColor_t color);
    PSA_MeterColor_t execute(in S index);
}

extern DirectMeter {
    DirectMeter(PSA_MeterType_t type);
    PSA_MeterColor_t execute(in PSA_MeterColor_t color);
    PSA_MeterColor_t execute();
}

extern Register<T, S> {
    Register(bit<32> size);
    Register(bit<32> size, T initial_value);
    @noSideEffects T read(in S index);
    void write(in S index, in T value);
}

extern Random<T> {
    Random(T min, T max);
    T read();
}

extern ActionProfile {
    ActionProfile(bit<32> size);
}

extern ActionSelector {
    ActionSelector(PSA_HashAlgorithm_t algo, bit<32> size, bit<32> outputWidth);
}

extern Digest<T> {
    Digest();
    void pack(in T data);
}

parser IngressParser<H, M, RESUBM, RECIRCM>(packet_in buffer, out H parsed_hdr, inout M user_meta, in psa_ingress_parser_input_metadata_t istd, in RESUBM resubmit_meta, in RECIRCM recirculate_meta);
control Ingress<H, M>(inout H hdr, inout M user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd);
control IngressDeparser<H, M, CI2EM, RESUBM, NM>(packet_out buffer, out CI2EM clone_i2e_meta, out RESUBM resubmit_meta, out NM normal_meta, inout H hdr, in M meta, in psa_ingress_output_metadata_t istd);
parser EgressParser<H, M, NM, CI2EM, CE2EM>(packet_in buffer, out H parsed_hdr, inout M user_meta, in psa_egress_parser_input_metadata_t istd, in NM normal_meta, in CI2EM clone_i2e_meta, in CE2EM clone_e2e_meta);
control Egress<H, M>(inout H hdr, inout M user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd);
control EgressDeparser<H, M, CE2EM, RECIRCM>(packet_out buffer, out CE2EM clone_e2e_meta, out RECIRCM recirculate_meta, inout H hdr, in M meta, in psa_egress_output_metadata_t istd, in psa_egress_deparser_input_metadata_t edstd);
package IngressPipeline<IH, IM, NM, CI2EM, RESUBM, RECIRCM>(IngressParser<IH, IM, RESUBM, RECIRCM> ip, Ingress<IH, IM> ig, IngressDeparser<IH, IM, CI2EM, RESUBM, NM> id);
package EgressPipeline<EH, EM, NM, CI2EM, CE2EM, RECIRCM>(EgressParser<EH, EM, NM, CI2EM, CE2EM> ep, Egress<EH, EM> eg, EgressDeparser<EH, EM, CE2EM, RECIRCM> ed);
package PSA_Switch<IH, IM, EH, EM, NM, CI2EM, CE2EM, RESUBM, RECIRCM>(IngressPipeline<IH, IM, NM, CI2EM, RESUBM, RECIRCM> ingress, PacketReplicationEngine pre, EgressPipeline<EH, EM, NM, CI2EM, CE2EM, RECIRCM> egress, BufferingQueueingEngine bqe);
typedef bit<48> EthernetAddress;
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
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
    tcp_t      tcp;
}

typedef bit<32> PacketCounter_t;
typedef bit<8> ErrorIndex_t;
struct tuple_0 {
    bit<4>  f0;
    bit<4>  f1;
    bit<8>  f2;
    bit<16> f3;
    bit<16> f4;
    bit<3>  f5;
    bit<13> f6;
    bit<8>  f7;
    bit<8>  f8;
    bit<32> f9;
    bit<32> f10;
}

parser IngressParserImpl(packet_in buffer, out headers hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
    @name("IngressParserImpl.tmp") bit<16> tmp;
    @name("IngressParserImpl.tmp_0") bool tmp_0;
    @name("IngressParserImpl.tmp_1") bool tmp_1;
    @name("IngressParserImpl.ck") InternetChecksum() ck_0;
    state start {
        buffer.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        buffer.extract<ipv4_t>(hdr.ipv4);
        verify(hdr.ipv4.ihl == 4w5, error.UnhandledIPv4Options);
        ck_0.clear();
        ck_0.add<tuple_0>((tuple_0){f0 = hdr.ipv4.version,f1 = hdr.ipv4.ihl,f2 = hdr.ipv4.diffserv,f3 = hdr.ipv4.totalLen,f4 = hdr.ipv4.identification,f5 = hdr.ipv4.flags,f6 = hdr.ipv4.fragOffset,f7 = hdr.ipv4.ttl,f8 = hdr.ipv4.protocol,f9 = hdr.ipv4.srcAddr,f10 = hdr.ipv4.dstAddr});
        tmp = ck_0.get();
        tmp_0 = tmp == hdr.ipv4.hdrChecksum;
        tmp_1 = tmp_0;
        verify(tmp_1, error.BadIPv4HeaderChecksum);
        transition select(hdr.ipv4.protocol) {
            8w6: parse_tcp;
            default: accept;
        }
    }
    state parse_tcp {
        buffer.extract<tcp_t>(hdr.tcp);
        transition accept;
    }
}

control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
    bool hasExited;
    @name("ingress.meta") psa_ingress_output_metadata_t meta_0;
    @noWarnUnused @name(".ingress_drop") action ingress_drop_0() {
        {
            meta_0.class_of_service = ostd.class_of_service;
            meta_0.clone = ostd.clone;
            meta_0.clone_session_id = ostd.clone_session_id;
            meta_0.drop = ostd.drop;
            meta_0.resubmit = ostd.resubmit;
            meta_0.multicast_group = ostd.multicast_group;
            meta_0.egress_port = ostd.egress_port;
        }
        meta_0.drop = true;
        {
            ostd.class_of_service = meta_0.class_of_service;
            ostd.clone = meta_0.clone;
            ostd.clone_session_id = meta_0.clone_session_id;
            ostd.drop = true;
            ostd.resubmit = meta_0.resubmit;
            ostd.multicast_group = meta_0.multicast_group;
            ostd.egress_port = meta_0.egress_port;
        }
    }
    @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts_0;
    @name("ingress.set_error_idx") action set_error_idx(@name("idx") ErrorIndex_t idx) {
        parser_error_counts_0.count();
    }
    @name("ingress.parser_error_count_and_convert") table parser_error_count_and_convert_0 {
        key = {
            istd.parser_error: exact @name("istd.parser_error") ;
        }
        actions = {
            set_error_idx();
        }
        default_action = set_error_idx(8w0);
        const entries = {
                        error.NoError : set_error_idx(8w1);
                        error.PacketTooShort : set_error_idx(8w2);
                        error.NoMatch : set_error_idx(8w3);
                        error.StackOutOfBounds : set_error_idx(8w4);
                        error.HeaderTooShort : set_error_idx(8w5);
                        error.ParserTimeout : set_error_idx(8w6);
                        error.BadIPv4HeaderChecksum : set_error_idx(8w7);
                        error.UnhandledIPv4Options : set_error_idx(8w8);
        }
        psa_direct_counter = parser_error_counts_0;
    }
    apply {
        hasExited = false;
        if (istd.parser_error != error.NoError) {
            parser_error_count_and_convert_0.apply();
            ingress_drop_0();
            hasExited = true;
        }
        if (!hasExited) {
        }
    }
}

parser EgressParserImpl(packet_in buffer, out headers hdr, inout metadata user_meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
    state start {
        transition accept;
    }
}

control egress(inout headers hdr, inout metadata user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
    apply {
    }
}

control IngressDeparserImpl(packet_out packet, out empty_metadata_t clone_i2e_meta, out empty_metadata_t resubmit_meta, out empty_metadata_t normal_meta, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
        packet.emit<tcp_t>(hdr.tcp);
    }
}

control EgressDeparserImpl(packet_out packet, out empty_metadata_t clone_e2e_meta, out empty_metadata_t recirculate_meta, inout headers hdr, in metadata meta, in psa_egress_output_metadata_t istd, in psa_egress_deparser_input_metadata_t edstd) {
    @name("EgressDeparserImpl.ck") InternetChecksum() ck_1;
    apply {
        ck_1.clear();
        ck_1.add<tuple_0>((tuple_0){f0 = hdr.ipv4.version,f1 = hdr.ipv4.ihl,f2 = hdr.ipv4.diffserv,f3 = hdr.ipv4.totalLen,f4 = hdr.ipv4.identification,f5 = hdr.ipv4.flags,f6 = hdr.ipv4.fragOffset,f7 = hdr.ipv4.ttl,f8 = hdr.ipv4.protocol,f9 = hdr.ipv4.srcAddr,f10 = hdr.ipv4.dstAddr});
        hdr.ipv4.hdrChecksum = ck_1.get();
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
        packet.emit<tcp_t>(hdr.tcp);
    }
}

IngressPipeline<headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(IngressParserImpl(), ingress(), IngressDeparserImpl()) ip;

EgressPipeline<headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(EgressParserImpl(), egress(), EgressDeparserImpl()) ep;

PSA_Switch<headers, metadata, headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;

