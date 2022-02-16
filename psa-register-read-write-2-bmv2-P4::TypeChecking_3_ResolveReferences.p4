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

extern void verify(in bool check, in error toSignal);
@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

typedef bit<32> PortIdUint_t;
typedef bit<32> MulticastGroupUint_t;
typedef bit<16> CloneSessionIdUint_t;
typedef bit<8> ClassOfServiceUint_t;
typedef bit<16> PacketLengthUint_t;
typedef bit<16> EgressInstanceUint_t;
typedef bit<64> TimestampUint_t;
@p4runtime_translation("p4.org/psa/v1/PortId_t" , 32) type PortIdUint_t PortId_t;
@p4runtime_translation("p4.org/psa/v1/MulticastGroup_t" , 32) type MulticastGroupUint_t MulticastGroup_t;
@p4runtime_translation("p4.org/psa/v1/CloneSessionId_t" , 16) type CloneSessionIdUint_t CloneSessionId_t;
@p4runtime_translation("p4.org/psa/v1/ClassOfService_t" , 8) type ClassOfServiceUint_t ClassOfService_t;
@p4runtime_translation("p4.org/psa/v1/PacketLength_t" , 16) type PacketLengthUint_t PacketLength_t;
@p4runtime_translation("p4.org/psa/v1/EgressInstance_t" , 16) type EgressInstanceUint_t EgressInstance_t;
@p4runtime_translation("p4.org/psa/v1/Timestamp_t" , 64) type TimestampUint_t Timestamp_t;
typedef error ParserError_t;
const PortId_t PSA_PORT_RECIRCULATE = (PortId_t)32w0xfffffffa;
const PortId_t PSA_PORT_CPU = (PortId_t)32w0xfffffffd;
const CloneSessionId_t PSA_CLONE_SESSION_TO_CPU = (CloneSessionId_t)16w0;
typedef bit<32> PortIdInHeaderUint_t;
typedef bit<32> MulticastGroupInHeaderUint_t;
typedef bit<16> CloneSessionIdInHeaderUint_t;
typedef bit<8> ClassOfServiceInHeaderUint_t;
typedef bit<16> PacketLengthInHeaderUint_t;
typedef bit<16> EgressInstanceInHeaderUint_t;
typedef bit<64> TimestampInHeaderUint_t;
@p4runtime_translation("p4.org/psa/v1/PortIdInHeader_t" , 32) type PortIdInHeaderUint_t PortIdInHeader_t;
@p4runtime_translation("p4.org/psa/v1/MulticastGroupInHeader_t" , 32) type MulticastGroupInHeaderUint_t MulticastGroupInHeader_t;
@p4runtime_translation("p4.org/psa/v1/CloneSessionIdInHeader_t" , 16) type CloneSessionIdInHeaderUint_t CloneSessionIdInHeader_t;
@p4runtime_translation("p4.org/psa/v1/ClassOfServiceInHeader_t" , 8) type ClassOfServiceInHeaderUint_t ClassOfServiceInHeader_t;
@p4runtime_translation("p4.org/psa/v1/PacketLengthInHeader_t" , 16) type PacketLengthInHeaderUint_t PacketLengthInHeader_t;
@p4runtime_translation("p4.org/psa/v1/EgressInstanceInHeader_t" , 16) type EgressInstanceInHeaderUint_t EgressInstanceInHeader_t;
@p4runtime_translation("p4.org/psa/v1/TimestampInHeader_t" , 64) type TimestampInHeaderUint_t TimestampInHeader_t;
PortId_t psa_PortId_header_to_int(in PortIdInHeader_t x) {
    return (PortId_t)(PortIdUint_t)(PortIdInHeaderUint_t)x;
}
MulticastGroup_t psa_MulticastGroup_header_to_int(in MulticastGroupInHeader_t x) {
    return (MulticastGroup_t)(MulticastGroupUint_t)(MulticastGroupInHeaderUint_t)x;
}
CloneSessionId_t psa_CloneSessionId_header_to_int(in CloneSessionIdInHeader_t x) {
    return (CloneSessionId_t)(CloneSessionIdUint_t)(CloneSessionIdInHeaderUint_t)x;
}
ClassOfService_t psa_ClassOfService_header_to_int(in ClassOfServiceInHeader_t x) {
    return (ClassOfService_t)(ClassOfServiceUint_t)(ClassOfServiceInHeaderUint_t)x;
}
PacketLength_t psa_PacketLength_header_to_int(in PacketLengthInHeader_t x) {
    return (PacketLength_t)(PacketLengthUint_t)(PacketLengthInHeaderUint_t)x;
}
EgressInstance_t psa_EgressInstance_header_to_int(in EgressInstanceInHeader_t x) {
    return (EgressInstance_t)(EgressInstanceUint_t)(EgressInstanceInHeaderUint_t)x;
}
Timestamp_t psa_Timestamp_header_to_int(in TimestampInHeader_t x) {
    return (Timestamp_t)(TimestampUint_t)(TimestampInHeaderUint_t)x;
}
PortIdInHeader_t psa_PortId_int_to_header(in PortId_t x) {
    return (PortIdInHeader_t)(PortIdInHeaderUint_t)(PortIdUint_t)x;
}
MulticastGroupInHeader_t psa_MulticastGroup_int_to_header(in MulticastGroup_t x) {
    return (MulticastGroupInHeader_t)(MulticastGroupInHeaderUint_t)(MulticastGroupUint_t)x;
}
CloneSessionIdInHeader_t psa_CloneSessionId_int_to_header(in CloneSessionId_t x) {
    return (CloneSessionIdInHeader_t)(CloneSessionIdInHeaderUint_t)(CloneSessionIdUint_t)x;
}
ClassOfServiceInHeader_t psa_ClassOfService_int_to_header(in ClassOfService_t x) {
    return (ClassOfServiceInHeader_t)(ClassOfServiceInHeaderUint_t)(ClassOfServiceUint_t)x;
}
PacketLengthInHeader_t psa_PacketLength_int_to_header(in PacketLength_t x) {
    return (PacketLengthInHeader_t)(PacketLengthInHeaderUint_t)(PacketLengthUint_t)x;
}
EgressInstanceInHeader_t psa_EgressInstance_int_to_header(in EgressInstance_t x) {
    return (EgressInstanceInHeader_t)(EgressInstanceInHeaderUint_t)(EgressInstanceUint_t)x;
}
TimestampInHeader_t psa_Timestamp_int_to_header(in Timestamp_t x) {
    return (TimestampInHeader_t)(TimestampInHeaderUint_t)(TimestampUint_t)x;
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

@pure extern bool psa_clone_i2e(in psa_ingress_output_metadata_t istd);
@pure extern bool psa_resubmit(in psa_ingress_output_metadata_t istd);
@pure extern bool psa_normal(in psa_ingress_output_metadata_t istd);
@pure extern bool psa_clone_e2e(in psa_egress_output_metadata_t istd);
@pure extern bool psa_recirculate(in psa_egress_output_metadata_t istd, in psa_egress_deparser_input_metadata_t edstd);
extern void assert(in bool check);
extern void assume(in bool check);
match_kind {
    range,
    selector,
    optional
}

@noWarnUnused action send_to_port(inout psa_ingress_output_metadata_t meta, in PortId_t egress_port) {
    meta.drop = false;
    meta.multicast_group = (MulticastGroup_t)32w0;
    meta.egress_port = egress_port;
}
@noWarnUnused action multicast(inout psa_ingress_output_metadata_t meta, in MulticastGroup_t multicast_group) {
    meta.drop = false;
    meta.multicast_group = multicast_group;
}
@noWarnUnused action ingress_drop(inout psa_ingress_output_metadata_t meta) {
    meta.drop = true;
}
@noWarnUnused action egress_drop(inout psa_egress_output_metadata_t meta) {
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
struct EMPTY {
}

typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header output_data_t {
    bit<32> word0;
    bit<32> word1;
    bit<32> word2;
    bit<32> word3;
}

struct headers_t {
    ethernet_t    ethernet;
    output_data_t output_data;
}

struct metadata_t {
}

parser MyIP(packet_in pkt, out headers_t hdr, inout metadata_t user_meta, in psa_ingress_parser_input_metadata_t istd, in EMPTY resubmit_meta, in EMPTY recirculate_meta) {
    state start {
        pkt.extract<ethernet_t>(hdr.ethernet);
        pkt.extract<output_data_t>(hdr.output_data);
        transition accept;
    }
}

parser MyEP(packet_in pkt, out headers_t hdr, inout metadata_t user_meta, in psa_egress_parser_input_metadata_t istd, in EMPTY normal_meta, in EMPTY clone_i2e_meta, in EMPTY clone_e2e_meta) {
    state start {
        transition accept;
    }
}

control MyIC(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
    Register<bit<16>, bit<8>>(32w6) reg;
    bit<8> idx;
    bit<8> action_type;
    bit<16> orig_data;
    bit<16> next_data;
    apply {
        if (hdr.ethernet.isValid()) {
            idx = hdr.ethernet.dstAddr[7:0];
            action_type = hdr.ethernet.dstAddr[15:8];
            bool validAction = action_type >= 8w1 && action_type <= 8w3;
            if (validAction) {
                orig_data = reg.read(idx);
            }
            if (action_type == 8w1) {
                next_data = hdr.ethernet.dstAddr[47:32];
            } else if (action_type == 8w2) {
                next_data = orig_data;
            } else if (action_type == 8w3) {
                next_data = orig_data + 16w1;
            } else {
                orig_data = 16w0xdead;
                next_data = 16w0xbeef;
            }
            reg.write(idx, next_data);
            hdr.output_data.word0 = (bit<32>)orig_data;
            hdr.output_data.word1 = (bit<32>)next_data;
        }
        send_to_port(ostd, (PortId_t)32w1);
    }
}

control MyEC(inout headers_t hdr, inout metadata_t user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
    apply {
    }
}

control MyID(packet_out pkt, out EMPTY clone_i2e_meta, out EMPTY resubmit_meta, out EMPTY normal_meta, inout headers_t hdr, in metadata_t user_meta, in psa_ingress_output_metadata_t istd) {
    apply {
        pkt.emit<ethernet_t>(hdr.ethernet);
        pkt.emit<output_data_t>(hdr.output_data);
    }
}

control MyED(packet_out pkt, out EMPTY clone_e2e_meta, out EMPTY recirculate_meta, inout headers_t hdr, in metadata_t user_meta, in psa_egress_output_metadata_t istd, in psa_egress_deparser_input_metadata_t edstd) {
    apply {
    }
}

IngressPipeline<headers_t, metadata_t, EMPTY, EMPTY, EMPTY, EMPTY>(MyIP(), MyIC(), MyID()) ip;

EgressPipeline<headers_t, metadata_t, EMPTY, EMPTY, EMPTY, EMPTY>(MyEP(), MyEC(), MyED()) ep;

PSA_Switch<headers_t, metadata_t, headers_t, metadata_t, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;

