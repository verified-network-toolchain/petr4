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

typedef bit<32> PortIdUint_t;
typedef bit<32> MulticastGroupUint_t;
typedef bit<16> CloneSessionIdUint_t;
typedef bit<8> ClassOfServiceUint_t;
typedef bit<16> EgressInstanceUint_t;
typedef bit<64> TimestampUint_t;
@p4runtime_translation("p4.org/psa/v1/PortId_t" , 32) type PortIdUint_t PortId_t;
@p4runtime_translation("p4.org/psa/v1/MulticastGroup_t" , 32) type MulticastGroupUint_t MulticastGroup_t;
@p4runtime_translation("p4.org/psa/v1/CloneSessionId_t" , 16) type CloneSessionIdUint_t CloneSessionId_t;
@p4runtime_translation("p4.org/psa/v1/ClassOfService_t" , 8) type ClassOfServiceUint_t ClassOfService_t;
@p4runtime_translation("p4.org/psa/v1/EgressInstance_t" , 16) type EgressInstanceUint_t EgressInstance_t;
@p4runtime_translation("p4.org/psa/v1/Timestamp_t" , 64) type TimestampUint_t Timestamp_t;
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
struct EMPTY {
}

typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

struct headers_t {
    ethernet_t ethernet;
}

parser MyIP(packet_in buffer, out headers_t hdr, inout EMPTY b, in psa_ingress_parser_input_metadata_t c, in EMPTY d, in EMPTY e) {
    state start {
        buffer.extract<ethernet_t>(hdr.ethernet);
        transition accept;
    }
}

parser MyEP(packet_in buffer, out EMPTY a, inout EMPTY b, in psa_egress_parser_input_metadata_t c, in EMPTY d, in EMPTY e, in EMPTY f) {
    state start {
        transition accept;
    }
}

control MyIC(inout headers_t hdr, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @name("ap") ActionProfile(32w1024) ap_0;
    @name("ap1") ActionProfile(32w1024) ap1_0;
    @name("a1") action a1(@name("param") bit<48> param_0) {
        hdr.ethernet.dstAddr = param_0;
    }
    @name("a2") action a2(@name("param") bit<16> param_1) {
        hdr.ethernet.etherType = param_1;
    }
    @name("tbl") table tbl_0 {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            NoAction_1();
            a1();
            a2();
        }
        psa_implementation = { ap_0, ap1_0 };
        default_action = NoAction_1();
    }
    apply {
        tbl_0.apply();
    }
}

control MyEC(inout EMPTY a, inout EMPTY b, in psa_egress_input_metadata_t c, inout psa_egress_output_metadata_t d) {
    apply {
    }
}

control MyID(packet_out buffer, out EMPTY a, out EMPTY b, out EMPTY c, inout headers_t hdr, in EMPTY e, in psa_ingress_output_metadata_t f) {
    apply {
        buffer.emit<ethernet_t>(hdr.ethernet);
    }
}

control MyED(packet_out buffer, out EMPTY a, out EMPTY b, inout EMPTY c, in EMPTY d, in psa_egress_output_metadata_t e, in psa_egress_deparser_input_metadata_t f) {
    apply {
    }
}

IngressPipeline<headers_t, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(MyIP(), MyIC(), MyID()) ip;

EgressPipeline<EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(MyEP(), MyEC(), MyED()) ep;

PSA_Switch<headers_t, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, EMPTY>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;

