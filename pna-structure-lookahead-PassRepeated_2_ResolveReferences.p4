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
@p4runtime_translation("p4.org/pna/v1/PortId_t" , 32) type PortIdUint_t PortId_t;
@p4runtime_translation("p4.org/pna/v1/InterfaceId_t" , 32) type InterfaceIdUint_t InterfaceId_t;
@p4runtime_translation("p4.org/pna/v1/MulticastGroup_t" , 32) type MulticastGroupUint_t MulticastGroup_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSessionId_t" , 16) type MirrorSessionIdUint_t MirrorSessionId_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSlotId_t" , 8) type MirrorSlotIdUint_t MirrorSlotId_t;
@p4runtime_translation("p4.org/pna/v1/ClassOfService_t" , 8) type ClassOfServiceUint_t ClassOfService_t;
@p4runtime_translation("p4.org/pna/v1/PacketLength_t" , 16) type PacketLengthUint_t PacketLength_t;
@p4runtime_translation("p4.org/pna/v1/MulticastInstance_t" , 16) type MulticastInstanceUint_t MulticastInstance_t;
@p4runtime_translation("p4.org/pna/v1/Timestamp_t" , 64) type TimestampUint_t Timestamp_t;
@p4runtime_translation("p4.org/pna/v1/FlowId_t" , 32) type FlowIdUint_t FlowId_t;
@p4runtime_translation("p4.org/pna/v1/ExpireTimeProfileId_t" , 8) type ExpireTimeProfileIdUint_t ExpireTimeProfileId_t;
@p4runtime_translation("p4.org/pna/v1/PassNumber_t" , 8) type PassNumberUint_t PassNumber_t;
@p4runtime_translation("p4.org/pna/v1/SecurityAssocId_t" , 64) type SecurityAssocIdUint_t SecurityAssocId_t;
typedef error ParserError_t;
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
@p4runtime_translation("p4.org/pna/v1/PortIdInHeader_t" , 32) type PortIdInHeaderUint_t PortIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/InterfaceIdInHeader_t" , 32) type InterfaceIdInHeaderUint_t InterfaceIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MulticastGroupInHeader_t" , 32) type MulticastGroupInHeaderUint_t MulticastGroupInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MirrorSessionIdInHeader_t" , 16) type MirrorSessionIdInHeaderUint_t MirrorSessionIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/ClassOfServiceInHeader_t" , 8) type ClassOfServiceInHeaderUint_t ClassOfServiceInHeader_t;
@p4runtime_translation("p4.org/pna/v1/PacketLengthInHeader_t" , 16) type PacketLengthInHeaderUint_t PacketLengthInHeader_t;
@p4runtime_translation("p4.org/pna/v1/MulticastInstanceInHeader_t" , 16) type MulticastInstanceInHeaderUint_t MulticastInstanceInHeader_t;
@p4runtime_translation("p4.org/pna/v1/TimestampInHeader_t" , 64) type TimestampInHeaderUint_t TimestampInHeader_t;
@p4runtime_translation("p4.org/pna/v1/FlowIdInHeader_t" , 32) type FlowIdInHeaderUint_t FlowIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/ExpireTimeProfileIdInHeader_t" , 8) type ExpireTimeProfileIdInHeaderUint_t ExpireTimeProfileIdInHeader_t;
@p4runtime_translation("p4.org/pna/v1/PassNumberInHeader_t" , 8) type PassNumberInHeaderUint_t PassNumberInHeader_t;
match_kind {
    range,
    selector
}

enum PNA_HashAlgorithm_t {
    TARGET_DEFAULT
}

extern Hash<O> {
    Hash(PNA_HashAlgorithm_t algo);
    O get_hash<D>(in D data);
    O get_hash<T, D>(in T base, in D data, in T max);
}

extern Checksum<W> {
    Checksum(PNA_HashAlgorithm_t hash);
    void clear();
    void update<T>(in T data);
    W get();
}

extern InternetChecksum {
    InternetChecksum();
    void clear();
    void add<T>(in T data);
    void subtract<T>(in T data);
    bit<16> get();
    bit<16> get_state();
    void set_state(in bit<16> checksum_state);
}

enum PNA_CounterType_t {
    PACKETS,
    BYTES,
    PACKETS_AND_BYTES
}

extern Counter<W, S> {
    Counter(bit<32> n_counters, PNA_CounterType_t type);
    void count(in S index);
}

extern DirectCounter<W> {
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

extern Meter<S> {
    Meter(bit<32> n_meters, PNA_MeterType_t type);
    PNA_MeterColor_t execute(in S index, in PNA_MeterColor_t color);
    PNA_MeterColor_t execute(in S index);
}

extern DirectMeter {
    DirectMeter(PNA_MeterType_t type);
    PNA_MeterColor_t execute(in PNA_MeterColor_t color);
    PNA_MeterColor_t execute();
}

extern Register<T, S> {
    Register(bit<32> size);
    Register(bit<32> size, T initial_value);
    T read(in S index);
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
    ActionSelector(PNA_HashAlgorithm_t algo, bit<32> size, bit<32> outputWidth);
}

extern Digest<T> {
    Digest();
    void pack(in T data);
}

enum PNA_Direction_t {
    NET_TO_HOST,
    HOST_TO_NET
}

struct pna_pre_input_metadata_t {
    PortId_t        input_port;
    ParserError_t   parser_error;
    PNA_Direction_t direction;
    PassNumber_t    pass;
    bool            loopedback;
}

struct pna_pre_output_metadata_t {
    bool              decrypt;
    SecurityAssocId_t said;
    bit<16>           decrypt_start_offset;
}

struct pna_main_parser_input_metadata_t {
    PNA_Direction_t direction;
    PassNumber_t    pass;
    bool            loopedback;
    PortId_t        input_port;
}

struct pna_main_input_metadata_t {
    PNA_Direction_t  direction;
    PassNumber_t     pass;
    bool             loopedback;
    Timestamp_t      timestamp;
    ParserError_t    parser_error;
    ClassOfService_t class_of_service;
    PortId_t         input_port;
}

struct pna_main_output_metadata_t {
    ClassOfService_t class_of_service;
}

control PreControlT<PH, PM>(in PH pre_hdr, inout PM pre_user_meta, in pna_pre_input_metadata_t istd, inout pna_pre_output_metadata_t ostd);
parser MainParserT<PM, MH, MM>(packet_in pkt, out MH main_hdr, inout MM main_user_meta, in pna_main_parser_input_metadata_t istd);
control MainControlT<PM, MH, MM>(inout MH main_hdr, inout MM main_user_meta, in pna_main_input_metadata_t istd, inout pna_main_output_metadata_t ostd);
control MainDeparserT<MH, MM>(packet_out pkt, in MH main_hdr, in MM main_user_meta, in pna_main_output_metadata_t ostd);
package PNA_NIC<PH, PM, MH, MM>(MainParserT<PM, MH, MM> main_parser, PreControlT<PH, PM> pre_control, MainControlT<PM, MH, MM> main_control, MainDeparserT<MH, MM> main_deparser);
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

parser MainParserImpl(packet_in pkt, out headers_t hdr, inout main_metadata_t main_meta, in pna_main_parser_input_metadata_t istd) {
    state start {
        my_struct_t tmp = pkt.lookahead<my_struct_t>();
        transition select(tmp.type2) {
            8w1: parse_header;
            default: accept;
        }
    }
    state parse_header {
        pkt.extract<my_header_t>(hdr.h);
        transition accept;
    }
}

control PreControlImpl(in headers_t hdr, inout main_metadata_t meta, in pna_pre_input_metadata_t istd, inout pna_pre_output_metadata_t ostd) {
    apply {
    }
}

control MainControlImpl(inout headers_t hdr, inout main_metadata_t user_meta, in pna_main_input_metadata_t istd, inout pna_main_output_metadata_t ostd) {
    apply {
    }
}

control MainDeparserImpl(packet_out pkt, in headers_t hdr, in main_metadata_t user_meta, in pna_main_output_metadata_t ostd) {
    apply {
    }
}

PNA_NIC<headers_t, main_metadata_t, headers_t, main_metadata_t>(MainParserImpl(), PreControlImpl(), MainControlImpl(), MainDeparserImpl()) main;

