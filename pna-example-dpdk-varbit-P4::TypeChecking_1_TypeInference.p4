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
typedef bit<8> ClassOfServiceUint_t;
typedef bit<64> TimestampUint_t;
typedef bit<3> PassNumberUint_t;
typedef bit<32> SecurityAssocIdUint_t;
@p4runtime_translation("p4.org/pna/v1/PortId_t" , 32) type PortIdUint_t PortId_t;
@p4runtime_translation("p4.org/pna/v1/ClassOfService_t" , 8) type ClassOfServiceUint_t ClassOfService_t;
@p4runtime_translation("p4.org/pna/v1/Timestamp_t" , 64) type TimestampUint_t Timestamp_t;
@p4runtime_translation("p4.org/pna/v1/PassNumber_t" , 8) type PassNumberUint_t PassNumber_t;
@p4runtime_translation("p4.org/pna/v1/SecurityAssocId_t" , 64) type SecurityAssocIdUint_t SecurityAssocId_t;
typedef error ParserError_t;
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

extern void send_to_port(PortId_t dest_port);
control PreControlT<PH, PM>(in PH pre_hdr, inout PM pre_user_meta, in pna_pre_input_metadata_t istd, inout pna_pre_output_metadata_t ostd);
parser MainParserT<PM, MH, MM>(packet_in pkt, out MH main_hdr, inout MM main_user_meta, in pna_main_parser_input_metadata_t istd);
control MainControlT<PM, MH, MM>(inout MH main_hdr, inout MM main_user_meta, in pna_main_input_metadata_t istd, inout pna_main_output_metadata_t ostd);
control MainDeparserT<MH, MM>(packet_out pkt, in MH main_hdr, in MM main_user_meta, in pna_main_output_metadata_t ostd);
package PNA_NIC<PH, PM, MH, MM>(MainParserT<PM, MH, MM> main_parser, PreControlT<PH, PM> pre_control, MainControlT<PM, MH, MM> main_control, MainDeparserT<MH, MM> main_deparser);
typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header ipv4_base_t {
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

header ipv4_option_timestamp_t {
    bit<8>      value;
    bit<8>      len;
    varbit<304> data;
}

struct main_metadata_t {
}

struct headers_t {
    ethernet_t              ethernet;
    ipv4_base_t             ipv4_base;
    ipv4_option_timestamp_t ipv4_option_timestamp;
}

parser MainParserImpl(packet_in pkt, out headers_t hdr, inout main_metadata_t main_meta, in pna_main_parser_input_metadata_t istd) {
    @name("tmp16") bit<16> tmp16_0;
    @name("tmp_len") bit<8> tmp_len_0;
    @name("tmp") bit<8> tmp;
    @name("tmp_0") bit<8> tmp_0;
    state start {
        pkt.extract<ethernet_t>(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        pkt.extract<ipv4_base_t>(hdr.ipv4_base);
        transition select(hdr.ipv4_base.ihl) {
            4w0x5: accept;
            default: parse_ipv4_options;
        }
    }
    state parse_ipv4_option_timestamp {
        tmp16_0 = pkt.lookahead<bit<16>>();
        tmp_len_0 = tmp16_0[7:0];
        pkt.extract<ipv4_option_timestamp_t>(hdr.ipv4_option_timestamp, ((bit<32>)tmp_len_0 << 3) + 32w4294967280);
        transition accept;
    }
    state parse_ipv4_options {
        tmp_0 = pkt.lookahead<bit<8>>();
        tmp = tmp_0;
        transition select(tmp) {
            8w0x44: parse_ipv4_option_timestamp;
            default: accept;
        }
    }
}

control PreControlImpl(in headers_t hdr, inout main_metadata_t meta, in pna_pre_input_metadata_t istd, inout pna_pre_output_metadata_t ostd) {
    apply {
    }
}

control MainControlImpl(inout headers_t hdr, inout main_metadata_t user_meta, in pna_main_input_metadata_t istd, inout pna_main_output_metadata_t ostd) {
    @noWarn("unused") @name(".NoAction") action NoAction_1() {
    }
    @noWarn("unused") @name(".NoAction") action NoAction_2() {
    }
    @name("a1") action a1(@name("param") bit<48> param) {
        hdr.ethernet.dstAddr = param;
    }
    @name("a2") action a2(@name("param") bit<16> param_2) {
        hdr.ethernet.etherType = param_2;
    }
    @name("tbl") table tbl_0 {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            NoAction_1();
            a2();
        }
        default_action = NoAction_1();
    }
    @name("tbl2") table tbl2_0 {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            NoAction_2();
            a1();
        }
        default_action = NoAction_2();
    }
    apply {
        send_to_port((PortId_t)32w0);
        tbl_0.apply();
        tbl2_0.apply();
    }
}

control MainDeparserImpl(packet_out pkt, in headers_t hdr, in main_metadata_t user_meta, in pna_main_output_metadata_t ostd) {
    apply {
        pkt.emit<ethernet_t>(hdr.ethernet);
        pkt.emit<ipv4_base_t>(hdr.ipv4_base);
    }
}

PNA_NIC<headers_t, main_metadata_t, headers_t, main_metadata_t>(MainParserImpl(), PreControlImpl(), MainControlImpl(), MainDeparserImpl()) main;

