error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument,
    IPv4OptionsNotSupported,
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
@noWarn("unused") action NoAction() {
}
match_kind {
    exact,
    ternary,
    lpm
}

typedef bit<4> PortId;
const PortId REAL_PORT_COUNT = 4w8;
struct InControl {
    PortId inputPort;
}

const PortId RECIRCULATE_IN_PORT = (bit<4>)4w0xd;
const PortId CPU_IN_PORT = (bit<4>)4w0xe;
struct OutControl {
    PortId outputPort;
}

const PortId DROP_PORT = (bit<4>)4w0xf;
const PortId CPU_OUT_PORT = (bit<4>)4w0xe;
const PortId RECIRCULATE_OUT_PORT = (bit<4>)4w0xd;
parser Parser<H>(packet_in b, out H parsedHeaders);
control Pipe<H>(inout H headers, in error parseError, in InControl inCtrl, out OutControl outCtrl);
control Deparser<H>(inout H outputHeaders, packet_out b);
package VSS<H>(Parser<H> p, Pipe<H> map, Deparser<H> d);
extern Ck16 {
    Ck16();
    void clear();
    void update<T>(in T data);
    bit<16> get();
}

typedef bit<48> EthernetAddress;
typedef bit<32> IPv4Address;
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header Ipv4_h {
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
}

struct Parsed_packet {
    Ethernet_h ethernet;
    Ipv4_h     ip;
}

parser TopParser(packet_in b, out Parsed_packet p) {
    Ck16() ck;
    state start {
        b.extract(p.ethernet);
        transition select(p.ethernet.etherType) {
            16w0x800: parse_ipv4;
        }
    }
    state parse_ipv4 {
        b.extract(p.ip);
        verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
        verify(p.ip.ihl == 4w5, error.IPv4OptionsNotSupported);
        ck.clear();
        ck.update(p.ip);
        verify(ck.get() == 16w0, error.IPv4ChecksumError);
        transition accept;
    }
}

control TopPipe(inout Parsed_packet headers, in error parseError, in InControl inCtrl, out OutControl outCtrl) {
    action Drop_action() {
        outCtrl.outputPort = DROP_PORT;
    }
    IPv4Address nextHop;
    action Set_nhop(IPv4Address ipv4_dest, PortId port) {
        nextHop = ipv4_dest;
        headers.ip.ttl = headers.ip.ttl - 8w1;
        outCtrl.outputPort = port;
    }
    table ipv4_match {
        key = {
            headers.ip.dstAddr: lpm;
        }
        actions = {
            Drop_action();
            Set_nhop();
        }
        size = 1024;
        default_action = Drop_action();
    }
    action Send_to_cpu() {
        outCtrl.outputPort = CPU_OUT_PORT;
    }
    table check_ttl {
        key = {
            headers.ip.ttl: exact;
        }
        actions = {
            Send_to_cpu();
            NoAction();
        }
        const default_action = NoAction();
    }
    action Set_dmac(EthernetAddress dmac) {
        headers.ethernet.dstAddr = dmac;
    }
    table dmac {
        key = {
            nextHop: exact;
        }
        actions = {
            Drop_action();
            Set_dmac();
        }
        size = 1024;
        default_action = Drop_action();
    }
    action Set_smac(EthernetAddress smac) {
        headers.ethernet.srcAddr = smac;
    }
    table smac {
        key = {
            outCtrl.outputPort: exact;
        }
        actions = {
            Drop_action();
            Set_smac();
        }
        size = 16;
        default_action = Drop_action();
    }
    apply {
        if (parseError != error.NoError) {
            Drop_action();
            return;
        }
        ipv4_match.apply();
        if (outCtrl.outputPort == DROP_PORT) {
            return;
        }
        check_ttl.apply();
        if (outCtrl.outputPort == CPU_OUT_PORT) {
            return;
        }
        dmac.apply();
        if (outCtrl.outputPort == DROP_PORT) {
            return;
        }
        smac.apply();
    }
}

control TopDeparser(inout Parsed_packet p, packet_out b) {
    Ck16() ck;
    apply {
        b.emit(p.ethernet);
        if (p.ip.isValid()) {
            ck.clear();
            p.ip.hdrChecksum = 16w0;
            ck.update(p.ip);
            p.ip.hdrChecksum = ck.get();
        }
        b.emit(p.ip);
    }
}

VSS(TopParser(), TopPipe(), TopDeparser()) main;

