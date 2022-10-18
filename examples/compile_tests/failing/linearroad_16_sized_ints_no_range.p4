#include <core.p4>
#include <v1model.p4>

struct egress_metadata_t {
    bit<1> recirculate;
}

struct accident_meta_t {
    bit<8> cur_stp_cnt;
    bit<8> prev_stp_cnt;
    bit<8> accident_seg;
    bit<1> has_accident_ahead;
}

struct seg_metadata_t {
    bit<8>  vol;
    bit<8>  prev_vol;
    bit<16> ewma_spd;
}

struct stopped_metadata_t {
    bit<8> seg0l1;
    bit<8> seg0l2;
    bit<8> seg0l3;
    bit<8> seg1l1;
    bit<8> seg1l2;
    bit<8> seg1l3;
    bit<8> seg2l1;
    bit<8> seg2l2;
    bit<8> seg2l3;
    bit<8> seg3l1;
    bit<8> seg3l2;
    bit<8> seg3l3;
    bit<8> seg4l1;
    bit<8> seg4l2;
    bit<8> seg4l3;
    bit<8> seg0_ord;
    bit<8> seg1_ord;
    bit<8> seg2_ord;
    bit<8> seg3_ord;
    bit<8> seg4_ord;
}

struct travel_estimate_metadata_t {
    bit<1>  recirculated;
    bit<1>  dir;
    bit<8>  seg_cur;
    bit<8>  seg_end;
    bit<16> toll_sum;
    bit<16> time_sum;
}

struct toll_metadata_t {
    bit<16> toll;
    bit<1>  has_toll;
    bit<32> bal;
}

struct v_state_metadata_t {
    bit<1> new;
    bit<1> new_seg;
    bit<8> prev_spd;
    bit<8> prev_xway;
    bit<3> prev_lane;
    bit<8> prev_seg;
    bit<1> prev_dir;
    bit<3> prev_nomove_cnt;
    bit<3> nomove_cnt;
}

header accident_alert_t {
    bit<16> time;
    bit<32> vid;
    bit<16> emit;
    bit<8>  seg;
}

header accnt_bal_t {
    bit<16> time;
    bit<32> vid;
    bit<16> emit;
    bit<32> qid;
    bit<32> bal;
}

header accnt_bal_req_t {
    bit<16> time;
    bit<32> vid;
    bit<32> qid;
}

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header expenditure_report_t {
    bit<16> time;
    bit<16> emit;
    bit<32> qid;
    bit<16> bal;
}

header expenditure_req_t {
    bit<16> time;
    bit<32> vid;
    bit<32> qid;
    bit<8>  xway;
    bit<8>  day;
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

header lr_msg_type_t {
    bit<8> msg_type;
}

header pos_report_t {
    bit<16> time;
    bit<32> vid;
    bit<8>  spd;
    bit<8>  xway;
    bit<8>  lane;
    bit<8>  dir;
    bit<8>  seg;
}

header toll_notification_t {
    bit<16> time;
    bit<32> vid;
    bit<16> emit;
    bit<8>  spd;
    bit<16> toll;
}

header travel_estimate_t {
    bit<32> qid;
    bit<16> travel_time;
    bit<16> toll;
}

header travel_estimate_req_t {
    bit<16> time;
    bit<32> qid;
    bit<8>  xway;
    bit<8>  seg_init;
    bit<8>  seg_end;
    bit<8>  dow;
    bit<8>  tod;
}

header udp_t {
    bit<16> srcPort;
    bit<16> dstPort;
    bit<16> length_;
    bit<16> checksum;
}

struct metadata {
    @name(".accident_egress_meta") 
    egress_metadata_t          accident_egress_meta;
    @name(".accident_meta") 
    accident_meta_t            accident_meta;
    @name(".accnt_bal_egress_meta") 
    egress_metadata_t          accnt_bal_egress_meta;
    @name(".seg_meta") 
    seg_metadata_t             seg_meta;
    @name(".stopped_ahead") 
    stopped_metadata_t         stopped_ahead;
    @name(".te_md") 
    travel_estimate_metadata_t te_md;
    @name(".toll_egress_meta") 
    egress_metadata_t          toll_egress_meta;
    @name(".toll_meta") 
    toll_metadata_t            toll_meta;
    @name(".v_state") 
    v_state_metadata_t         v_state;
}

struct headers {
    @name(".accident_alert") 
    accident_alert_t      accident_alert;
    @name(".accnt_bal") 
    accnt_bal_t           accnt_bal;
    @name(".accnt_bal_req") 
    accnt_bal_req_t       accnt_bal_req;
    @name(".ethernet") 
    ethernet_t            ethernet;
    @name(".expenditure_report") 
    expenditure_report_t  expenditure_report;
    @name(".expenditure_req") 
    expenditure_req_t     expenditure_req;
    @name(".ipv4") 
    ipv4_t                ipv4;
    @name(".lr_msg_type") 
    lr_msg_type_t         lr_msg_type;
    @name(".pos_report") 
    pos_report_t          pos_report;
    @name(".toll_notification") 
    toll_notification_t   toll_notification;
    @name(".travel_estimate") 
    travel_estimate_t     travel_estimate;
    @name(".travel_estimate_req") 
    travel_estimate_req_t travel_estimate_req;
    @name(".udp") 
    udp_t                 udp;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".parse_accident_alert") state parse_accident_alert {
        packet.extract(hdr.accident_alert);
        transition accept;
    }
    @name(".parse_accnt_bal") state parse_accnt_bal {
        packet.extract(hdr.accnt_bal);
        transition accept;
    }
    @name(".parse_accnt_bal_req") state parse_accnt_bal_req {
        packet.extract(hdr.accnt_bal_req);
        transition accept;
    }
    @name(".parse_ethernet") state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    @name(".parse_expenditure_report") state parse_expenditure_report {
        packet.extract(hdr.expenditure_report);
        transition accept;
    }
    @name(".parse_expenditure_req") state parse_expenditure_req {
        packet.extract(hdr.expenditure_req);
        transition accept;
    }
    @name(".parse_ipv4") state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            8w0x11: parse_udp;
            default: accept;
        }
    }
    @name(".parse_lr") state parse_lr {
        packet.extract(hdr.lr_msg_type);
        transition select(hdr.lr_msg_type.msg_type) {
            8w0: parse_pos_report;
            8w2: parse_accnt_bal_req;
            8w10: parse_toll_notification;
            8w11: parse_accident_alert;
            8w12: parse_accnt_bal;
            8w3: parse_expenditure_req;
            8w13: parse_expenditure_report;
            8w4: parse_travel_estimate_req;
            8w14: parse_travel_estimate;
            default: accept;
        }
    }
    @name(".parse_pos_report") state parse_pos_report {
        packet.extract(hdr.pos_report);
        transition accept;
    }
    @name(".parse_toll_notification") state parse_toll_notification {
        packet.extract(hdr.toll_notification);
        transition accept;
    }
    @name(".parse_travel_estimate") state parse_travel_estimate {
        packet.extract(hdr.travel_estimate);
        transition accept;
    }
    @name(".parse_travel_estimate_req") state parse_travel_estimate_req {
        packet.extract(hdr.travel_estimate_req);
        transition accept;
    }
    @name(".parse_udp") state parse_udp {
        packet.extract(hdr.udp);
        transition select(hdr.udp.dstPort) {
            16w1234: parse_lr;
            default: accept;
        }
    }
    @name(".start") state start {
        transition parse_ethernet;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".make_expenditure_report") action make_expenditure_report(bit<16> bal) {
        hdr.lr_msg_type.msg_type = 8w13;
        hdr.expenditure_report.setValid();
        hdr.expenditure_report.time = hdr.expenditure_req.time;
        hdr.expenditure_report.emit = hdr.expenditure_req.time;
        hdr.expenditure_report.qid = hdr.expenditure_req.qid;
        hdr.expenditure_report.bal = bal;
        hdr.expenditure_req.setInvalid();
        hdr.ipv4.totalLen = 16w39;
        hdr.udp.length_ = 16w19;
        hdr.udp.checksum = 16w0;
    }
    @name(".accident_alert_e2e") action accident_alert_e2e(bit<32> mir_ses) {
        meta.accident_egress_meta.recirculate = 1w1;
        clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.accident_meta, meta.accident_egress_meta });
    }
    @name(".make_accident_alert") action make_accident_alert() {
        hdr.lr_msg_type.msg_type = 8w11;
        hdr.accident_alert.setValid();
        hdr.accident_alert.time = hdr.pos_report.time;
        hdr.accident_alert.vid = hdr.pos_report.vid;
        hdr.accident_alert.seg = meta.accident_meta.accident_seg;
        hdr.pos_report.setInvalid();
        hdr.ipv4.totalLen = 16w38;
        hdr.udp.length_ = 16w18;
        hdr.udp.checksum = 16w0;
    }
    @name(".accnt_bal_e2e") action accnt_bal_e2e(bit<32> mir_ses) {
        meta.accnt_bal_egress_meta.recirculate = 1w1;
        clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.toll_meta, meta.accnt_bal_egress_meta });
    }
    @name(".make_accnt_bal") action make_accnt_bal() {
        hdr.lr_msg_type.msg_type = 8w12;
        hdr.accnt_bal.setValid();
        hdr.accnt_bal.time = hdr.accnt_bal_req.time;
        hdr.accnt_bal.vid = hdr.accnt_bal_req.vid;
        hdr.accnt_bal.qid = hdr.accnt_bal_req.qid;
        hdr.accnt_bal.bal = meta.toll_meta.bal;
        hdr.accnt_bal_req.setInvalid();
        hdr.ipv4.totalLen = 16w45;
        hdr.udp.length_ = 16w25;
        hdr.udp.checksum = 16w0;
    }
    @name(".rewrite_mac") action rewrite_mac(bit<48> smac) {
        hdr.ethernet.srcAddr = smac;
    }
    @name("._drop") action _drop() {
        mark_to_drop();
    }
    @name(".toll_notification_e2e") action toll_notification_e2e(bit<32> mir_ses) {
        meta.toll_egress_meta.recirculate = 1w1;
        clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.toll_meta, meta.toll_egress_meta, meta.seg_meta });
    }
    @name(".make_toll_notification") action make_toll_notification() {
        hdr.lr_msg_type.msg_type = 8w10;
        hdr.toll_notification.setValid();
        hdr.toll_notification.time = hdr.pos_report.time;
        hdr.toll_notification.vid = hdr.pos_report.vid;
        hdr.toll_notification.spd = (bit<8>)meta.seg_meta.ewma_spd;
        hdr.toll_notification.toll = meta.toll_meta.toll;
        hdr.pos_report.setInvalid();
        hdr.ipv4.totalLen = 16w40;
        hdr.udp.length_ = 16w20;
        hdr.udp.checksum = 16w0;
    }
    @name(".update_travel_estimate") action update_travel_estimate(bit<16> time, bit<16> toll) {
        meta.te_md.time_sum = meta.te_md.time_sum + time;
        meta.te_md.toll_sum = meta.te_md.toll_sum + toll;
    }
    @name(".do_travel_estimate_init") action do_travel_estimate_init() {
        meta.te_md.dir = 1w0;
        meta.te_md.seg_cur = hdr.travel_estimate_req.seg_init;
        meta.te_md.seg_end = hdr.travel_estimate_req.seg_end;
    }
    @name(".do_travel_estimate_init_rev") action do_travel_estimate_init_rev() {
        meta.te_md.dir = 1w1;
        meta.te_md.seg_cur = hdr.travel_estimate_req.seg_end;
        meta.te_md.seg_end = hdr.travel_estimate_req.seg_init;
    }
    @name(".travel_estimate_e2e") action travel_estimate_e2e(bit<32> mir_ses) {
        meta.te_md.seg_cur = meta.te_md.seg_cur + 8w1;
        meta.te_md.recirculated = 1w1;
        clone3(CloneType.E2E, (bit<32>)mir_ses, { meta.te_md });
        mark_to_drop();
    }
    @name(".do_travel_estimate_send") action do_travel_estimate_send() {
        hdr.lr_msg_type.msg_type = 8w14;
        hdr.travel_estimate.setValid();
        hdr.travel_estimate.qid = hdr.travel_estimate_req.qid;
        hdr.travel_estimate.travel_time = meta.te_md.time_sum;
        hdr.travel_estimate.toll = meta.te_md.toll_sum;
        hdr.travel_estimate_req.setInvalid();
        hdr.ipv4.totalLen = 16w37;
        hdr.udp.length_ = 16w17;
        hdr.udp.checksum = 16w0;
    }
    @name(".daily_expenditure") table daily_expenditure {
        actions = {
            make_expenditure_report;
        }
        key = {
            hdr.expenditure_req.vid : exact;
            hdr.expenditure_req.day : exact;
            hdr.expenditure_req.xway: exact;
        }
        size = 1024;
    }
    @name(".send_accident_alert") table send_accident_alert {
        actions = {
            accident_alert_e2e;
            make_accident_alert;
        }
        key = {
            meta.accident_meta.has_accident_ahead: exact;
            meta.accident_egress_meta.recirculate: exact;
        }
    }
    @name(".send_accnt_bal") table send_accnt_bal {
        actions = {
            accnt_bal_e2e;
            make_accnt_bal;
        }
        key = {
            meta.accnt_bal_egress_meta.recirculate: exact;
        }
    }
    @name(".send_frame") table send_frame {
        actions = {
            rewrite_mac;
            _drop;
        }
        key = {
            standard_metadata.egress_port: exact;
        }
        size = 256;
    }
    @name(".send_toll_notification") table send_toll_notification {
        actions = {
            toll_notification_e2e;
            make_toll_notification;
        }
        key = {
            meta.toll_meta.has_toll          : exact;
            meta.toll_egress_meta.recirculate: exact;
        }
    }
    @name(".travel_estimate_history") table travel_estimate_history {
        actions = {
            update_travel_estimate;
        }
        key = {
            hdr.travel_estimate_req.dow : exact;
            hdr.travel_estimate_req.tod : exact;
            hdr.travel_estimate_req.xway: exact;
            meta.te_md.dir              : exact;
            meta.te_md.seg_cur          : exact;
        }
        size = 1024;
    }
    @name(".travel_estimate_init") table travel_estimate_init {
        actions = {
            do_travel_estimate_init;
        }
        size = 1;
        default_action = do_travel_estimate_init();
    }
    @name(".travel_estimate_init_rev") table travel_estimate_init_rev {
        actions = {
            do_travel_estimate_init_rev;
        }
        size = 1;
        default_action = do_travel_estimate_init_rev();
    }
    @name(".travel_estimate_recirc") table travel_estimate_recirc {
        actions = {
            travel_estimate_e2e;
        }
        size = 1;
    }
    @name(".travel_estimate_send") table travel_estimate_send {
        actions = {
            do_travel_estimate_send;
        }
        size = 1;
        default_action = do_travel_estimate_send();
    }
    apply {
        if (hdr.ipv4.isValid()) {
            if (hdr.pos_report.isValid()) {
                send_accident_alert.apply();
                send_toll_notification.apply();
            }
            else {
                if (hdr.accnt_bal_req.isValid()) {
                    send_accnt_bal.apply();
                }
                else {
                    if (hdr.expenditure_req.isValid()) {
                        daily_expenditure.apply();
                    }
                    else {
                        if (hdr.travel_estimate_req.isValid()) {
                            if (meta.te_md.recirculated == 1w0) {
                                if (hdr.travel_estimate_req.seg_init < hdr.travel_estimate_req.seg_end) {
                                    travel_estimate_init.apply();
                                }
                                else {
                                    travel_estimate_init_rev.apply();
                                }
                            }
                            travel_estimate_history.apply();
                            if (meta.te_md.seg_cur == meta.te_md.seg_end) {
                                travel_estimate_send.apply();
                            }
                            else {
                                travel_estimate_recirc.apply();
                            }
                        }
                    }
                }
            }
            send_frame.apply();
        }
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name(".seg_ewma_spd_reg") register<bit<16>>(32w400) seg_ewma_spd_reg;
    @name(".seg_vol_reg") register<bit<8>>(32w400) seg_vol_reg;
    @name(".stopped_cnt_reg") register<bit<8>>(32w1200) stopped_cnt_reg;
    @name(".v_accnt_bal_reg") register<bit<32>>(32w512) v_accnt_bal_reg;
    @name(".v_dir_reg") register<bit<1>>(32w512) v_dir_reg;
    @name(".v_lane_reg") register<bit<3>>(32w512) v_lane_reg;
    @name(".v_nomove_cnt_reg") register<bit<3>>(32w512) v_nomove_cnt_reg;
    @name(".v_seg_reg") register<bit<8>>(32w512) v_seg_reg;
    @name(".v_spd_reg") register<bit<8>>(32w512) v_spd_reg;
    @name(".v_valid_reg") register<bit<1>>(32w512) v_valid_reg;
    @name(".v_xway_reg") register<bit<8>>(32w512) v_xway_reg;
    @name(".set_accident_meta") action set_accident_meta(bit<8> ofst) {
        meta.accident_meta.accident_seg = hdr.pos_report.seg + ofst;
        meta.accident_meta.has_accident_ahead = 1w1;
    }
    @name(".issue_toll") action issue_toll(bit<16> base_toll) {
        meta.toll_meta.has_toll = 1w1;
        meta.toll_meta.toll = base_toll * ((bit<16>)meta.seg_meta.vol - 16w50) * ((bit<16>)meta.seg_meta.vol - 16w50);
        v_accnt_bal_reg.read(meta.toll_meta.bal, (bit<32>)hdr.pos_report.vid);
        meta.toll_meta.bal = meta.toll_meta.bal + (bit<32>)meta.toll_meta.toll;
        v_accnt_bal_reg.write((bit<32>)hdr.pos_report.vid, (bit<32>)meta.toll_meta.bal);
    }
    @name(".do_dec_prev_stopped") action do_dec_prev_stopped() {
        stopped_cnt_reg.read(meta.accident_meta.prev_stp_cnt, (bit<32>)((bit<16>)meta.v_state.prev_xway * 16w600 + (bit<16>)(meta.v_state.prev_seg * 8w2) * 16w3 + (bit<16>)meta.v_state.prev_dir * 16w3 + (bit<16>)meta.v_state.prev_lane));
        stopped_cnt_reg.write((bit<32>)((bit<16>)meta.v_state.prev_xway * 16w600 + (bit<16>)(meta.v_state.prev_seg * 8w2) * 16w3 + (bit<16>)meta.v_state.prev_dir * 16w3 + (bit<16>)meta.v_state.prev_lane), (bit<8>)(meta.accident_meta.prev_stp_cnt - 8w1));
    }
    @name(".set_dmac") action set_dmac(bit<48> dmac) {
        hdr.ethernet.dstAddr = dmac;
    }
    @name("._drop") action _drop() {
        mark_to_drop();
    }
    @name(".do_inc_stopped") action do_inc_stopped() {
        stopped_cnt_reg.read(meta.accident_meta.cur_stp_cnt, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + (bit<16>)hdr.pos_report.lane));
        stopped_cnt_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + (bit<16>)hdr.pos_report.lane), (bit<8>)(meta.accident_meta.cur_stp_cnt + 8w1));
    }
    @name(".set_nhop") action set_nhop(bit<32> nhop_ipv4, bit<9> port) {
        hdr.ipv4.dstAddr = nhop_ipv4;
        standard_metadata.egress_spec = port;
    }
    @name(".do_load_accnt_bal") action do_load_accnt_bal() {
        v_accnt_bal_reg.read(meta.toll_meta.bal, (bit<32>)hdr.accnt_bal_req.vid);
    }
    @name(".do_load_stopped_ahead") action do_load_stopped_ahead() {
        stopped_cnt_reg.read(meta.stopped_ahead.seg0l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1));
        stopped_cnt_reg.read(meta.stopped_ahead.seg0l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2));
        stopped_cnt_reg.read(meta.stopped_ahead.seg0l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)(hdr.pos_report.seg * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3));
        stopped_cnt_reg.read(meta.stopped_ahead.seg1l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w1) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1));
        stopped_cnt_reg.read(meta.stopped_ahead.seg1l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w1) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2));
        stopped_cnt_reg.read(meta.stopped_ahead.seg1l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w1) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3));
        stopped_cnt_reg.read(meta.stopped_ahead.seg2l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w2) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1));
        stopped_cnt_reg.read(meta.stopped_ahead.seg2l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w2) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2));
        stopped_cnt_reg.read(meta.stopped_ahead.seg2l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w2) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3));
        stopped_cnt_reg.read(meta.stopped_ahead.seg3l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w3) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1));
        stopped_cnt_reg.read(meta.stopped_ahead.seg3l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w3) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2));
        stopped_cnt_reg.read(meta.stopped_ahead.seg3l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w3) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3));
        stopped_cnt_reg.read(meta.stopped_ahead.seg4l1, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w4) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w1));
        stopped_cnt_reg.read(meta.stopped_ahead.seg4l2, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w4) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w2));
        stopped_cnt_reg.read(meta.stopped_ahead.seg4l3, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w600 + (bit<16>)((hdr.pos_report.seg + 8w4) * 8w2) * 16w3 + (bit<16>)hdr.pos_report.dir * 16w3 + 16w3));
        meta.stopped_ahead.seg0_ord = meta.stopped_ahead.seg0l1 | meta.stopped_ahead.seg0l2 | meta.stopped_ahead.seg0l3;
        meta.stopped_ahead.seg1_ord = meta.stopped_ahead.seg1l1 | meta.stopped_ahead.seg1l2 | meta.stopped_ahead.seg1l3;
        meta.stopped_ahead.seg2_ord = meta.stopped_ahead.seg2l1 | meta.stopped_ahead.seg2l2 | meta.stopped_ahead.seg2l3;
        meta.stopped_ahead.seg3_ord = meta.stopped_ahead.seg3l1 | meta.stopped_ahead.seg3l2 | meta.stopped_ahead.seg3l3;
        meta.stopped_ahead.seg4_ord = meta.stopped_ahead.seg4l1 | meta.stopped_ahead.seg4l2 | meta.stopped_ahead.seg4l3;
    }
    @name(".do_loc_changed") action do_loc_changed() {
        v_nomove_cnt_reg.read(meta.v_state.prev_nomove_cnt, (bit<32>)hdr.pos_report.vid);
        v_nomove_cnt_reg.write((bit<32>)hdr.pos_report.vid, (bit<3>)3w0);
    }
    @name(".do_loc_not_changed") action do_loc_not_changed() {
        v_nomove_cnt_reg.read(meta.v_state.prev_nomove_cnt, (bit<32>)hdr.pos_report.vid);
        meta.v_state.nomove_cnt = meta.v_state.prev_nomove_cnt + 3w1 - ((meta.v_state.prev_nomove_cnt + 3w1 & 3w4) >> 3w2);
        v_nomove_cnt_reg.write((bit<32>)hdr.pos_report.vid, (bit<3>)meta.v_state.nomove_cnt);
    }
    @name(".set_spd") action set_spd() {
        meta.seg_meta.ewma_spd = (bit<16>)hdr.pos_report.spd;
        seg_ewma_spd_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir), (bit<16>)meta.seg_meta.ewma_spd);
    }
    @name(".calc_ewma_spd") action calc_ewma_spd() {
        seg_ewma_spd_reg.read(meta.seg_meta.ewma_spd, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir));
        meta.seg_meta.ewma_spd = (bit<16>)((bit<32>)meta.seg_meta.ewma_spd * 32w96 + (bit<32>)(((bit<16>)hdr.pos_report.spd * 16w32) >> 16w7));
        seg_ewma_spd_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir), (bit<16>)meta.seg_meta.ewma_spd);
    }
    @name(".set_new_seg") action set_new_seg() {
        meta.v_state.new_seg = 1w1;
    }
    @name(".do_update_pos_state") action do_update_pos_state() {
        v_valid_reg.read(meta.v_state.new, (bit<32>)hdr.pos_report.vid);
        meta.v_state.new = ~meta.v_state.new;
        v_spd_reg.read(meta.v_state.prev_spd, (bit<32>)hdr.pos_report.vid);
        v_xway_reg.read(meta.v_state.prev_xway, (bit<32>)hdr.pos_report.vid);
        v_lane_reg.read(meta.v_state.prev_lane, (bit<32>)hdr.pos_report.vid);
        v_seg_reg.read(meta.v_state.prev_seg, (bit<32>)hdr.pos_report.vid);
        v_dir_reg.read(meta.v_state.prev_dir, (bit<32>)hdr.pos_report.vid);
        v_valid_reg.write((bit<32>)hdr.pos_report.vid, (bit<1>)1w1);
        v_spd_reg.write((bit<32>)hdr.pos_report.vid, (bit<8>)hdr.pos_report.spd);
        v_xway_reg.write((bit<32>)hdr.pos_report.vid, (bit<8>)hdr.pos_report.xway);
        v_lane_reg.write((bit<32>)hdr.pos_report.vid, (bit<3>)hdr.pos_report.lane);
        v_seg_reg.write((bit<32>)hdr.pos_report.vid, (bit<8>)hdr.pos_report.seg);
        v_dir_reg.write((bit<32>)hdr.pos_report.vid, (bit<1>)hdr.pos_report.dir);
    }
    @name(".load_vol") action load_vol() {
        seg_vol_reg.read(meta.seg_meta.vol, (bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir));
    }
    @name(".load_and_inc_vol") action load_and_inc_vol() {
        load_vol();
        meta.seg_meta.vol = meta.seg_meta.vol + 8w1;
        seg_vol_reg.write((bit<32>)((bit<16>)hdr.pos_report.xway * 16w200 + (bit<16>)(hdr.pos_report.seg * 8w2) + (bit<16>)hdr.pos_report.dir), (bit<8>)meta.seg_meta.vol);
    }
    @name(".load_and_inc_and_dec_vol") action load_and_inc_and_dec_vol() {
        load_and_inc_vol();
        seg_vol_reg.read(meta.seg_meta.prev_vol, (bit<32>)((bit<16>)meta.v_state.prev_xway * 16w200 + (bit<16>)(meta.v_state.prev_seg * 8w2) + (bit<16>)meta.v_state.prev_dir));
        meta.seg_meta.prev_vol = meta.seg_meta.prev_vol - 8w1;
        seg_vol_reg.write((bit<32>)((bit<16>)meta.v_state.prev_xway * 16w200 + (bit<16>)(meta.v_state.prev_seg * 8w2) + (bit<16>)meta.v_state.prev_dir), (bit<8>)meta.seg_meta.prev_vol);
    }
    @name(".check_accidents") table check_accidents {
        actions = {
            set_accident_meta;
        }
        key = {
            meta.stopped_ahead.seg0_ord: ternary;
            meta.stopped_ahead.seg1_ord: ternary;
            meta.stopped_ahead.seg2_ord: ternary;
            meta.stopped_ahead.seg3_ord: ternary;
            meta.stopped_ahead.seg4_ord: ternary;
        }
        size = 8;
    }
    @name(".check_toll") table check_toll {
        actions = {
            issue_toll;
        }
        key = {
            meta.v_state.new_seg                 : exact;
            meta.seg_meta.ewma_spd               : ternary;
            meta.seg_meta.vol                    : ternary;
            meta.accident_meta.has_accident_ahead: ternary;
        }
        size = 1;
    }
    @name(".dec_prev_stopped") table dec_prev_stopped {
        actions = {
            do_dec_prev_stopped;
        }
    }
    @name(".forward") table forward {
        actions = {
            set_dmac;
            _drop;
        }
        key = {
            hdr.ipv4.dstAddr: exact;
        }
        size = 512;
    }
    @name(".inc_stopped") table inc_stopped {
        actions = {
            do_inc_stopped;
        }
    }
    @name(".ipv4_lpm") table ipv4_lpm {
        actions = {
            set_nhop;
            _drop;
        }
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        size = 1024;
    }
    @name(".load_accnt_bal") table load_accnt_bal {
        actions = {
            do_load_accnt_bal;
        }
    }
    @name(".load_stopped_ahead") table load_stopped_ahead {
        actions = {
            do_load_stopped_ahead;
        }
    }
    @name(".loc_changed") table loc_changed {
        actions = {
            do_loc_changed;
        }
    }
    @name(".loc_not_changed") table loc_not_changed {
        actions = {
            do_loc_not_changed;
        }
    }
    @name(".update_ewma_spd") table update_ewma_spd {
        actions = {
            set_spd;
            calc_ewma_spd;
        }
        key = {
            meta.seg_meta.vol: exact;
        }
        size = 2;
        default_action = calc_ewma_spd();
    }
    @name(".update_new_seg") table update_new_seg {
        actions = {
            set_new_seg;
        }
    }
    @name(".update_pos_state") table update_pos_state {
        actions = {
            do_update_pos_state;
        }
    }
    @name(".update_vol_state") table update_vol_state {
        actions = {
            load_vol;
            load_and_inc_vol;
            load_and_inc_and_dec_vol;
        }
        key = {
            meta.v_state.new    : exact;
            meta.v_state.new_seg: exact;
        }
        size = 4;
    }
    apply {
        if (hdr.ipv4.isValid()) {
            if (hdr.pos_report.isValid()) {
                update_pos_state.apply();
                if (meta.v_state.new == 1w1 || meta.v_state.prev_seg != hdr.pos_report.seg) {
                    update_new_seg.apply();
                }
                update_vol_state.apply();
                update_ewma_spd.apply();
                if (hdr.pos_report.xway == meta.v_state.prev_xway && hdr.pos_report.seg == meta.v_state.prev_seg && hdr.pos_report.dir == (bit<8>)meta.v_state.prev_dir && hdr.pos_report.lane == (bit<8>)meta.v_state.prev_lane) {
                    loc_not_changed.apply();
                }
                else {
                    loc_changed.apply();
                }
                if (meta.v_state.prev_nomove_cnt == 3w3 && meta.v_state.nomove_cnt < 3w3) {
                    dec_prev_stopped.apply();
                }
                if (meta.v_state.prev_nomove_cnt < 3w3 && meta.v_state.nomove_cnt == 3w3) {
                    inc_stopped.apply();
                }
                load_stopped_ahead.apply();
                check_accidents.apply();
                check_toll.apply();
            }
            else {
                if (hdr.accnt_bal_req.isValid()) {
                    load_accnt_bal.apply();
                }
            }
            ipv4_lpm.apply();
            forward.apply();
        }
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
        packet.emit(hdr.udp);
        packet.emit(hdr.lr_msg_type);
        packet.emit(hdr.travel_estimate);
        packet.emit(hdr.travel_estimate_req);
        packet.emit(hdr.expenditure_report);
        packet.emit(hdr.expenditure_req);
        packet.emit(hdr.accnt_bal);
        packet.emit(hdr.accident_alert);
        packet.emit(hdr.toll_notification);
        packet.emit(hdr.accnt_bal_req);
        packet.emit(hdr.pos_report);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
        verify_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
        update_checksum(true, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
    }
}

V1Switch(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;

