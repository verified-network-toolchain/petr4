/petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4
\n
/*
* Copyright 2019, MNK Consulting
* http://mnkcg.com
*
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <v1model.p4>

typedef bit<48> mac_addr_t;
typedef bit<32>  IPv4Address;

header ethernet_t {
    mac_addr_t dstAddr;
    mac_addr_t srcAddr;
    bit<16>    etherType;
}

// IPv4 header without options
header ipv4_t {
    bit<4>       version;
    bit<4>       ihl;
    bit<8>       diffserv;
    bit<16>      packet_length;
    bit<16>      identification;
    bit<3>       flags;
    bit<13>      fragOffset;
    bit<8>       ttl;
    bit<8>       protocol;
    bit<16>      hdrChecksum;
    IPv4Address  srcAddr;
    IPv4Address  dstAddr;
}

struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
}


struct metadata { }

parser MyParser(packet_in packet, out headers hdr, inout metadata meta,
inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}

control MyIngress(inout headers hdr, inout metadata meta,
inout standard_metadata_t standard_metadata) {
    action drop() { mark_to_drop(standard_metadata); }
    action actTbl(bit<24> id, bit<32> ip) {
    }
    table ingress_tbl {
	key = {
	    hdr.ipv4.dstAddr    : exact;
	}
	actions = {actTbl; drop;}
	const default_action = drop;
	const entries = {
	    {(8w0x20++8w0x02++8w0x04++8w0x20)} : actTbl(24w42, (8w0x20++8w0x02++8w0x42++8w0x00));
	}
    }

    apply {
        if (hdr.ipv4.isValid()) {
	    ingress_tbl.apply();
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
MyComputeChecksum(), MyDeparser()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("cannot cast"
   (expr
    ((I
      (filename
       /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
      (line_start 72) (line_end ()) (col_start 5) (col_end 39))
     ((expr
       (List
        (values
         (((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
            (line_start 72) (line_end ()) (col_start 7) (col_end 37))
           ((expr
             (BinaryOp
              (op
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                 (line_start 72) (line_end ()) (col_start 29) (col_end 31))
                PlusPlus))
              (args
               (((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                  (line_start 72) (line_end ()) (col_start 7) (col_end 29))
                 ((expr
                   (BinaryOp
                    (op
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                       (line_start 72) (line_end ()) (col_start 21)
                       (col_end 23))
                      PlusPlus))
                    (args
                     (((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                        (line_start 72) (line_end ()) (col_start 7)
                        (col_end 21))
                       ((expr
                         (BinaryOp
                          (op
                           ((I
                             (filename
                              /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                             (line_start 72) (line_end ()) (col_start 13)
                             (col_end 15))
                            PlusPlus))
                          (args
                           (((I
                              (filename
                               /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                              (line_start 72) (line_end ()) (col_start 7)
                              (col_end 13))
                             ((expr
                               (Int
                                ((I
                                  (filename
                                   /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                                  (line_start 72) (line_end ()) (col_start 7)
                                  (col_end 13))
                                 ((value 32) (width_signed ((8 false)))))))
                              (typ (Bit ((width 8)))) (dir Directionless)))
                            ((I
                              (filename
                               /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                              (line_start 72) (line_end ()) (col_start 15)
                              (col_end 21))
                             ((expr
                               (Int
                                ((I
                                  (filename
                                   /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                                  (line_start 72) (line_end ())
                                  (col_start 15) (col_end 21))
                                 ((value 2) (width_signed ((8 false)))))))
                              (typ (Bit ((width 8)))) (dir Directionless)))))))
                        (typ (Bit ((width 16)))) (dir Directionless)))
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                        (line_start 72) (line_end ()) (col_start 23)
                        (col_end 29))
                       ((expr
                         (Int
                          ((I
                            (filename
                             /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                            (line_start 72) (line_end ()) (col_start 23)
                            (col_end 29))
                           ((value 4) (width_signed ((8 false)))))))
                        (typ (Bit ((width 8)))) (dir Directionless)))))))
                  (typ (Bit ((width 24)))) (dir Directionless)))
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                  (line_start 72) (line_end ()) (col_start 31) (col_end 37))
                 ((expr
                   (Int
                    ((I
                      (filename
                       /petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4)
                      (line_start 72) (line_end ()) (col_start 31)
                      (col_end 37))
                     ((value 32) (width_signed ((8 false)))))))
                  (typ (Bit ((width 8)))) (dir Directionless)))))))
            (typ (Bit ((width 32)))) (dir Directionless)))))))
      (typ (List ((types ((Bit ((width 32)))))))) (dir Directionless))))
   (typ (Bit ((width 32)))))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.cast_if_needed in file "lib/checker.ml", line 901, characters 37-70
Called from Petr4__Checker.check_match in file "lib/checker.ml", line 2983, characters 22-70
Called from Petr4__Checker.check_match_product in file "lib/checker.ml", line 2992, characters 6-29
Called from Petr4__Checker.type_table_entries.type_table_entry in file "lib/checker.ml", line 3373, characters 24-79
Called from Base__List.count_map in file "src/list.ml", line 387, characters 13-17
Called from Petr4__Checker.type_table' in file "lib/checker.ml", line 3578, characters 31-87
Called from Petr4__Checker.type_table in file "lib/checker.ml", line 3314, characters 2-95
Called from Petr4__Checker.type_declarations.f in file "lib/checker.ml", line 4118, characters 26-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_declarations in file "lib/checker.ml", line 4121, characters 19-58
Called from Petr4__Checker.open_control_scope in file "lib/checker.ml", line 3087, characters 26-73
Called from Petr4__Checker.type_control in file "lib/checker.ml", line 3096, characters 6-69
Called from Petr4__Checker.type_declarations.f in file "lib/checker.ml", line 4118, characters 26-55
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Base__List0.fold in file "src/list0.ml" (inlined), line 21, characters 22-52
Called from Petr4__Checker.type_declarations in file "lib/checker.ml", line 4121, characters 19-58
Called from Petr4__Checker.check_program in file "lib/checker.ml", line 4128, characters 18-78
Called from Petr4__Common.Make_parse.check_file' in file "lib/common.ml", line 95, characters 17-51
Called from Petr4__Common.Make_parse.check_file in file "lib/common.ml", line 108, characters 10-50
Called from Main.check_command.(fun) in file "bin/main.ml", line 70, characters 14-65
Called from Core_kernel__Command.For_unix.run.(fun) in file "src/command.ml", line 2453, characters 8-238
Called from Base__Exn.handle_uncaught_aux in file "src/exn.ml", line 111, characters 6-10
************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4(63): [--Wwarn=unused] warning: 'id' is unused
    action actTbl(bit<24> id, bit<32> ip) {
                          ^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/action-two-params.p4(63): [--Wwarn=unused] warning: 'ip' is unused
    action actTbl(bit<24> id, bit<32> ip) {
                                      ^^
