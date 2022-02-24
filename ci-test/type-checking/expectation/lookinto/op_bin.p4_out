/petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4
\n
/*
Copyright 2021-present MNK Labs & Consulting, LLC.

https://mnkcg.com

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

#include <ebpf_model.p4>

typedef bit<48> EthernetAddress;

// standard Ethernet header
header Ethernet_h
{
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16> etherType;
}

header IPv6_h {
    bit<32>     ip_version_traffic_class_and_flow_label;
    bit<16>     payload_length;
    bit<8>      protocol;
    bit<8>      hop_limit;
    bit<128>    src_address;
    bit<128>    dst_address;
}

struct Headers_t
{
    Ethernet_h ethernet;
    IPv6_h     ipv6;
}

parser prs(packet_in p, out Headers_t headers) {
    state start {
        p.extract(headers.ethernet);
        transition select(headers.ethernet.etherType) {
            0x86DD   : ipv6;
            default : reject;
        }
    }

    state ipv6 {
        p.extract(headers.ipv6);
        transition accept;
    }

}

control pipe(inout Headers_t headers, out bool xout) {
    // UBPF does not support const entries, so using hard-coded label below.
    action set_flowlabel(bit<20> label) {
     	headers.ipv6.ip_version_traffic_class_and_flow_label[31:12] = label;
    }

    table filter_tbl {
        key = {
            headers.ipv6.src_address : exact;
        }
        actions = {
            set_flowlabel;
        }
	const entries = {
	    {(8w0x20++8w0x02++8w0x04++8w0x20++8w0x03++8w0x80++8w0xDE++8w0xAD++8w0xBE++8w0xEF++8w0xF0++8w0x0D++8w0x0D++8w0x09++8w0++8w0x01)} : set_flowlabel(52);
	}
	implementation = hash_table(8);
    }

    apply {
        xout = true;
        filter_tbl.apply();

        // If-statement below tests if appropriate parenthesis are
        // added because, if not, gcc compling fails with emitted C code.
        if (headers.ipv6.isValid() && ((headers.ethernet.etherType == 0x86dd)
	    || (headers.ipv6.hop_limit == 255)))
            headers.ipv6.protocol = 17;
        // If-statement below tests if duplicate parenthesis
        // are not added in emitted C code causing gcc compiling failure.
        if (headers.ethernet.etherType == 0x0800)
            headers.ipv6.protocol = 10;
    }
}

ebpfFilter(prs(), pipe()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("cannot cast"
   (expr
    ((I
      (filename
       /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
      (line_start 76) (line_end ()) (col_start 5) (col_end 132))
     ((expr
       (List
        (values
         (((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
            (line_start 76) (line_end ()) (col_start 7) (col_end 130))
           ((expr
             (BinaryOp
              (op
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                 (line_start 76) (line_end ()) (col_start 122) (col_end 124))
                PlusPlus))
              (args
               (((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                  (line_start 76) (line_end ()) (col_start 7) (col_end 122))
                 ((expr
                   (BinaryOp
                    (op
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                       (line_start 76) (line_end ()) (col_start 117)
                       (col_end 119))
                      PlusPlus))
                    (args
                     (((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                        (line_start 76) (line_end ()) (col_start 7)
                        (col_end 117))
                       ((expr
                         (BinaryOp
                          (op
                           ((I
                             (filename
                              /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                             (line_start 76) (line_end ()) (col_start 109)
                             (col_end 111))
                            PlusPlus))
                          (args
                           (((I
                              (filename
                               /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                              (line_start 76) (line_end ()) (col_start 7)
                              (col_end 109))
                             ((expr
                               (BinaryOp
                                (op
                                 ((I
                                   (filename
                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                   (line_start 76) (line_end ())
                                   (col_start 101) (col_end 103))
                                  PlusPlus))
                                (args
                                 (((I
                                    (filename
                                     /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                    (line_start 76) (line_end ())
                                    (col_start 7) (col_end 101))
                                   ((expr
                                     (BinaryOp
                                      (op
                                       ((I
                                         (filename
                                          /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                         (line_start 76) (line_end ())
                                         (col_start 93) (col_end 95))
                                        PlusPlus))
                                      (args
                                       (((I
                                          (filename
                                           /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                          (line_start 76) (line_end ())
                                          (col_start 7) (col_end 93))
                                         ((expr
                                           (BinaryOp
                                            (op
                                             ((I
                                               (filename
                                                /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                               (line_start 76) (line_end ())
                                               (col_start 85) (col_end 87))
                                              PlusPlus))
                                            (args
                                             (((I
                                                (filename
                                                 /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                (line_start 76) (line_end ())
                                                (col_start 7) (col_end 85))
                                               ((expr
                                                 (BinaryOp
                                                  (op
                                                   ((I
                                                     (filename
                                                      /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                     (line_start 76)
                                                     (line_end ())
                                                     (col_start 77)
                                                     (col_end 79))
                                                    PlusPlus))
                                                  (args
                                                   (((I
                                                      (filename
                                                       /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                      (line_start 76)
                                                      (line_end ())
                                                      (col_start 7)
                                                      (col_end 77))
                                                     ((expr
                                                       (BinaryOp
                                                        (op
                                                         ((I
                                                           (filename
                                                            /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                           (line_start 76)
                                                           (line_end ())
                                                           (col_start 69)
                                                           (col_end 71))
                                                          PlusPlus))
                                                        (args
                                                         (((I
                                                            (filename
                                                             /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                            (line_start 76)
                                                            (line_end ())
                                                            (col_start 7)
                                                            (col_end 69))
                                                           ((expr
                                                             (BinaryOp
                                                              (op
                                                               ((I
                                                                 (filename
                                                                  /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                 (line_start
                                                                  76)
                                                                 (line_end
                                                                  ())
                                                                 (col_start
                                                                  61)
                                                                 (col_end 63))
                                                                PlusPlus))
                                                              (args
                                                               (((I
                                                                  (filename
                                                                   /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                  (line_start
                                                                   76)
                                                                  (line_end
                                                                   ())
                                                                  (col_start
                                                                   7)
                                                                  (col_end
                                                                   61))
                                                                 ((expr
                                                                   (BinaryOp
                                                                    (op
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    53)
                                                                    (col_end
                                                                    55))
                                                                    PlusPlus))
                                                                    (args
                                                                    (((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    53))
                                                                    ((expr
                                                                    (BinaryOp
                                                                    (op
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    45)
                                                                    (col_end
                                                                    47))
                                                                    PlusPlus))
                                                                    (args
                                                                    (((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    45))
                                                                    ((expr
                                                                    (BinaryOp
                                                                    (op
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    37)
                                                                    (col_end
                                                                    39))
                                                                    PlusPlus))
                                                                    (args
                                                                    (((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    37))
                                                                    ((expr
                                                                    (BinaryOp
                                                                    (op
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    29)
                                                                    (col_end
                                                                    31))
                                                                    PlusPlus))
                                                                    (args
                                                                    (((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    29))
                                                                    ((expr
                                                                    (BinaryOp
                                                                    (op
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    21)
                                                                    (col_end
                                                                    23))
                                                                    PlusPlus))
                                                                    (args
                                                                    (((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    21))
                                                                    ((expr
                                                                    (BinaryOp
                                                                    (op
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    13)
                                                                    (col_end
                                                                    15))
                                                                    PlusPlus))
                                                                    (args
                                                                    (((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    13))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    7)
                                                                    (col_end
                                                                    13))
                                                                    ((value
                                                                    32)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    15)
                                                                    (col_end
                                                                    21))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    15)
                                                                    (col_end
                                                                    21))
                                                                    ((value
                                                                    2)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    16))))
                                                                    (dir
                                                                    Directionless)))
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    23)
                                                                    (col_end
                                                                    29))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    23)
                                                                    (col_end
                                                                    29))
                                                                    ((value
                                                                    4)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    24))))
                                                                    (dir
                                                                    Directionless)))
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    31)
                                                                    (col_end
                                                                    37))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    31)
                                                                    (col_end
                                                                    37))
                                                                    ((value
                                                                    32)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    32))))
                                                                    (dir
                                                                    Directionless)))
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    39)
                                                                    (col_end
                                                                    45))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    39)
                                                                    (col_end
                                                                    45))
                                                                    ((value
                                                                    3)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    40))))
                                                                    (dir
                                                                    Directionless)))
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    47)
                                                                    (col_end
                                                                    53))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    47)
                                                                    (col_end
                                                                    53))
                                                                    ((value
                                                                    128)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    48))))
                                                                    (dir
                                                                    Directionless)))
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    55)
                                                                    (col_end
                                                                    61))
                                                                    ((expr
                                                                    (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    55)
                                                                    (col_end
                                                                    61))
                                                                    ((value
                                                                    222)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                    (typ
                                                                    (Bit
                                                                    ((width
                                                                    8))))
                                                                    (dir
                                                                    Directionless)))))))
                                                                  (typ
                                                                   (Bit
                                                                    ((width
                                                                    56))))
                                                                  (dir
                                                                   Directionless)))
                                                                ((I
                                                                  (filename
                                                                   /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                  (line_start
                                                                   76)
                                                                  (line_end
                                                                   ())
                                                                  (col_start
                                                                   63)
                                                                  (col_end
                                                                   69))
                                                                 ((expr
                                                                   (Int
                                                                    ((I
                                                                    (filename
                                                                    /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                    (line_start
                                                                    76)
                                                                    (line_end
                                                                    ())
                                                                    (col_start
                                                                    63)
                                                                    (col_end
                                                                    69))
                                                                    ((value
                                                                    173)
                                                                    (width_signed
                                                                    ((8
                                                                    false)))))))
                                                                  (typ
                                                                   (Bit
                                                                    ((width
                                                                    8))))
                                                                  (dir
                                                                   Directionless)))))))
                                                            (typ
                                                             (Bit
                                                              ((width 64))))
                                                            (dir
                                                             Directionless)))
                                                          ((I
                                                            (filename
                                                             /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                            (line_start 76)
                                                            (line_end ())
                                                            (col_start 71)
                                                            (col_end 77))
                                                           ((expr
                                                             (Int
                                                              ((I
                                                                (filename
                                                                 /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                                (line_start
                                                                 76)
                                                                (line_end ())
                                                                (col_start
                                                                 71)
                                                                (col_end 77))
                                                               ((value 190)
                                                                (width_signed
                                                                 ((8 false)))))))
                                                            (typ
                                                             (Bit
                                                              ((width 8))))
                                                            (dir
                                                             Directionless)))))))
                                                      (typ
                                                       (Bit ((width 72))))
                                                      (dir Directionless)))
                                                    ((I
                                                      (filename
                                                       /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                      (line_start 76)
                                                      (line_end ())
                                                      (col_start 79)
                                                      (col_end 85))
                                                     ((expr
                                                       (Int
                                                        ((I
                                                          (filename
                                                           /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                          (line_start 76)
                                                          (line_end ())
                                                          (col_start 79)
                                                          (col_end 85))
                                                         ((value 239)
                                                          (width_signed
                                                           ((8 false)))))))
                                                      (typ (Bit ((width 8))))
                                                      (dir Directionless)))))))
                                                (typ (Bit ((width 80))))
                                                (dir Directionless)))
                                              ((I
                                                (filename
                                                 /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                (line_start 76) (line_end ())
                                                (col_start 87) (col_end 93))
                                               ((expr
                                                 (Int
                                                  ((I
                                                    (filename
                                                     /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                                    (line_start 76)
                                                    (line_end ())
                                                    (col_start 87)
                                                    (col_end 93))
                                                   ((value 240)
                                                    (width_signed
                                                     ((8 false)))))))
                                                (typ (Bit ((width 8))))
                                                (dir Directionless)))))))
                                          (typ (Bit ((width 88))))
                                          (dir Directionless)))
                                        ((I
                                          (filename
                                           /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                          (line_start 76) (line_end ())
                                          (col_start 95) (col_end 101))
                                         ((expr
                                           (Int
                                            ((I
                                              (filename
                                               /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                              (line_start 76) (line_end ())
                                              (col_start 95) (col_end 101))
                                             ((value 13)
                                              (width_signed ((8 false)))))))
                                          (typ (Bit ((width 8))))
                                          (dir Directionless)))))))
                                    (typ (Bit ((width 96))))
                                    (dir Directionless)))
                                  ((I
                                    (filename
                                     /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                    (line_start 76) (line_end ())
                                    (col_start 103) (col_end 109))
                                   ((expr
                                     (Int
                                      ((I
                                        (filename
                                         /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                        (line_start 76) (line_end ())
                                        (col_start 103) (col_end 109))
                                       ((value 13)
                                        (width_signed ((8 false)))))))
                                    (typ (Bit ((width 8))))
                                    (dir Directionless)))))))
                              (typ (Bit ((width 104)))) (dir Directionless)))
                            ((I
                              (filename
                               /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                              (line_start 76) (line_end ()) (col_start 111)
                              (col_end 117))
                             ((expr
                               (Int
                                ((I
                                  (filename
                                   /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                                  (line_start 76) (line_end ())
                                  (col_start 111) (col_end 117))
                                 ((value 9) (width_signed ((8 false)))))))
                              (typ (Bit ((width 8)))) (dir Directionless)))))))
                        (typ (Bit ((width 112)))) (dir Directionless)))
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                        (line_start 76) (line_end ()) (col_start 119)
                        (col_end 122))
                       ((expr
                         (Int
                          ((I
                            (filename
                             /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                            (line_start 76) (line_end ()) (col_start 119)
                            (col_end 122))
                           ((value 0) (width_signed ((8 false)))))))
                        (typ (Bit ((width 8)))) (dir Directionless)))))))
                  (typ (Bit ((width 120)))) (dir Directionless)))
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                  (line_start 76) (line_end ()) (col_start 124)
                  (col_end 130))
                 ((expr
                   (Int
                    ((I
                      (filename
                       /petr4/ci-test/type-checking/testdata/p4_16_samples/op_bin.p4)
                      (line_start 76) (line_end ()) (col_start 124)
                      (col_end 130))
                     ((value 1) (width_signed ((8 false)))))))
                  (typ (Bit ((width 8)))) (dir Directionless)))))))
            (typ (Bit ((width 128)))) (dir Directionless)))))))
      (typ (List ((types ((Bit ((width 128)))))))) (dir Directionless))))
   (typ (Bit ((width 128)))))

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
