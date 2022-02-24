/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2844-enum.p4
\n

/*
Copyright 2018 Cisco Systems, Inc.

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

#include <core.p4>
#include <v1model.p4>

typedef bit<48>  EthernetAddress;

header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

struct Parsed_packet {
    Ethernet_h    ethernet;
}

struct metadata_t {
    bit<4>  a;
    bit<4>  b;
}

enum bit<32> sizes {
    COUNTER_SIZE = 1024
}

control my_control_type(inout bit<16> x);

control C1(inout bit<16> x)
{
    counter(sizes.COUNTER_SIZE, CounterType.packets) stats;
    apply {
        x = x + 1;
        stats.count((bit<32>) x);
    }
};

control C2(inout bit<16> x)(my_control_type c)
{
    apply {
        x = x << 1;
        c.apply(x);
    }
}

control C3(inout bit<16> x)(my_control_type c) {
    apply {
        x = x << 3;
        c.apply(x);
    }
}

control E(inout bit<16> x) {
    C1() c1;
    C2(c1) c2;
    C3(c1) c3;
    apply {
        c2.apply(x);
        c3.apply(x);
    }
}

parser parserI(packet_in pkt,
               out Parsed_packet hdr,
               inout metadata_t meta,
               inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract(hdr.ethernet);
        transition accept;
    }
}

control cIngress(inout Parsed_packet hdr,
                 inout metadata_t meta,
                 inout standard_metadata_t stdmeta) {
    apply {
        E.apply(hdr.ethernet.etherType);
    }
}

control cEgress(inout Parsed_packet hdr,
                inout metadata_t meta,
                inout standard_metadata_t stdmeta) {
    apply { }
}

control DeparserI(packet_out packet,
                  in Parsed_packet hdr) {
    apply { packet.emit(hdr.ethernet); }
}

control vc(inout Parsed_packet hdr,
           inout metadata_t meta) {
    apply { }
}

control uc(inout Parsed_packet hdr,
           inout metadata_t meta) {
    apply { }
}

V1Switch(parserI(),
    vc(),
    cIngress(),
    cEgress(),
    uc(),
    DeparserI()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  (Failure "cast to bitstring undefined")

Raised at Stdlib.failwith in file "stdlib.ml", line 29, characters 17-33
Called from Petr4__Util.option_map in file "lib/util.ml", line 25, characters 19-24
Called from Petr4__Checker.compile_time_known_expr in file "lib/checker.ml", line 818, characters 8-39
Called from Petr4__Checker.type_constructor_invocation.cast_arg in file "lib/checker.ml", line 2551, characters 10-39
Called from Base__List.rev_filter_map.loop in file "src/list.ml", line 812, characters 13-17
Called from Base__List.filter_map in file "src/list.ml" (inlined), line 819, characters 26-47
Called from Petr4__Checker.type_constructor_invocation in file "lib/checker.ml", line 2560, characters 4-50
Called from Petr4__Checker.type_nameless_instantiation in file "lib/checker.ml", line 2573, characters 32-97
Called from Petr4__Checker.type_instantiation in file "lib/checker.ml", line 2928, characters 23-77
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
