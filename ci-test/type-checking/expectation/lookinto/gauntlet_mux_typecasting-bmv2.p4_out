/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_mux_typecasting-bmv2.p4
\n
#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

struct Meta {}

parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {

    apply {
        h.eth_hdr.eth_type = (bit<16>)-((h.eth_hdr.src_addr == 1) ? 2 : 3w1);
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  (lib/error.ml.Type
   ((I
     (filename
      /petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_mux_typecasting-bmv2.p4)
     (line_start 29) (line_end ()) (col_start 68) (col_end 75))
    (Type_Difference Integer (Bit ((width 3))))))

Raised at Petr4__Error.raise_type_error in file "lib/error.ml", line 44, characters 2-26
Called from Petr4__Checker.type_ternary in file "lib/checker.ml", line 2133, characters 2-84
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 874, characters 7-40
Called from Petr4__Checker.type_unary_op in file "lib/checker.ml", line 1554, characters 18-45
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 862, characters 7-35
Called from Petr4__Checker.type_cast in file "lib/checker.ml", line 1934, characters 19-47
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 866, characters 7-33
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 923, characters 21-60
Called from Petr4__Checker.type_assignment in file "lib/checker.ml", line 2708, characters 20-72
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2651, characters 7-38
Called from Petr4__Checker.type_statements.fold in file "lib/checker.ml", line 2782, characters 26-58
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Petr4__Checker.type_block in file "lib/checker.ml", line 2794, characters 27-73
Called from Petr4__Checker.type_control in file "lib/checker.ml", line 3098, characters 29-61
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
