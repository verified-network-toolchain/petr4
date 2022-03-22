/petr4/ci-test/type-checking/testdata/p4_16_samples/pvs-nested-struct.p4
\n
#include <v1model.p4>

header data_h {
  bit<32> da;
  bit<32> db;
}

struct my_packet {
  data_h data;
}

struct my_metadata {
  data_h[2] data;
}

struct inner_value_set_t {
  bit<32> field;
}

struct value_set_t {
  bit<32> field;
  inner_value_set_t inner;
}

parser MyParser(packet_in b, out my_packet p, inout my_metadata m, inout standard_metadata_t s) {

    value_set<value_set_t>(4) pvs;

    state start {
        b.extract(p.data);
        transition select(p.data.da, p.data.da) {
            pvs: accept;
            (0x810, 0x810) : foo;
        }
    }

    state foo {
        transition accept;
    }
}

control MyVerifyChecksum(inout my_packet hdr, inout my_metadata meta) {
  apply { }
}


control MyIngress(inout my_packet p, inout my_metadata meta, inout standard_metadata_t s) {
    action set_data() {
    }
    table t {
        actions = { set_data; }
        key = { meta.data[0].da : exact;}
    }
    apply {
        t.apply();
    }
}

control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
  apply {
  }
}

control MyComputeChecksum(inout my_packet p, inout my_metadata m) {
  apply { }
}

control MyDeparser(packet_out b, in my_packet p) {
  apply { }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("cannot cast"
   (expr
    ((I
      (filename
       /petr4/ci-test/type-checking/testdata/p4_16_samples/pvs-nested-struct.p4)
      (line_start 32) (line_end ()) (col_start 12) (col_end 15))
     ((expr
       (Name
        (BareName
         ((I
           (filename
            /petr4/ci-test/type-checking/testdata/p4_16_samples/pvs-nested-struct.p4)
           (line_start 32) (line_end ()) (col_start 12) (col_end 15))
          pvs))))
      (typ
       (Set
        (TypeName
         (BareName
          ((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/pvs-nested-struct.p4)
            (line_start 27) (line_end ()) (col_start 14) (col_end 25))
           value_set_t)))))
      (dir Directionless))))
   (typ (List ((types ((Bit ((width 32))) (Bit ((width 32)))))))))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.cast_if_needed in file "lib/checker.ml", line 901, characters 37-70
Called from Petr4__Checker.check_match in file "lib/checker.ml", line 2983, characters 22-70
Called from Petr4__Checker.check_match_product in file "lib/checker.ml", line 2994, characters 6-44
Called from Petr4__Checker.type_select_case in file "lib/checker.ml", line 2999, characters 22-73
Called from Base__List.count_map in file "src/list.ml", line 390, characters 13-17
Called from Base__List.map in file "src/list.ml" (inlined), line 418, characters 15-31
Called from Petr4__Checker.type_transition in file "lib/checker.ml", line 3016, characters 8-75
Called from Petr4__Checker.type_parser_state in file "lib/checker.ml", line 3022, characters 25-91
Called from Base__List.count_map in file "src/list.ml", line 390, characters 13-17
Called from Base__List.map in file "src/list.ml" (inlined), line 418, characters 15-31
Called from Petr4__Checker.type_parser in file "lib/checker.ml", line 3059, characters 21-76
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
