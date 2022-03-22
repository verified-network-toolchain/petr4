/petr4/ci-test/type-checking/testdata/p4_16_samples/fabric_20190420/include/control/acl.p4
\n
/*
 * Copyright 2017-present Open Networking Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <core.p4>
#include <v1model.p4>

#include "../define.p4"
#include "../header.p4"

control Acl (inout parsed_headers_t hdr,
             inout fabric_metadata_t fabric_metadata,
             inout standard_metadata_t standard_metadata) {

    /*
     * ACL Table.
     */
    direct_counter(CounterType.packets_and_bytes) acl_counter;

    action set_next_id_acl(next_id_t next_id) {
        fabric_metadata.next_id = next_id;
        acl_counter.count();
    }

    // Send immendiatelly to CPU - skip the rest of ingress.
    action punt_to_cpu() {
        standard_metadata.egress_spec = CPU_PORT;
        fabric_metadata.skip_next = _TRUE;
        acl_counter.count();
    }

    action clone_to_cpu() {
        // FIXME: works only if pkt will be replicated via PRE multicast group.
        fabric_metadata.clone_to_cpu = _TRUE;
        acl_counter.count();
    }

    action drop() {
        mark_to_drop(standard_metadata);
        fabric_metadata.skip_next = _TRUE;
        acl_counter.count();
    }

    action nop_acl() {
        acl_counter.count();
    }

    table acl {
        key = {
            standard_metadata.ingress_port: ternary @name("ig_port"); // 9
            fabric_metadata.ip_proto: ternary @name("ip_proto"); // 8
            fabric_metadata.l4_sport: ternary @name("l4_sport"); // 16
            fabric_metadata.l4_dport: ternary @name("l4_dport"); // 16
            hdr.ethernet.dst_addr: ternary @name("eth_src"); // 48
            hdr.ethernet.src_addr: ternary @name("eth_dst"); // 48
            hdr.vlan_tag.vlan_id: ternary @name("vlan_id"); // 12
            fabric_metadata.eth_type: ternary @name("eth_type"); //16
            hdr.ipv4.src_addr: ternary @name("ipv4_src"); // 32
            hdr.ipv4.dst_addr: ternary @name("ipv4_dst"); // 32
            hdr.icmp.icmp_type: ternary @name("icmp_type"); // 8
            hdr.icmp.icmp_code: ternary @name("icmp_code"); // 8
        }

        actions = {
            set_next_id_acl;
            punt_to_cpu;
            clone_to_cpu;
            drop;
            nop_acl;
        }

        const default_action = nop_acl();
        size = ACL_TABLE_SIZE;
        counters = acl_counter;
    }

    apply {
        acl.apply();
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  Petr4.Prog.Env.UnboundName("CPU_PORT")

Raised at Petr4__Prog.Env.raise_unbound in file "lib/prog.ml", line 1455, characters 4-32
Called from Petr4__Checker.type_expression in file "lib/checker.ml", line 849, characters 22-54
Called from Petr4__Checker.cast_expression in file "lib/checker.ml", line 941, characters 21-60
Called from Petr4__Checker.type_assignment in file "lib/checker.ml", line 2708, characters 20-72
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2651, characters 7-38
Called from Petr4__Checker.type_statements.fold in file "lib/checker.ml", line 2782, characters 26-58
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Petr4__Checker.type_block in file "lib/checker.ml", line 2794, characters 27-73
Called from Petr4__Checker.type_function in file "lib/checker.ml", line 3148, characters 27-55
Called from Petr4__Checker.type_action in file "lib/checker.ml", line 3282, characters 4-83
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
/petr4/ci-test/type-checking/testdata/p4_16_samples/fabric_20190420/include/control/acl.p4(39): [--Werror=not-found] error: CPU_PORT: declaration not found
        standard_metadata.egress_spec = CPU_PORT;
                                        ^^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/fabric_20190420/include/control/acl.p4(85): [--Werror=not-found] error: ACL_TABLE_SIZE: declaration not found
        size = ACL_TABLE_SIZE;
               ^^^^^^^^^^^^^^
