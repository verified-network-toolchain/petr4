/*
Copyright 2017 VMware, Inc.

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
header_type ethernet_t {
    fields {
        dstAddr : 48;
        srcAddr : 48;
        ethertype : 16;
    }
}

header ethernet_t ethernet;

parser start {
    extract(ethernet);
    return ingress;
}

action set_egress_port(port) {
    modify_field(standard_metadata.egress_spec, port);
}

table t1 {
    reads {
         ethernet.dstAddr : lpm;
         ethernet.srcAddr : lpm;
    }
    actions {
         set_egress_port;
    }
}

control ingress {
    apply(t1);
}

control egress {
}