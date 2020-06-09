/*
Copyright 2016 VMware, Inc.

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
typedef standard_metadata_t std_meta_t;

header h_t { 
  bit<8> x;
}

struct H { 
  h_t h;
}

struct M { 
}

parser ParserI(packet_in pk, out H hdr, inout M meta, inout std_meta_t std_meta) {
    state start {
        pk.extract(hdr.h);
        transition accept;
    }
}

control VerifyChecksumI(inout H hdr, inout M meta) {
    apply { }
}

control ComputeChecksumI(inout H hdr, inout M meta) {
    apply { }
}

action g(inout bit<8> b) { b = ~b; }

action f(inout bit<8> b) { g(b); }

control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
  action g(inout bit<8> b) { b = 0x99; }
  apply {
    f(hdr.h.x);
  }
}

control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
    apply { }
}

control DeparserI(packet_out b, in H hdr) {
    apply {
        b.emit(hdr.h);
    }
}

V1Switch(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;
