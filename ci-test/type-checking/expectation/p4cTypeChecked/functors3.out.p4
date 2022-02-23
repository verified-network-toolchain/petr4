/petr4/ci-test/type-checking/testdata/p4_16_samples/functors3.p4
\n
/*
Copyright 2013-present Barefoot Networks, Inc.

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

parser p1(out bit z1)(bit b1) {
    state start {
        z1 = b1;
        transition accept;
    }
}

parser p(out bit z)(bit b, bit c) {
   p1(b) p1i;

   state start {
        p1i.apply(z);
        z = z & b & c;
        transition accept;
   }
}

const bit bv = 1w0;

parser simple(out bit z);
package m(simple n);

m(p(bv, 1w1)) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
