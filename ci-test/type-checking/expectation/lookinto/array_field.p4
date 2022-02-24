/petr4/ci-test/type-checking/testdata/p4_16_samples/array_field.p4
\n
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

header H { bit z; }

extern bit<32> f(inout bit x, in bit b);

control c(out H[2] h);
package top(c _c);

control my(out H[2] s) {
    apply {
        bit<32> a = 0;
        s[a].z = 1;
        s[a+1].z = 0;
        a = f(s[a].z, 0);
        a = f(s[a].z, 1);
    }
}

top(my()) main;
************************\n******** petr4 type checking result: ********\n************************\n
header H {
  bit<1> z;
}
extern bit<32> f(inout bit<1> x, in bit<1> b);
control c (out H[2] h);
package top (c _c);
control my(out H[2] s) {
  apply
    {
    bit<32> a = 0;
    s[a].z = 1;
    s[a+1].z = 0;
    a = f(s[a].z, 0);
    a = f(s[a].z, 1);
  }
}
top(my()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/array_field.p4(27): [--Wwarn=invalid_header] warning: accessing a field of an invalid header s[a]
        s[a].z = 1;
        ^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/array_field.p4(28): [--Wwarn=invalid_header] warning: accessing a field of an invalid header s[+]
        s[a+1].z = 0;
        ^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/array_field.p4(29): [--Wwarn=invalid_header] warning: accessing a field of an invalid header s[a]
        a = f(s[a].z, 0);
              ^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/array_field.p4(30): [--Wwarn=invalid_header] warning: accessing a field of an invalid header s[a]
        a = f(s[a].z, 1);
              ^^^^
