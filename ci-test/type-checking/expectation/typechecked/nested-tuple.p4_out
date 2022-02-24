/petr4/ci-test/type-checking/testdata/p4_16_samples/nested-tuple.p4
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

struct T { bit f; }

struct S {
    tuple<T, T> f1;
    T f2;
    bit z;
}

struct tuple_0 {
    T field;
    T field_0;
}

extern void f<T>(in T data);

control c(inout bit r) {
    apply {
        S s = { { {0}, {1} }, {0}, 1 };
        f(s.f1);
        f<tuple_0>({{0},{1}});
        r = s.f2.f & s.z;
    }
}

control simple(inout bit r);
package top(simple e);
top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
struct T {
  bit<1> f;
}
struct S {
  tuple<T, T> f1;
  T f2;
  bit<1> z;
}
struct tuple_0 {
  T field;
  T field_0;
}
extern void f<T0>(in T0 data);
control c(inout bit<1> r) {
  apply
    {
    S s = {{{0}, {1}}, {0}, 1};
    f(s.f1);
    f<tuple_0>({{0}, {1}});
    r = s.f2.f & s.z;
  }
}
control simple (inout bit<1> r);
package top (simple e);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/nested-tuple.p4(30): [--Wwarn=shadow] warning: 'T' shadows 'struct T'
extern void f<T>(in T data);
              ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/nested-tuple.p4(17)
struct T { bit f; }
       ^
