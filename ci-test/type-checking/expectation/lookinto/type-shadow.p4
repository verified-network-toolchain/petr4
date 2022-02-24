/petr4/ci-test/type-checking/testdata/p4_16_samples/type-shadow.p4
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
extern X<D>
{
   void f<D>(in D d); // D shadows D
}
************************\n******** petr4 type checking result: ********\n************************\n
extern X<D> {
  void f<D0>(in D0 d);
}


************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/type-shadow.p4(18): [--Wwarn=shadow] warning: 'D' shadows 'D'
   void f<D>(in D d); // D shadows D
          ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/type-shadow.p4(16)
extern X<D>
         ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/type-shadow.p4(16): [--Wwarn=unused] warning: 'D' is unused
extern X<D>
         ^
[--Wwarn=missing] warning: Program does not contain a `main' module
