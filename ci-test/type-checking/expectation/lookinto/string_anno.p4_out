/petr4/ci-test/type-checking/testdata/p4_16_samples/string_anno.p4
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

/* P4TEST_IGNORE_STDERR */

@name("original") const bit b = 1;
@name("string \" with \" quotes") const bit c = 1;
@name("string with
newline") const bit d = 1;
@name("string with quoted \
newline") const bit e = 1;
@name("8-bit string ⟶") const bit f = 1;
************************\n******** petr4 type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/string_anno.p4:21:7: warning: missing terminating " character
   21 | @name("string with
      |       ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/string_anno.p4:22:8: warning: missing terminating " character
   22 | newline") const bit d = 1;
      |        ^
@name("original")
const bit<1> b = 1;
@name("string " with " quotes")
const bit<1> c = 1;
@name("string with
newline")
const bit<1> d = 1;
@name("string with quoted newline")
const bit<1> e = 1;
@name("8-bit string ⟶")
const bit<1> f = 1;

************************\n******** p4c type checking result: ********\n************************\n
[--Wwarn=missing] warning: Program does not contain a `main' module
