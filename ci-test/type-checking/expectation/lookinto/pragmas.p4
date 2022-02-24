/petr4/ci-test/type-checking/testdata/p4_16_samples/pragmas.p4
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

@pragma annotest
const bit b = 1;

@pragma size 100
extern Annotated {
    @pragma name "annotated"
    Annotated();
    @pragma name "exe"
    void execute(bit<8> index);
}

@pragma cycles 10
extern bit<32> log(in bit<32> data);

control c() {
    apply {
        @pragma blockAnnotation
        {
        }
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
@annotest()
const bit<1> b = 1;
@size(100)
extern Annotated {
  @name("annotated")
  Annotated();
  @name("exe")
  void execute(bit<8> index);
}

@cycles(10)
extern bit<32> log(in bit<32> data);
control c() {
  apply {
    @blockAnnotation()
      {
      
    }
  }
}

************************\n******** p4c type checking result: ********\n************************\n
[--Wwarn=missing] warning: Program does not contain a `main' module
