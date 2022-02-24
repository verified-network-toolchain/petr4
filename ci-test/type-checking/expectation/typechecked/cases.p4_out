/petr4/ci-test/type-checking/testdata/p4_16_samples/cases.p4
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

control ctrl() {
    action a() {}
    action b() {}
    action c() {}

    table t {
        actions = { a; b; c; }
        default_action = a;
    }

    apply {
        switch (t.apply().action_run) {
            a:
            b: { return; }
            c:
        }
    }
}************************\n******** petr4 type checking result: ********\n************************\n
control ctrl() {
  action a() { 
  }
  action b() { 
  }
  action c() { 
  }
  table t {
    actions = {
      a;b;c;
    }
    default_action = a;
  }
  apply {
    switch (t.apply().action_run) {
    a:
    b: {
    return;
    }
    c:
    }
  }
}

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/cases.p4(31): [--Wwarn=missing] warning: SwitchCase: fallthrough with no statement
            c:
            ^
[--Wwarn=missing] warning: Program does not contain a `main' module
