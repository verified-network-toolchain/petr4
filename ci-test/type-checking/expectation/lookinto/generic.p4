/petr4/ci-test/type-checking/testdata/p4_16_samples/generic.p4
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

extern Crc16<T> 
{}

extern Checksum16 
{
    void initialize<T>();
}

extern void f<T>(in T dt);

control q<S>(in S dt)
{
    apply {
        f<bit<32>>(32w0);
        f(32w0);
        f<S>(dt);
    }
}

extern X<D>
{
   T f<T>(in D d, in T t);
}

control z<D1, T1>(in X<D1> x, in D1 v, in T1 t)
{
   // x's type is X<D1>
   // x.f's type is T f<T>(D1 d, T t);

    apply {
        T1 r1 = x.f<T1>(v, t);
        T1 r2 = x.f(v, t);
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("Control declarations cannot have type parameters" (name q))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
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
/petr4/ci-test/type-checking/testdata/p4_16_samples/generic.p4(17): [--Wwarn=unused] warning: 'T' is unused
extern Crc16<T>
             ^
[--Wwarn=missing] warning: Program does not contain a `main' module