/petr4/ci-test/type-checking/testdata/p4_16_samples/methodArgDontcare.p4
\n
extern E<T> {
    E();
    void f(in T arg);
}

control c() {
    E<_>() e;
    apply {
        e.f(0);
    }
}

control proto();
package top(proto p);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("could not solve type equality t1 = t2" (t1 Void) (t2 Integer)
   (unknowns ())
   (env
    ((typ (((E (Extern ((name E)))))))
     (typ_of
      (((e
         ((SpecializedType ((base (Extern ((name E)))) (args (Void))))
          Directionless))
        (E
         ((Constructor
           ((type_params (T)) (wildcard_params ()) (parameters ())
            (return
             (SpecializedType
              ((base (Extern ((name E))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/methodArgDontcare.p4)
                     (line_start 1) (line_end ()) (col_start 9) (col_end 10))
                    T))))))))))
          Directionless)))))
     (const (()))
     (externs
      (((E
         ((type_params (T))
          (methods
           (((name f)
             (typ
              ((type_params ())
               (parameters
                (((annotations ()) (direction In)
                  (typ (TypeName (BareName ((M "") T))))
                  (variable
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/methodArgDontcare.p4)
                     (line_start 3) (line_end ()) (col_start 16)
                     (col_end 19))
                    arg))
                  (opt_value ()))))
               (kind Extern) (return Void)))))))))))
     (renamer ((counter 0) (seen (__wild T main top proto c E)))))))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.infer_type_arguments in file "lib/checker.ml", line 531, characters 4-86
Called from Petr4__Checker.type_function_call in file "lib/checker.ml", line 2336, characters 4-90
Called from Petr4__Checker.type_method_call in file "lib/checker.ml", line 2678, characters 19-80
Called from Petr4__Checker.type_statement in file "lib/checker.ml", line 2649, characters 7-61
Called from Petr4__Checker.type_statements.fold in file "lib/checker.ml", line 2782, characters 26-58
Called from Stdlib__list.fold_left in file "list.ml", line 121, characters 24-34
Called from Petr4__Checker.type_block in file "lib/checker.ml", line 2794, characters 27-73
Called from Petr4__Checker.type_control in file "lib/checker.ml", line 3098, characters 29-61
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
