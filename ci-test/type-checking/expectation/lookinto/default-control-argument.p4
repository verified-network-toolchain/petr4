/petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4
\n
struct intrinsic_metadata_t {
   bit<8> f0;
   bit<8> f1;
}

struct empty_t {}

control C<H, M>(
    inout H hdr,
    inout M meta,
    in intrinsic_metadata_t intr_md = {0, 0});

package P<H, M>(C<H, M> c);

struct hdr_t { }
struct meta_t { }

control MyC(inout hdr_t hdr, inout meta_t meta) {
   apply {}
}

P(MyC()) main;

************************\n******** petr4 type checking result: ********\n************************\n
Uncaught exception:
  
  ("could not solve type equality t1 = t2"
   (t1
    (SpecializedType
     ((base
       (TypeName
        (BareName
         ((I
           (filename
            /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
           (line_start 13) (line_end ()) (col_start 16) (col_end 17))
          C))))
      (args
       ((TypeName (BareName ((M "") H0))) (TypeName (BareName ((M "") M1))))))))
   (t2
    (Control
     ((type_params ())
      (parameters
       (((annotations ()) (direction InOut) (typ (Struct ((fields ()))))
         (variable
          ((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
            (line_start 18) (line_end ()) (col_start 24) (col_end 27))
           hdr))
         (opt_value ()))
        ((annotations ()) (direction InOut) (typ (Struct ((fields ()))))
         (variable
          ((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
            (line_start 18) (line_end ()) (col_start 42) (col_end 46))
           meta))
         (opt_value ())))))))
   (unknowns (H0 M1))
   (env
    ((typ
      (((meta_t (Struct ((fields ())))) (hdr_t (Struct ((fields ()))))
        (P
         (Package
          ((type_params (H0 M1)) (wildcard_params ())
           (parameters
            (((annotations ()) (direction Directionless)
              (typ
               (SpecializedType
                ((base
                  (TypeName
                   (BareName
                    ((I
                      (filename
                       /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                      (line_start 13) (line_end ()) (col_start 16)
                      (col_end 17))
                     C))))
                 (args
                  ((TypeName (BareName ((M "") H0)))
                   (TypeName (BareName ((M "") M1))))))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                 (line_start 13) (line_end ()) (col_start 24) (col_end 25))
                c))
              (opt_value ())))))))
        (C
         (Control
          ((type_params (H M))
           (parameters
            (((annotations ()) (direction InOut)
              (typ (TypeName (BareName ((M "") H))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                 (line_start 9) (line_end ()) (col_start 12) (col_end 15))
                hdr))
              (opt_value ()))
             ((annotations ()) (direction InOut)
              (typ (TypeName (BareName ((M "") M))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                 (line_start 10) (line_end ()) (col_start 12) (col_end 16))
                meta))
              (opt_value ()))
             ((annotations ()) (direction In)
              (typ
               (TypeName
                (BareName
                 ((I
                   (filename
                    /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                   (line_start 11) (line_end ()) (col_start 7) (col_end 27))
                  intrinsic_metadata_t))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                 (line_start 11) (line_end ()) (col_start 28) (col_end 35))
                intr_md))
              (opt_value
               (((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                  (line_start 11) (line_end ()) (col_start 38) (col_end 44))
                 (List
                  (values
                   (((I
                      (filename
                       /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                      (line_start 11) (line_end ()) (col_start 39)
                      (col_end 40))
                     (Int
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                        (line_start 11) (line_end ()) (col_start 39)
                        (col_end 40))
                       ((value 0) (width_signed ())))))
                    ((I
                      (filename
                       /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                      (line_start 11) (line_end ()) (col_start 42)
                      (col_end 43))
                     (Int
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                        (line_start 11) (line_end ()) (col_start 42)
                        (col_end 43))
                       ((value 0) (width_signed ())))))))))))))))))
        (empty_t (Struct ((fields ()))))
        (intrinsic_metadata_t
         (Struct
          ((fields
            (((name f0) (typ (Bit ((width 8)))))
             ((name f1) (typ (Bit ((width 8)))))))))))))
     (typ_of
      (((MyC
         ((Constructor
           ((type_params ()) (wildcard_params ()) (parameters ())
            (return
             (Control
              ((type_params ())
               (parameters
                (((annotations ()) (direction InOut)
                  (typ
                   (TypeName
                    (BareName
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                       (line_start 18) (line_end ()) (col_start 18)
                       (col_end 23))
                      hdr_t))))
                  (variable
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                     (line_start 18) (line_end ()) (col_start 24)
                     (col_end 27))
                    hdr))
                  (opt_value ()))
                 ((annotations ()) (direction InOut)
                  (typ
                   (TypeName
                    (BareName
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                       (line_start 18) (line_end ()) (col_start 35)
                       (col_end 41))
                      meta_t))))
                  (variable
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                     (line_start 18) (line_end ()) (col_start 42)
                     (col_end 46))
                    meta))
                  (opt_value ())))))))))
          Directionless))
        (P
         ((Constructor
           ((type_params (H0 M1)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ
                (SpecializedType
                 ((base
                   (TypeName
                    (BareName
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                       (line_start 13) (line_end ()) (col_start 16)
                       (col_end 17))
                      C))))
                  (args
                   ((TypeName (BareName ((M "") H0)))
                    (TypeName (BareName ((M "") M1))))))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                  (line_start 13) (line_end ()) (col_start 24) (col_end 25))
                 c))
               (opt_value ()))))
            (return
             (Package
              ((type_params ()) (wildcard_params ())
               (parameters
                (((annotations ()) (direction Directionless)
                  (typ
                   (SpecializedType
                    ((base
                      (TypeName
                       (BareName
                        ((I
                          (filename
                           /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                          (line_start 13) (line_end ()) (col_start 16)
                          (col_end 17))
                         C))))
                     (args
                      ((TypeName (BareName ((M "") H0)))
                       (TypeName (BareName ((M "") M1))))))))
                  (variable
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/default-control-argument.p4)
                     (line_start 13) (line_end ()) (col_start 24)
                     (col_end 25))
                    c))
                  (opt_value ())))))))))
          Directionless)))))
     (const (())) (externs (()))
     (renamer
      ((counter 2)
       (seen
        (M1 H0 M H main MyC meta_t hdr_t P C empty_t intrinsic_metadata_t)))))))

Raised at Base__Error.raise in file "src/error.ml" (inlined), line 8, characters 14-30
Called from Base__Error.raise_s in file "src/error.ml", line 9, characters 19-40
Called from Petr4__Checker.infer_type_arguments in file "lib/checker.ml", line 531, characters 4-86
Called from Petr4__Checker.type_constructor_invocation in file "lib/checker.ml", line 2546, characters 25-100
Called from Petr4__Checker.type_nameless_instantiation in file "lib/checker.ml", line 2573, characters 32-97
Called from Petr4__Checker.type_instantiation in file "lib/checker.ml", line 2928, characters 23-77
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
