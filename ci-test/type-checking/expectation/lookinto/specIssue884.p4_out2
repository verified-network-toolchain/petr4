/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4
\n
enum HashAlgorithm_t {
    IDENTITY,
    RANDOM,
    CRC8,
    CRC16,
    CRC32,
    CRC64
}

extern CRCPolynomial<T> {
    CRCPolynomial(T coeff);
}

extern LCGMatrix<W, H> {
    LCGMatrix(W width, H height, string contents);
}

extern Hash<W> {
    Hash(HashAlgorithm_t   algo);
    Hash(CRCPolynomial<_>  poly);
    Hash(LCGMatrix<_,_>    matrix);
    Hash(string            formula);

    W get<D>(in D data);
}

control IngressT<H, M>(inout H hdr, inout M meta);
package Switch<H,M>(IngressT<H,M> ingress);

struct headers_t {};
struct meta_t    {};

control Ingress(inout headers_t hdr, inout meta_t meta)
{
    Hash<bit<32>>(algo=HashAlgorithm_t.CRC32)       hash1;
    Hash<bit<32>>(poly=CRCPolynomial(coeff=16w0x107))  hash2;
    LCGMatrix(8w4, 10w7,
        "1000100
         0100011
         0010110
         0001001") hamming;
    Hash<bit<32>>(matrix=hamming) hash3;
    Hash<bit<32>>(formula="magic_formula()") hash4;

    apply {
    }
}

Switch(Ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4:38:9: warning: missing terminating " character
   38 |         "1000100
      |         ^
/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4:41:17: warning: missing terminating " character
   41 |          0001001") hamming;
      |                 ^
Uncaught exception:
  
  ("could not solve type equality t1 = t2"
   (t1
    (SpecializedType
     ((base
       (TypeName
        (BareName
         ((I
           (filename
            /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
           (line_start 20) (line_end ()) (col_start 9) (col_end 22))
          CRCPolynomial))))
      (args
       ((TypeName
         (BareName
          ((I
            (filename
             /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
            (line_start 20) (line_end ()) (col_start 23) (col_end 24))
           __wild))))))))
   (t2
    (SpecializedType
     ((base (Extern ((name CRCPolynomial)))) (args ((Bit ((width 16))))))))
   (unknowns ())
   (env
    ((typ
      (((W0 (Bit ((width 32)))) (meta_t (Struct ((fields ()))))
        (headers_t (Struct ((fields ()))))
        (Switch
         (Package
          ((type_params (H2 M3)) (wildcard_params ())
           (parameters
            (((annotations ()) (direction Directionless)
              (typ
               (SpecializedType
                ((base
                  (TypeName
                   (BareName
                    ((I
                      (filename
                       /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                      (line_start 28) (line_end ()) (col_start 20)
                      (col_end 28))
                     IngressT))))
                 (args
                  ((TypeName (BareName ((M "") H2)))
                   (TypeName (BareName ((M "") M3))))))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                 (line_start 28) (line_end ()) (col_start 34) (col_end 41))
                ingress))
              (opt_value ())))))))
        (IngressT
         (Control
          ((type_params (H1 M))
           (parameters
            (((annotations ()) (direction InOut)
              (typ (TypeName (BareName ((M "") H1))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                 (line_start 27) (line_end ()) (col_start 31) (col_end 34))
                hdr))
              (opt_value ()))
             ((annotations ()) (direction InOut)
              (typ (TypeName (BareName ((M "") M))))
              (variable
               ((I
                 (filename
                  /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                 (line_start 27) (line_end ()) (col_start 44) (col_end 48))
                meta))
              (opt_value ())))))))
        (Hash (Extern ((name Hash)))) (LCGMatrix (Extern ((name LCGMatrix))))
        (CRCPolynomial (Extern ((name CRCPolynomial))))
        (HashAlgorithm_t
         (Enum
          ((name HashAlgorithm_t) (typ ())
           (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))))))
     (typ_of
      (((hash1
         ((SpecializedType
           ((base (Extern ((name Hash)))) (args ((Bit ((width 32)))))))
          Directionless))
        (meta
         ((TypeName
           (BareName
            ((I
              (filename
               /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
              (line_start 33) (line_end ()) (col_start 43) (col_end 49))
             meta_t)))
          InOut))
        (hdr
         ((TypeName
           (BareName
            ((I
              (filename
               /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
              (line_start 33) (line_end ()) (col_start 22) (col_end 31))
             headers_t)))
          InOut))
        (Switch
         ((Constructor
           ((type_params (H2 M3)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ
                (SpecializedType
                 ((base
                   (TypeName
                    (BareName
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                       (line_start 28) (line_end ()) (col_start 20)
                       (col_end 28))
                      IngressT))))
                  (args
                   ((TypeName (BareName ((M "") H2)))
                    (TypeName (BareName ((M "") M3))))))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 28) (line_end ()) (col_start 34) (col_end 41))
                 ingress))
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
                           /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                          (line_start 28) (line_end ()) (col_start 20)
                          (col_end 28))
                         IngressT))))
                     (args
                      ((TypeName (BareName ((M "") H2)))
                       (TypeName (BareName ((M "") M3))))))))
                  (variable
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 28) (line_end ()) (col_start 34)
                     (col_end 41))
                    ingress))
                  (opt_value ())))))))))
          Directionless))
        (Hash
         ((Constructor
           ((type_params (W0)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ
                (TypeName
                 (BareName
                  ((I
                    (filename
                     /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                    (line_start 19) (line_end ()) (col_start 9) (col_end 24))
                   HashAlgorithm_t))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 19) (line_end ()) (col_start 25) (col_end 29))
                 algo))
               (opt_value ()))))
            (return
             (SpecializedType
              ((base (Extern ((name Hash))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 18) (line_end ()) (col_start 12)
                     (col_end 13))
                    W0))))))))))
          Directionless))
        (Hash
         ((Constructor
           ((type_params (W0)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ
                (SpecializedType
                 ((base
                   (TypeName
                    (BareName
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                       (line_start 20) (line_end ()) (col_start 9)
                       (col_end 22))
                      CRCPolynomial))))
                  (args
                   ((TypeName
                     (BareName
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                        (line_start 20) (line_end ()) (col_start 23)
                        (col_end 24))
                       __wild))))))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 20) (line_end ()) (col_start 26) (col_end 30))
                 poly))
               (opt_value ()))))
            (return
             (SpecializedType
              ((base (Extern ((name Hash))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 18) (line_end ()) (col_start 12)
                     (col_end 13))
                    W0))))))))))
          Directionless))
        (Hash
         ((Constructor
           ((type_params (W0)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ
                (SpecializedType
                 ((base
                   (TypeName
                    (BareName
                     ((I
                       (filename
                        /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                       (line_start 21) (line_end ()) (col_start 9)
                       (col_end 18))
                      LCGMatrix))))
                  (args
                   ((TypeName
                     (BareName
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                        (line_start 21) (line_end ()) (col_start 19)
                        (col_end 20))
                       __wild4)))
                    (TypeName
                     (BareName
                      ((I
                        (filename
                         /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                        (line_start 21) (line_end ()) (col_start 21)
                        (col_end 22))
                       __wild5))))))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 21) (line_end ()) (col_start 24) (col_end 30))
                 matrix))
               (opt_value ()))))
            (return
             (SpecializedType
              ((base (Extern ((name Hash))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 18) (line_end ()) (col_start 12)
                     (col_end 13))
                    W0))))))))))
          Directionless))
        (Hash
         ((Constructor
           ((type_params (W0)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless) (typ String)
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 22) (line_end ()) (col_start 16) (col_end 23))
                 formula))
               (opt_value ()))))
            (return
             (SpecializedType
              ((base (Extern ((name Hash))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 18) (line_end ()) (col_start 12)
                     (col_end 13))
                    W0))))))))))
          Directionless))
        (LCGMatrix
         ((Constructor
           ((type_params (W H)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ (TypeName (BareName ((M "") W))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 15) (line_end ()) (col_start 16) (col_end 21))
                 width))
               (opt_value ()))
              ((annotations ()) (direction Directionless)
               (typ (TypeName (BareName ((M "") H))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 15) (line_end ()) (col_start 25) (col_end 31))
                 height))
               (opt_value ()))
              ((annotations ()) (direction Directionless) (typ String)
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 15) (line_end ()) (col_start 40) (col_end 48))
                 contents))
               (opt_value ()))))
            (return
             (SpecializedType
              ((base (Extern ((name LCGMatrix))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 14) (line_end ()) (col_start 17)
                     (col_end 18))
                    W)))
                 (TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 14) (line_end ()) (col_start 20)
                     (col_end 21))
                    H))))))))))
          Directionless))
        (CRCPolynomial
         ((Constructor
           ((type_params (T)) (wildcard_params ())
            (parameters
             (((annotations ()) (direction Directionless)
               (typ (TypeName (BareName ((M "") T))))
               (variable
                ((I
                  (filename
                   /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                  (line_start 11) (line_end ()) (col_start 20) (col_end 25))
                 coeff))
               (opt_value ()))))
            (return
             (SpecializedType
              ((base (Extern ((name CRCPolynomial))))
               (args
                ((TypeName
                  (BareName
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 10) (line_end ()) (col_start 21)
                     (col_end 22))
                    T))))))))))
          Directionless))
        (HashAlgorithm_t.CRC64
         ((Enum
           ((name HashAlgorithm_t) (typ ())
            (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))
          Directionless))
        (HashAlgorithm_t.CRC32
         ((Enum
           ((name HashAlgorithm_t) (typ ())
            (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))
          Directionless))
        (HashAlgorithm_t.CRC16
         ((Enum
           ((name HashAlgorithm_t) (typ ())
            (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))
          Directionless))
        (HashAlgorithm_t.CRC8
         ((Enum
           ((name HashAlgorithm_t) (typ ())
            (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))
          Directionless))
        (HashAlgorithm_t.RANDOM
         ((Enum
           ((name HashAlgorithm_t) (typ ())
            (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))
          Directionless))
        (HashAlgorithm_t.IDENTITY
         ((Enum
           ((name HashAlgorithm_t) (typ ())
            (members (IDENTITY RANDOM CRC8 CRC16 CRC32 CRC64))))
          Directionless)))))
     (const
      (((HashAlgorithm_t.CRC64
         (VEnumField (typ_name HashAlgorithm_t) (enum_name CRC64)))
        (HashAlgorithm_t.CRC32
         (VEnumField (typ_name HashAlgorithm_t) (enum_name CRC32)))
        (HashAlgorithm_t.CRC16
         (VEnumField (typ_name HashAlgorithm_t) (enum_name CRC16)))
        (HashAlgorithm_t.CRC8
         (VEnumField (typ_name HashAlgorithm_t) (enum_name CRC8)))
        (HashAlgorithm_t.RANDOM
         (VEnumField (typ_name HashAlgorithm_t) (enum_name RANDOM)))
        (HashAlgorithm_t.IDENTITY
         (VEnumField (typ_name HashAlgorithm_t) (enum_name IDENTITY))))))
     (externs
      (((Hash
         ((type_params (W0))
          (methods
           (((name get)
             (typ
              ((type_params (D))
               (parameters
                (((annotations ()) (direction In)
                  (typ (TypeName (BareName ((M "") D))))
                  (variable
                   ((I
                     (filename
                      /petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4)
                     (line_start 24) (line_end ()) (col_start 18)
                     (col_end 22))
                    data))
                  (opt_value ()))))
               (kind Extern) (return (TypeName (BareName ((M "") W0)))))))))))
        (LCGMatrix ((type_params (W H)) (methods ())))
        (CRCPolynomial ((type_params (T)) (methods ()))))))
     (renamer
      ((counter 6)
       (seen
        (__wild5 __wild4 __wild M3 H2 M H1 D W0 H W T main Ingress meta_t
         headers_t Switch IngressT Hash LCGMatrix CRCPolynomial
         HashAlgorithm_t)))))))

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
Called from Petr4__Checker.open_control_scope in file "lib/checker.ml", line 3087, characters 26-73
Called from Petr4__Checker.type_control in file "lib/checker.ml", line 3096, characters 6-69
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
/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4(35): [--Wwarn=unused] warning: hash1: unused instance
    Hash<bit<32>>(algo=HashAlgorithm_t.CRC32) hash1;
                                              ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4(36): [--Wwarn=unused] warning: hash2: unused instance
    Hash<bit<32>>(poly=CRCPolynomial(coeff=16w0x107)) hash2;
                                                      ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4(42): [--Wwarn=unused] warning: hash3: unused instance
    Hash<bit<32>>(matrix=hamming) hash3;
                                  ^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/specIssue884.p4(43): [--Wwarn=unused] warning: hash4: unused instance
    Hash<bit<32>>(formula="magic_formula()") hash4;
                                             ^^^^^
