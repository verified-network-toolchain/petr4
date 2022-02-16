/petr4/ci-test/type-checking/testdata/p4_16_samples/default-package-argument.p4
\n
 struct intrinsic_metadata_t {
    bit<8> f0;
    bit<8> f1;
 }

 struct empty_t {}

 control nothing(inout empty_t hdr, inout empty_t meta, in intrinsic_metadata_t imeta) {
    apply {}
 }

 control C<H, M>(
     inout H hdr,
     inout M meta,
     in intrinsic_metadata_t intr_md);

 package P<H, M>(C<H, M> c = nothing());

 struct hdr_t { }
 struct meta_t { }

 P<_, _>() main;************************\n******** petr4 type checking result: ********\n************************\n
