header header_h {
    bit<8> field;
}

struct struct_t {
    header_h hdr;
}

control ctrl(inout struct_t input, out bit<8> out1, out header_h out2) {
    @name("tmp0") bit<8> tmp0;
    @name("tmp1") bit<8> tmp1;
    @name("tmp2") header_h tmp2;
    @name("tmp3") header_h tmp3;
    @name("act") action act_0() {
        tmp0 = input.hdr.field;
        input.hdr.setValid();
        tmp1 = tmp0;
        tmp2 = input.hdr;
        input.hdr.setInvalid();
        tmp3 = tmp2;
    }
    apply {
        tmp2.setInvalid();
        tmp3.setInvalid();
        act_0();
        out1 = tmp1;
        out2 = tmp3;
    }
}

control MyControl<S, H>(inout S i, out bit<8> o1, out H o2);
package MyPackage<S, H>(MyControl<S, H> c);
MyPackage<struct_t, header_h>(ctrl()) main;

