header H {
    bit<32> isValid;
}

type bit<32> T;
enum bit<16> E {
    z = 16w0
}

header H1 {
    bit<16> f;
    bit<8>  minSizeInBytes;
    bit<8>  minSizeInBits;
    T       f1;
    E       e;
}

struct Flags {
    bit<1> f0;
    bit<1> f1;
    bit<6> pad;
}

header Nested {
    Flags      flags;
    bit<32>    b;
    varbit<32> v;
}

struct S {
    H  h1;
    H1 h2;
}

header Empty {
}

bit<32> v(in H h1, in H1 h2) {
    @name("hasReturned") bool hasReturned_0 = false;
    @name("retval") bit<32> retval_0;
    @name("b1") bool b1;
    b1 = h2.minSizeInBits == 8w32;
    {
        hasReturned_0 = true;
        retval_0 = h1.isValid + (b1 ? 32w117 : 32w162);
    }
    return retval_0;
}
control c(out bit<32> size) {
    @name("h1") H h1_1;
    @name("h2") H1 h2_1;
    apply {
        h1_1.setInvalid();
        h2_1.setInvalid();
        size = v(h1_1, h2_1);
    }
}

control _c(out bit<32> s);
package top(_c c);
top(c()) main;

