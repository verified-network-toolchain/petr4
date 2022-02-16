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
    bool hasReturned = false;
    bit<32> retval;
    @name("b1") bool b1_0;
    b1_0 = h2.minSizeInBits == 8w32;
    {
        hasReturned = true;
        retval = h1.isValid + (b1_0 ? 32w117 : 32w162);
    }
    return retval;
}
control c(out bit<32> size) {
    @name("h1") H h1_0;
    @name("h2") H1 h2_0;
    apply {
        h1_0.setInvalid();
        h2_0.setInvalid();
        size = v(h1_0, h2_0);
    }
}

control _c(out bit<32> s);
package top(_c c);
top(c()) main;

