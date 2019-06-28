header H1 {
  bit<8> u;
}

header H2  {
  bit<16> v;
}

header_union Union {
  H1 h1;
  H2 h2;
}

Union f1(in bit<8> x) {
    Union tmp;
    tmp.h1 = {x};
    return tmp;
}

Union f2(in bit<8> x) {
    Union tmp;
    tmp.h2 = {x};
    return tmp;
}

Union set1(in Union x) {
    x.h1.setValid();
    x.h1.u = 8w42;
    return x;
}

Union set2(in Union x) {
    x.h2.setValid();
    x.h1.v = 16w42;
    return x;
}

const Union b = f1(42);
const Union c = f2(42);
const Union d = set1(a);
const Union e = set2(a);

package EmptyPackage();
EmptyPackage() main;
