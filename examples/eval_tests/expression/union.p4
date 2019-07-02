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
    x.h2.v = 16w42;
    return x;
}

Union set3(in Union x) {
    x.h1.setInvalid();
    x.h2.setInvalid();
    return x;
}

const Union a = f1(42);
const Union b = f2(42);
const bit<8> c = a.h1.u; //42
const bool d = a.h1.isValid(); //true
const bool e = a.h2.isValid(); //false
const bit<16> f = b.h2.v; //42
const bool g = b.h1.isValid(); //false
const bool h = b.h2.isValid(); //true
const Union i = set2(a);
const Union j = set1(b);
const bit<8> k = i.h2.v; //42
const bool l = i.h1.isValid(); //false
const bool m = i.h2.isValid(); //true
const bit<16> n = j.h1.u; //42
const bool o = j.h1.isValid(); //true
const bool p = j.h2.isValid(); //false
const Union q = set3(i);
const Union r = set3(j);
const bool s = q.h1.isValid(); //false
const bool t = q.h2.isValid(); //false
const bool u = r.h1.isValid(); //false
const bool v = r.h2.isValid(); //false

package EmptyPackage();
EmptyPackage() main;
