/petr4/ci-test/type-checking/testdata/p4_16_samples/equality.p4
\n
header H {
    bit<32> a;
    varbit<32> b;
}

struct S {
    bit<32> a;
    H h;
}

control c(out bit x) {
    varbit<32> a;
    varbit<32> b;
    H h1;
    H h2;
    S s1;
    S s2;
    H[2] a1;
    H[2] a2;

    apply {
        if (a == b) {
            x = 1;
        } else if (h1 == h2) {
            x = 1;
        } else if (s1 == s2) {
            x = 1;
        } else if (a1 == a2) {
            x = 1;
        } else {
            x = 0;
        }
    }
}

control ctrl(out bit x);
package top(ctrl _c);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
header H {
  bit<32> a;
  varbit <32> b;
}
struct S {
  bit<32> a;
  H h;
}
control c(out bit<1> x) {
  varbit <32> a;
  varbit <32> b;
  H h1;
  H h2;
  S s1;
  S s2;
  H[2] a1;
  H[2] a2;
  apply
    {
    if (a==b) {
      x = 1;
    }
       else
       if (h1==h2) {
         x = 1;
       }
          else if (s1==s2) {
                 x = 1;
          }
             else if (a1==a2) {
                    x = 1;
             }else {
             x = 0;
             }
  }
}
control ctrl (out bit<1> x);
package top (ctrl _c);
top(c()) main;

