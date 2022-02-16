typedef bit<9> Narrow_t;
typedef Narrow_t Narrow;
typedef bit<32> Wide_t;
typedef Wide_t Wide;
control c(out bool b) {
    @hidden action newtype1l12() {
        b = false;
    }
    apply {
        newtype1l12();
    }
}

control ctrl(out bool b);
package top(ctrl _c);
top(c()) main;

