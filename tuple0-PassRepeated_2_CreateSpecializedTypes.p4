extern void f(in tuple<bit<32>, bool> data);
control proto();
package top(proto _p);
control c() {
    tuple<bit<32>, bool> x = { 32w10, false };
    apply {
        f(x);
        f({ (bit<32>)20, true });
    }
}

top(c()) main;

