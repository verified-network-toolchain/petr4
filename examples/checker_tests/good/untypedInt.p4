extern void func<T>(in T x);

control proto();
package top(proto _p);

control c() {
    apply {
        func(true);
    }
}