extern X {
    X();
    abstract void a(inout bit<32> arg);
}

control c(inout bit<32> y) {
    @name("c.x") X() x_0 = {
        void a(inout bit<32> arg) {
            arg = arg + 32w1;
        }
    };
    @hidden action issue21755l29() {
        x_0.a(y);
    }
    apply {
        issue21755l29();
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(c()) main;

