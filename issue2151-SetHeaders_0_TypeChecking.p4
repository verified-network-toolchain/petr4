control c() {
    @name("a") action a_0() {
    }
    apply {
        exit;
        a_0();
    }
}

control e();
package top(e e);
top(c()) main;

