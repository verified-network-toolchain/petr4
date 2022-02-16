control c() {
    @name("a") action a() {
    }
    apply {
        exit;
        a();
    }
}

control e();
package top(e e);
top(c()) main;

