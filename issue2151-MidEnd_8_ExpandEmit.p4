control c() {
    bool hasExited;
    @name("c.a") action a() {
    }
    apply {
        hasExited = false;
        hasExited = true;
    }
}

control e();
package top(e e);
top(c()) main;

