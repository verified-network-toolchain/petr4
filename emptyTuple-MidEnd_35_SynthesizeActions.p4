struct tuple_0 {
}

typedef tuple_0 emptyTuple;
control c(out bool b) {
    @hidden action emptyTuple7() {
        b = true;
    }
    apply {
        emptyTuple7();
    }
}

control e(out bool b);
package top(e _e);
top(c()) main;

