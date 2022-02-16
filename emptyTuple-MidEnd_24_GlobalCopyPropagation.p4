struct tuple_0 {
}

typedef tuple_0 emptyTuple;
control c(out bool b) {
    @name("c.t") emptyTuple t_0;
    apply {
        {
        }
        b = true;
    }
}

control e(out bool b);
package top(e _e);
top(c()) main;

