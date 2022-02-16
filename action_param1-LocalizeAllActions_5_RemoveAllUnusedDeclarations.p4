control c(inout bit<32> x) {
    @name("a") action a(@name("arg") in bit<32> arg_0) {
        x = arg_0;
    }
    apply {
        a(32w15);
    }
}

control proto(inout bit<32> arg);
package top(proto p);
top(c()) main;

