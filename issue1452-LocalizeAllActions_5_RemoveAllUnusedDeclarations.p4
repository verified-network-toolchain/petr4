control c() {
    @name("x") bit<32> x_0;
    @name("a") action a(@name("arg") inout bit<32> arg_0) {
        bool hasReturned = false;
        arg_0 = 32w1;
        {
            hasReturned = true;
        }
    }
    apply {
        a(x_0);
    }
}

control proto();
package top(proto p);
top(c()) main;

