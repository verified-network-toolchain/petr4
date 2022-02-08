control c() {
    @name("x") bit<32> x;
    @name("hasReturned") bool hasReturned_0;
    @name("a") action a_0(@name("arg") inout bit<32> arg) {
        hasReturned_0 = false;
        arg = 32w1;
        {
            hasReturned_0 = true;
        }
    }
    apply {
        a_0(x);
    }
}

control proto();
package top(proto p);
top(c()) main;

