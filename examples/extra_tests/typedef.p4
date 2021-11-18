typedef bit<8> action_list_t;
control c(inout action_list_t p) {
    apply {
        p = p + 1;
    }
}

control d() {
    table t {
        key = {}
        actions = {}
    }

    apply{
        c() ci;
        bit<8> x = 4;
        ci.apply(x);
    }
}
