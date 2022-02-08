struct mystruct1_t {
    bit<16> f1;
}

struct mystruct2_t {
    mystruct1_t s1;
}

struct metadata_t {
    mystruct1_t s1;
    mystruct2_t s2;
}

control ingressImpl(inout metadata_t meta) {
    mystruct1_t helper_0_s1;
    apply {
        {
            {
                helper_0_s1.f1 = 16w2;
            }
        }
        {
            {
                meta.s2.s1.f1 = helper_0_s1.f1;
            }
        }
    }
}

control c(inout metadata_t meta);
package top(c _c);
top(ingressImpl()) main;

