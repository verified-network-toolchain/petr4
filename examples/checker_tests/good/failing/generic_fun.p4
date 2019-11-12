// Generic function declarations and function calls.

header hdr {
    bit<32> a;
    bit<32> b;
    bit<32> c;
}

T fun<T>(in T x){
    return x;
}

void fun_caller(in bool b, in int<32> i, in hdr h,
                out bool br, out int<32> ir, out hdr hr){
    br = fun<bool>(b);
    ir = fun<int<32>>(i);
    hr = fun<hdr>(h);
}

A lambda<A,B>(in A x, in B y, out B z){
    z = y;
    return x;
}

void lambda_caller(in bool b, in int<32> i, in hdr h,
                   out bool br, out int<32> ir, out hdr hr){
    // p4c fails to type check a series of generic
    // function calls with different type arguments
    br = lambda<bool,int<32>>(b,i,ir);
    hr = lambda<hdr,bool>(h,b,br);
    ir = lambda<int<32>,hdr>(i,h,hr);
}


A lam<A,B,C>(in A a, in B b, in C c, out C cout){
    cout = c;
    return a;
};

void lam_call(in bool b, in int<32> i, in hdr h,
    out int<32> iout, out bool bout){
    bout = lam<bool,hdr,int<32>>(b,h,i,iout);
    iout = lam<int<32>,hdr,bool>(i,h,b,bout);
}
