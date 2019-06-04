// Generic function declarations and function calls.

header hdr {
    bit<32> a;
    bit<32> b;
    bit<32> c;
}

T fun<T>(in T x){
    return x;
}

// Comment out each line of this function to see each
// the checker reject each ill-typed function call.
void fun_caller(in bool b, in int<32> i, in hdr h,
                out bool br, out int<32> ir, out hdr hr){
    ir = fun<bool>(b);
    hr = fun<int<32>>(i);
    ir = fun<hdr>(i);
}

A lambda<A,B>(in A x, in B y, out B z){
    z = y;
    return x;
}

// Comment out each line of this function to see each
// the checker reject each ill-typed function call.
void lambda_caller(in bool b, in int<32> i, in hdr h,
                   out bool br, out int<32> ir, out hdr hr){
    br = lambda<bool,hdr>(b,i,ir);
    hr = lambda<hdr,bool>(h,b,br);
    ir = lambda<int<32>,hdr>(i,h,hr);
}


A lam<A,B,C>(in A a, in B b, in C c, out C cout){
    cout = c;
    return a;
};


// Comment out each line of this function to see each
// the checker reject each ill-typed function call.
void lam_call(in bool b, in int<32> i, in hdr h,
    out int<32> iout, out bool bout){
    bout = lam<bool,hdr,int<32>>(b,h,i,iout);
    iout = lam<int<32>,hdr,bool>(i,h,b,bout);
}
