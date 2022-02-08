extern lpf<I> {
    lpf(I instance_count);
    T execute<T>(in T data, in I index);
}

control c() {
    lpf<bit<32>>(32w32) lpf_0;
    apply {
        lpf_0.execute<bit<8>>((bit<8>)0, (bit<32>)0);
    }
}

control e();
package top(e _e);
top(c()) main;

