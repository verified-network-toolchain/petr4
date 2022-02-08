extern ext<H> {
    ext(H v);
    void method<T>(H h, T t);
}

control c() {
    ext<bit<16>>(16w0) x;
    apply {
        x.method(16w0, 8w0);
    }
}

