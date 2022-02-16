struct H3<T> {
    tuple<T> t;
}

struct S {
    bit<32> b;
}

const H3<S> h4 = (H3<S>){t = { (S){b = 32w0} }};
