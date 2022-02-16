struct S<T> {
    tuple<T, T> t;
}

const S<bit<32>> x = (S<bit<32>>){t = { 32w0, 32w0 }};
