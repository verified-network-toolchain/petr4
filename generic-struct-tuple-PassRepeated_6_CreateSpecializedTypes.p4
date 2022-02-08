struct S<T> {
    tuple<T, T> t;
}

struct S_0 {
    tuple<bit<32>, bit<32>> t;
}

const S<bit<32>> x = (S<bit<32>>){t = { 32w0, 32w0 }};
