struct Header<St> {
    St     data;
    bit<1> valid;
}

struct S {
    bit<32> b;
}

struct Header_0 {
    S      data;
    bit<1> valid;
}

struct U {
    Header<S> f;
}

const U u = (U){f = (Header<S>){data = (S){b = 32w10},valid = 1w1}};
struct H2<G> {
    Header<G> g;
    bit<1>    invalid;
}

struct H4<T> {
    T x;
}

const Header<S> h2 = (Header<S>){data = (S){b = 32w0},valid = 1w0};
struct Header_1 {
    bit<16> data;
    bit<1>  valid;
}

const Header<bit<16>> bz = (Header<bit<16>>){data = 16w16,valid = 1w1};
const Header<S> h = (Header<S>){data = (S){b = 32w0},valid = 1w0};
struct H2_0 {
    Header<S> g;
    bit<1>    invalid;
}

const H2<S> h1 = (H2<S>){g = (Header<S>){data = (S){b = 32w0},valid = 1w1},invalid = 1w1};
const H2<S> h3 = (H2<S>){g = (Header<S>){data = (S){b = 32w0},valid = 1w1},invalid = 1w1};
typedef H2<S> R;
struct H3<T> {
    R           r;
    T           s;
    H2<T>       h2;
    H4<H2<T>>   h3;
    tuple<T, T> t;
}

header GH<T> {
    T data;
}

header X {
    bit<32> b;
}

header GH_0 {
    bit<32> data;
}

const GH<bit<32>> g = (GH<bit<32>>){data = 32w0};
header GH_1 {
    S data;
}

const GH<S> g1 = (GH<S>){data = (S){b = 32w0}};
typedef GH<S>[3] Stack;
struct H3_0 {
    R           r;
    S           s;
    H2<S>       h2;
    H4<H2<S>>   h3;
    tuple<S, S> t;
}

const H3<S> h4 = (H3<S>){r = (H2<S>){g = (Header<S>){data = (S){b = 32w10},valid = 1w0},invalid = 1w1},s = (S){b = 32w20},h2 = (H2<S>){g = (Header<S>){data = (S){b = 32w0},valid = 1w1},invalid = 1w1},h3 = (H4<H2<S>>){x = (H2<S>){g = (Header<S>){data = (S){b = 32w0},valid = 1w1},invalid = 1w1}},t = { (S){b = 32w0}, (S){b = 32w1} }};
header_union HU<T> {
    X     xu;
    GH<T> h3u;
}

header_union HU_0 {
    X           xu;
    GH<bit<32>> h3u;
}

control c(out bit<1> x) {
    apply {
        H3<S> h5;
        H4<H2<S>> n;
        GH<S> gh;
        bool b = gh.isValid();
        Stack s;
        s[0] = (GH<S>){data = (S){b = 32w1}};
        b = b && s[0].isValid();
        X xinst = (X){b = 32w2};
        HU<bit<32>> z;
        z.xu = xinst;
        z.h3u = (GH<bit<32>>){data = 32w1};
        x = u.f.valid & h1.g.valid & h.valid & h2.valid & h1.g.valid & h3.g.valid & n.x.g.valid & (bit<1>)b;
    }
}

control ctrl(out bit<1> x);
package top(ctrl _c);
top(c()) main;

