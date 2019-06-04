header my_header {
    bit    g1;
    bit<2> g2;
    bit<3> g3;
}

header hdr {
    bit<32> a;
    bit<32> b;
    bit<32> c;
}

enum Choice {
    First,
    Second
}

header_union my_union
{
    my_header h1;
    my_header h2;
    hdr       h3;
}

struct str
{
     my_header hdr;
     my_union  unn;
     bit<32>     dt;
     Choice  choice;
}

// typedef tuple<bit<32>, bool> pair;
// struct S {
//     bit<32> f;
//     bool    s;
// }
