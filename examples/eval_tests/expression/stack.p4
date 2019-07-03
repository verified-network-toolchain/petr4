header MyHeader {
    bit<8> a;
    bit<8> b;
}

MyHeader[5] init() {
    MyHeader[5] tmp;
    return tmp;
}

MyHeader[5] set_next(in MyHeader[5] a) {
    a.next = {8w42,8w42};
    return a;
}

MyHeader[5] set_third(in MyHeader[5] a) {
    a[3] = {8w42,8w42};
    return a;
}

MyHeader[5] push1(in MyHeader[5] a) {
    a.push_front(1);
    return a;
}

MyHeader[5] pop2(in MyHeader[5] a) {
    a.pop_front(2);
    return a;
}

const MyHeader[5] a = init();
const MyHeader b = a[0];
const MyHeader c = a[1];
const MyHeader d = a[2];
const MyHeader e = a[3];
const MyHeader f = a[4];
const bit<32> g = a.size; //5
const MyHeader h = a.next;
const MyHeader[5] i = set_next(a);
const MyHeader j = i.next;
const MyHeader[5] k = set_third(i);
const MyHeader l = k[3];
const MyHeader[5] m = push1(k);
const MyHeader n = m[0];
const MyHeader o = m[1];
const MyHeader p = m[2];
const MyHeader q = m[3];
const MyHeader r = m[4];
const MyHeader[5] s = pop2(m);
const MyHeader t = s[0];
const MyHeader u = s[1];
const MyHeader v = s[2];
const MyHeader w = s[3];
const MyHeader x = s[4];

package EmptyPackage();
EmptyPackage() main;
