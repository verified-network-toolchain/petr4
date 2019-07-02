header MyHeader {
    bit<8> a;
    bit<8> b;
}

MyHeader[5] init() {
    MyHeader[5] tmp;
    return tmp;
}

const MyHeader[5] a = init();
const MyHeader b = a[0];
const MyHeader c = a[1];
const MyHeader d = a[2];
const MyHeader e = a[3];
const MyHeader f = a[4];
const bit<32> g = a.size; //5
const MyHeader h = a.next;

package EmptyPackage();
EmptyPackage() main;
