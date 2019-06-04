void foo<T>(in T x) {}

void bar() {
    foo(true);
}

void main() {
    foo("string");
}
