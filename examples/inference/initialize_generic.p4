#include <core.p4>

T foo<T>(in T x) {
    // This fails because T is parsed as a nonTypeName
    T y = x;
    return y;
}
