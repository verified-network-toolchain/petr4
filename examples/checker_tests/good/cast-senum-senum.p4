enum bit<8> flag_t {
    ok = 0,
    not_ok = 1
}

enum bit<8> bool_t {
    my_true = 0,
    my_false = 1
}

bool_t f(flag_t x) {
    bool_t ret = (bool_t)x;
    return ret;
}