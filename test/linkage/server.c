#include "scalar.h"

unsigned char shared = 64;

static int adjust(int code) {
    return code + 2;
}

int remote(int code) {
    return adjust(code);
}
